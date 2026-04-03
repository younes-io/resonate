use rusqlite::{params, Connection};
use std::sync::{Arc, Mutex};

use super::{
    Db, OutgoingExecute, OutgoingUnblock, PromiseCreateParams, PromiseSettleParams,
    PromiseSettleResult, RegisterCallbackResult, ScheduleCreateParams, StorageResult,
    TaskAcquireParams, TaskAcquireResult, TaskContinueResult, TaskCreateParams, TaskCreateResult,
    TaskFenceCreateParams, TaskFenceResult, TaskFenceSettleParams, TaskFulfillParams,
    TaskFulfillResult, TaskHaltResult, TaskSuspendResult,
};
use crate::types::{
    PromiseRecord, PromiseState, PromiseValue, ScheduleRecord, Snapshot, SnapshotCallback,
    SnapshotListener, SnapshotMessage, SnapshotPromiseTimeout, SnapshotTaskTimeout, TaskRecord,
    TaskState,
};

fn parse_promise_state(s: &str) -> PromiseState {
    s.parse()
        .unwrap_or_else(|e| panic!("corrupt promise state in DB: {}", e))
}

fn parse_task_state(s: &str) -> TaskState {
    s.parse()
        .unwrap_or_else(|e| panic!("corrupt task state in DB: {}", e))
}

/// Initialize database: set pragmas and create schema
pub fn init_db(conn: &Connection) -> rusqlite::Result<()> {
    conn.execute_batch(
        "
        PRAGMA journal_mode = WAL;
        PRAGMA busy_timeout = 5000;
        PRAGMA foreign_keys = ON;
        PRAGMA synchronous = NORMAL;
        ",
    )?;
    create_schema(conn)?;
    Ok(())
}

fn create_schema(conn: &Connection) -> rusqlite::Result<()> {
    conn.execute_batch(
        "
        CREATE TABLE IF NOT EXISTS promises (
          id TEXT PRIMARY KEY,
          state TEXT NOT NULL DEFAULT 'pending'
            CHECK (state IN ('pending', 'resolved', 'rejected', 'rejected_canceled', 'rejected_timedout')),
          param_headers TEXT,
          param_data TEXT,
          value_headers TEXT,
          value_data TEXT,
          tags TEXT NOT NULL DEFAULT '{}',
          target TEXT GENERATED ALWAYS AS (json_extract(tags, '$.resonate:target')) STORED,
          origin TEXT GENERATED ALWAYS AS (json_extract(tags, '$.resonate:origin')) STORED,
          branch TEXT GENERATED ALWAYS AS (json_extract(tags, '$.resonate:branch')) STORED,
          timer BOOLEAN NOT NULL GENERATED ALWAYS AS (COALESCE(json_extract(tags, '$.resonate:timer'), '') = 'true') STORED,
          timeout_at BIGINT NOT NULL,
          created_at BIGINT NOT NULL,
          settled_at BIGINT
        );
        CREATE INDEX IF NOT EXISTS idx_promises_timeout_at ON promises (timeout_at) WHERE state = 'pending';
        CREATE INDEX IF NOT EXISTS idx_promises_target ON promises (target) WHERE target IS NOT NULL;

        CREATE TABLE IF NOT EXISTS promise_timeouts (
          timeout_at BIGINT NOT NULL,
          id TEXT PRIMARY KEY REFERENCES promises(id) ON DELETE CASCADE
        );
        CREATE INDEX IF NOT EXISTS idx_promise_timeouts_timeout_at_id ON promise_timeouts (timeout_at ASC, id ASC);

        CREATE TABLE IF NOT EXISTS callbacks (
          awaited_id TEXT NOT NULL REFERENCES promises(id) ON DELETE CASCADE,
          awaiter_id TEXT NOT NULL REFERENCES promises(id) ON DELETE CASCADE,
          ready BOOLEAN NOT NULL DEFAULT false,
          PRIMARY KEY (awaited_id, awaiter_id)
        );
        CREATE INDEX IF NOT EXISTS idx_callbacks_awaiter_id ON callbacks (awaiter_id);
        CREATE INDEX IF NOT EXISTS idx_callbacks_ready ON callbacks (awaiter_id) WHERE ready = true;

        CREATE TABLE IF NOT EXISTS listeners (
          promise_id TEXT NOT NULL REFERENCES promises(id) ON DELETE CASCADE,
          address TEXT NOT NULL,
          PRIMARY KEY (promise_id, address)
        );

        CREATE TABLE IF NOT EXISTS tasks (
          id TEXT PRIMARY KEY REFERENCES promises(id) ON DELETE CASCADE,
          state TEXT NOT NULL DEFAULT 'pending'
            CHECK (state IN ('pending', 'acquired', 'suspended', 'halted', 'fulfilled')),
          version INT NOT NULL DEFAULT 0
        );

        CREATE TABLE IF NOT EXISTS task_timeouts (
          timeout_at BIGINT NOT NULL,
          id TEXT PRIMARY KEY REFERENCES tasks(id) ON DELETE CASCADE,
          timeout_type SMALLINT NOT NULL DEFAULT 0,
          process_id TEXT,
          ttl BIGINT NOT NULL DEFAULT 30000
        );
        CREATE INDEX IF NOT EXISTS idx_task_timeouts_timeout_at_id ON task_timeouts (timeout_at ASC, id ASC);
        CREATE INDEX IF NOT EXISTS idx_task_timeouts_process_id ON task_timeouts (process_id) WHERE process_id IS NOT NULL;
        CREATE INDEX IF NOT EXISTS idx_task_timeouts_timeout_type ON task_timeouts (timeout_type, timeout_at ASC);

        CREATE TABLE IF NOT EXISTS outgoing_execute (
          id TEXT PRIMARY KEY REFERENCES tasks(id) ON DELETE CASCADE,
          version INT NOT NULL,
          address TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS outgoing_unblock (
          promise_id TEXT NOT NULL REFERENCES promises(id) ON DELETE CASCADE,
          address TEXT NOT NULL,
          PRIMARY KEY (promise_id, address)
        );

        CREATE TABLE IF NOT EXISTS schedules (
          id TEXT PRIMARY KEY,
          cron TEXT NOT NULL,
          promise_id TEXT NOT NULL,
          promise_timeout BIGINT NOT NULL,
          promise_param_headers TEXT,
          promise_param_data TEXT,
          promise_tags TEXT NOT NULL DEFAULT '{}',
          created_at BIGINT NOT NULL,
          next_run_at BIGINT NOT NULL,
          last_run_at BIGINT
        );
        ",
    )?;
    Ok(())
}

pub struct SqliteStorage {
    conn: Arc<Mutex<Connection>>,
    task_retry_timeout: i64,
}

impl SqliteStorage {
    pub fn open(path: &str, task_retry_timeout: i64) -> rusqlite::Result<Self> {
        let conn = Connection::open(path)?;
        init_db(&conn)?;
        Ok(Self {
            conn: Arc::new(Mutex::new(conn)),
            task_retry_timeout,
        })
    }

    pub async fn transact<F, T>(&self, f: F) -> StorageResult<T>
    where
        F: FnMut(&dyn Db) -> StorageResult<T> + Send + 'static,
        T: Send + 'static,
    {
        #[cfg(feature = "concurrency-stress")]
        tokio::task::yield_now().await;

        let mut f = f;
        let conn = Arc::clone(&self.conn);
        let task_retry_timeout = self.task_retry_timeout;
        tokio::task::block_in_place(|| {
            // Use unwrap_or_else to recover from poisoned mutex (a prior panic
            // while holding the lock). The connection itself is still valid.
            let conn = conn.lock().unwrap_or_else(|e| e.into_inner());
            let tx = conn.unchecked_transaction()?;
            let db = SqliteDb {
                conn: &tx,
                task_retry_timeout,
            };
            let result = f(&db)?;
            tx.commit()?;
            Ok(result)
        })
    }

    pub async fn query<F, T>(&self, f: F) -> StorageResult<T>
    where
        F: FnMut(&dyn Db) -> StorageResult<T> + Send + 'static,
        T: Send + 'static,
    {
        #[cfg(feature = "concurrency-stress")]
        tokio::task::yield_now().await;

        let mut f = f;
        let conn = Arc::clone(&self.conn);
        let task_retry_timeout = self.task_retry_timeout;
        tokio::task::block_in_place(|| {
            let conn = conn.lock().unwrap_or_else(|e| e.into_inner());
            let db = SqliteDb {
                conn: &conn,
                task_retry_timeout,
            };
            f(&db)
        })
    }
}

struct SqliteDb<'a> {
    conn: &'a rusqlite::Connection,
    task_retry_timeout: i64,
}

// === Settlement chain helpers (multi-statement within the transaction) ===

/// SettlementEnqueued: fulfill task, delete task timeout, delete callbacks by awaiter
fn settlement_enqueued(tx: &rusqlite::Connection, promise_id: &str) -> rusqlite::Result<bool> {
    let fulfilled = tx.execute(
        "UPDATE tasks SET state = 'fulfilled' WHERE id = ?1 AND state != 'fulfilled'",
        params![promise_id],
    )? > 0;
    if fulfilled {
        tx.execute(
            "DELETE FROM task_timeouts WHERE id = ?1",
            params![promise_id],
        )?;
        tx.execute(
            "DELETE FROM callbacks WHERE awaiter_id = ?1",
            params![promise_id],
        )?;
    }
    Ok(fulfilled)
}

/// ResumptionEnqueued: mark callbacks ready, resume suspended tasks, insert outgoing
fn resumption_enqueued(
    tx: &rusqlite::Connection,
    awaited_id: &str,
    time: i64,
    task_retry_timeout: i64,
    exclude_fulfilled: Option<&[String]>,
) -> rusqlite::Result<()> {
    // Mark callbacks ready
    tx.execute(
        "UPDATE callbacks SET ready = true WHERE awaited_id = ?1",
        params![awaited_id],
    )?;

    // Find awaiter IDs that need resuming (suspended tasks whose callbacks just became ready)
    let mut stmt = tx.prepare(
        "SELECT DISTINCT c.awaiter_id FROM callbacks c
         JOIN tasks t ON t.id = c.awaiter_id
         WHERE c.awaited_id = ?1 AND c.ready = true AND t.state = 'suspended'",
    )?;
    let awaiter_ids: Vec<String> = {
        let mut rows = stmt.query(params![awaited_id])?;
        let mut ids = Vec::new();
        while let Some(row) = rows.next()? {
            let id: String = row.get(0)?;
            if let Some(excluded) = exclude_fulfilled {
                if excluded.contains(&id) {
                    continue;
                }
            }
            ids.push(id);
        }
        ids
    };

    for awaiter_id in &awaiter_ids {
        // Resume: set to pending, increment version
        let updated = tx.execute(
            "UPDATE tasks SET state = 'pending', version = version + 1 WHERE id = ?1 AND state = 'suspended'",
            params![awaiter_id],
        )?;
        if updated > 0 {
            // Get new version
            let version: i64 = tx.query_row(
                "SELECT version FROM tasks WHERE id = ?1",
                params![awaiter_id],
                |r| r.get(0),
            )?;
            // Insert/update task timeout (retry type 0)
            tx.execute(
                "INSERT INTO task_timeouts (timeout_at, id, timeout_type, ttl) VALUES (?1, ?2, 0, ?3)
                 ON CONFLICT (id) DO UPDATE SET timeout_at = ?1, timeout_type = 0, process_id = NULL, ttl = ?3",
                params![time + task_retry_timeout, awaiter_id, task_retry_timeout],
            )?;
            // Insert/update outgoing execute
            let target: Option<String> = tx
                .query_row(
                    "SELECT target FROM promises WHERE id = ?1",
                    params![awaiter_id],
                    |r| r.get(0),
                )
                .ok()
                .flatten();
            if let Some(target) = target {
                tx.execute(
                    "INSERT INTO outgoing_execute (id, version, address) VALUES (?1, ?2, ?3)
                     ON CONFLICT (id) DO UPDATE SET version = EXCLUDED.version, address = EXCLUDED.address",
                    params![awaiter_id, version, target],
                )?;
            }
        }
    }
    Ok(())
}

/// ListenerUnblocked: insert outgoing unblock messages, delete listeners
fn listener_unblocked(tx: &rusqlite::Connection, promise_id: &str) -> rusqlite::Result<()> {
    tx.execute(
        "INSERT INTO outgoing_unblock (promise_id, address)
         SELECT l.promise_id, l.address FROM listeners l WHERE l.promise_id = ?1
         ON CONFLICT DO NOTHING",
        params![promise_id],
    )?;
    tx.execute(
        "DELETE FROM listeners WHERE promise_id = ?1",
        params![promise_id],
    )?;
    Ok(())
}

/// Full settlement chain: settle promise + SettlementEnqueued + ResumptionEnqueued + ListenerUnblocked
#[allow(clippy::too_many_arguments)]
fn settle_promise(
    tx: &rusqlite::Connection,
    id: &str,
    state: &str,
    value_headers: Option<&str>,
    value_data: Option<&str>,
    settled_at: i64,
    time: i64,
    task_retry_timeout: i64,
) -> rusqlite::Result<bool> {
    let updated = tx.execute(
        "UPDATE promises SET state = ?2, value_headers = ?3, value_data = ?4, settled_at = ?5 WHERE id = ?1 AND state = 'pending'",
        params![id, state, value_headers, value_data, settled_at],
    )?;
    if updated == 0 {
        return Ok(false);
    }

    tx.execute("DELETE FROM promise_timeouts WHERE id = ?1", params![id])?;
    settlement_enqueued(tx, id)?;
    resumption_enqueued(tx, id, time, task_retry_timeout, None)?;
    listener_unblocked(tx, id)?;
    Ok(true)
}

impl<'a> Db for SqliteDb<'a> {
    fn task_retry_timeout(&self) -> i64 {
        self.task_retry_timeout
    }

    fn try_timeout(&self, ids: &[&str], time: i64) -> StorageResult<()> {
        if ids.is_empty() {
            return Ok(());
        }
        let ids_json = serde_json::to_string(ids).unwrap();
        // Find expired promises from the ID set
        let mut stmt = self.conn.prepare(
            "SELECT id, timer, timeout_at FROM promises
             WHERE id IN (SELECT value FROM json_each(?1))
               AND state = 'pending' AND timeout_at <= ?2",
        )?;
        let expired: Vec<(String, bool, i64)> = {
            let mut rows = stmt.query(params![ids_json, time])?;
            let mut results = Vec::new();
            while let Some(row) = rows.next()? {
                results.push((row.get(0)?, row.get(1)?, row.get(2)?));
            }
            results
        };

        if expired.is_empty() {
            return Ok(());
        }

        // Settle each expired promise
        let mut fulfilled_ids = Vec::new();
        for (id, timer, timeout_at) in &expired {
            let new_state = if *timer {
                "resolved"
            } else {
                "rejected_timedout"
            };
            self.conn.execute(
                "UPDATE promises SET state = ?2, settled_at = ?3 WHERE id = ?1 AND state = 'pending'",
                params![id, new_state, timeout_at],
            )?;
            self.conn
                .execute("DELETE FROM promise_timeouts WHERE id = ?1", params![id])?;

            // SettlementEnqueued
            if settlement_enqueued(self.conn, id)? {
                fulfilled_ids.push(id.clone());
            }
        }

        // ResumptionEnqueued for each expired
        for (id, _, _) in &expired {
            resumption_enqueued(
                self.conn,
                id,
                time,
                self.task_retry_timeout,
                Some(&fulfilled_ids),
            )?;
        }

        // ListenerUnblocked for each expired
        for (id, _, _) in &expired {
            listener_unblocked(self.conn, id)?;
        }

        Ok(())
    }

    fn promise_get(&self, id: &str) -> StorageResult<Option<PromiseRecord>> {
        let mut stmt = self.conn.prepare(
            "SELECT id, state, param_headers, param_data, value_headers, value_data, tags, timeout_at, created_at, settled_at FROM promises WHERE id = ?1",
        )?;
        let mut rows = stmt.query(params![id])?;
        match rows.next()? {
            Some(row) => Ok(Some(row_to_promise(row)?)),
            None => Ok(None),
        }
    }

    fn promise_create(&self, params: &PromiseCreateParams) -> StorageResult<PromiseRecord> {
        let PromiseCreateParams {
            id,
            state,
            param_headers,
            param_data,
            tags,
            timeout_at,
            created_at,
            settled_at,
            already_timedout,
            address,
        } = *params;
        // Idempotent insert
        let inserted = self.conn.execute(
            "INSERT OR IGNORE INTO promises (id, state, param_headers, param_data, tags, timeout_at, created_at, settled_at)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8)",
            params![id, state, param_headers, param_data, tags, timeout_at, created_at, settled_at],
        )?;

        if inserted > 0 {
            if already_timedout {
                // Already timed out — create fulfilled task if resonate:target
                if address.is_some() {
                    self.conn.execute(
                        "INSERT OR IGNORE INTO tasks (id, state) VALUES (?1, 'fulfilled')",
                        params![id],
                    )?;
                }
            } else {
                // Promise timeout
                self.conn.execute(
                    "INSERT OR IGNORE INTO promise_timeouts (timeout_at, id) VALUES (?1, ?2)",
                    params![timeout_at, id],
                )?;
                // TaskInfraCreated
                if let Some(addr) = address {
                    self.conn.execute(
                        "INSERT OR IGNORE INTO tasks (id, state) VALUES (?1, 'pending')",
                        params![id],
                    )?;
                    if self.conn.changes() > 0 {
                        self.conn.execute(
                            "INSERT OR IGNORE INTO task_timeouts (timeout_at, id, timeout_type, ttl) VALUES (?1, ?2, 0, ?3)",
                            params![created_at + self.task_retry_timeout, id, self.task_retry_timeout],
                        )?;
                        self.conn.execute(
                            "INSERT INTO outgoing_execute (id, version, address) VALUES (?1, 0, ?2)
                             ON CONFLICT (id) DO UPDATE SET version = EXCLUDED.version, address = EXCLUDED.address",
                            params![id, addr],
                        )?;
                    }
                }
            }
        }

        Ok(self.promise_get(id)?.unwrap())
    }

    fn promise_settle(&self, params: &PromiseSettleParams) -> StorageResult<PromiseSettleResult> {
        let PromiseSettleParams {
            id,
            state,
            value_headers,
            value_data,
            settled_at,
        } = *params;
        let was_settled = settle_promise(
            self.conn,
            id,
            state,
            value_headers,
            value_data,
            settled_at,
            settled_at,
            self.task_retry_timeout,
        )?;

        Ok(PromiseSettleResult {
            was_settled,
            promise: self.promise_get(id)?,
        })
    }

    fn promise_register_callback(
        &self,
        awaited_id: &str,
        awaiter_id: &str,
        time: i64,
    ) -> StorageResult<RegisterCallbackResult> {
        let awaited = self.promise_get(awaited_id)?;
        let awaiter = self.promise_get(awaiter_id)?;

        // Insert callback only if both pending and awaiter has target
        if let (Some(ref pa), Some(ref pw)) = (&awaited, &awaiter) {
            if pa.state == PromiseState::Pending
                && pw.state == PromiseState::Pending
                && pw.tags.contains_key("resonate:target")
            {
                self.conn.execute(
                    "INSERT OR IGNORE INTO callbacks (awaited_id, awaiter_id) VALUES (?1, ?2)",
                    params![awaited_id, awaiter_id],
                )?;
            }
        }

        // Direct resume if awaited is already settled
        if let Some(ref pa) = awaited {
            if pa.state != PromiseState::Pending {
                // Resume awaiter if suspended
                let updated = self.conn.execute(
                    "UPDATE tasks SET state = 'pending', version = version + 1 WHERE id = ?1 AND state = 'suspended'",
                    params![awaiter_id],
                )?;
                if updated > 0 {
                    let version: i64 = self.conn.query_row(
                        "SELECT version FROM tasks WHERE id = ?1",
                        params![awaiter_id],
                        |r| r.get(0),
                    )?;
                    self.conn.execute(
                        "INSERT INTO task_timeouts (timeout_at, id, timeout_type, ttl) VALUES (?1, ?2, 0, ?3)
                         ON CONFLICT (id) DO UPDATE SET timeout_at = ?1, timeout_type = 0, process_id = NULL, ttl = ?3",
                        params![time + self.task_retry_timeout, awaiter_id, self.task_retry_timeout],
                    )?;
                    let target: Option<String> = self
                        .conn
                        .query_row(
                            "SELECT target FROM promises WHERE id = ?1",
                            params![awaiter_id],
                            |r| r.get(0),
                        )
                        .ok()
                        .flatten();
                    if let Some(target) = target {
                        self.conn.execute(
                            "INSERT INTO outgoing_execute (id, version, address) VALUES (?1, ?2, ?3)
                             ON CONFLICT (id) DO UPDATE SET version = EXCLUDED.version, address = EXCLUDED.address",
                            params![awaiter_id, version, target],
                        )?;
                    }
                }
            }
        }

        Ok(RegisterCallbackResult { awaited, awaiter })
    }

    fn promise_register_listener(
        &self,
        awaited_id: &str,
        address: &str,
    ) -> StorageResult<Option<PromiseRecord>> {
        let promise = self.promise_get(awaited_id)?;
        if let Some(ref p) = promise {
            if p.state == PromiseState::Pending {
                self.conn.execute(
                    "INSERT OR IGNORE INTO listeners (promise_id, address) VALUES (?1, ?2)",
                    params![awaited_id, address],
                )?;
            }
        }
        Ok(promise)
    }

    fn promise_search(
        &self,
        state: Option<&str>,
        tags: Option<&str>,
        cursor: Option<&str>,
        limit: i64,
    ) -> StorageResult<Vec<PromiseRecord>> {
        let mut stmt = self.conn.prepare(
            "SELECT id, state, param_headers, param_data, value_headers, value_data, tags, timeout_at, created_at, settled_at
             FROM promises
             WHERE (?1 IS NULL OR state = ?1)
               AND (?2 IS NULL OR NOT EXISTS (
                 SELECT key, value FROM json_each(?2) EXCEPT SELECT key, value FROM json_each(tags)
               ))
               AND (?3 IS NULL OR id > ?3)
             ORDER BY id ASC LIMIT ?4",
        )?;
        let mut rows = stmt.query(params![state, tags, cursor, limit])?;
        let mut results = Vec::new();
        while let Some(row) = rows.next()? {
            results.push(row_to_promise(row)?);
        }
        Ok(results)
    }

    fn task_get(&self, id: &str) -> StorageResult<Option<TaskRecord>> {
        let mut stmt = self.conn.prepare(
            "SELECT t.id, t.state, t.version,
                    CASE WHEN tt.timeout_type = 1 THEN tt.ttl ELSE NULL END,
                    CASE WHEN tt.timeout_type = 1 THEN tt.process_id ELSE NULL END
             FROM tasks t LEFT JOIN task_timeouts tt ON tt.id = t.id
             WHERE t.id = ?1",
        )?;
        let mut rows = stmt.query(params![id])?;
        match rows.next()? {
            Some(row) => {
                let task_id: String = row.get(0)?;
                let resumes = get_resumes(self.conn, &task_id)?;
                let state_str: String = row.get(1)?;
                Ok(Some(TaskRecord {
                    id: task_id,
                    state: parse_task_state(&state_str),
                    version: row.get(2)?,
                    resumes,
                    ttl: row.get(3)?,
                    pid: row.get(4)?,
                }))
            }
            None => Ok(None),
        }
    }

    fn task_create(&self, params: &TaskCreateParams) -> StorageResult<Option<TaskCreateResult>> {
        let TaskCreateParams {
            promise_id,
            state,
            param_headers,
            param_data,
            tags,
            timeout_at,
            created_at,
            settled_at,
            already_timedout,
            ttl,
            pid,
        } = *params;

        let promise_inserted = self.conn.execute(
            "INSERT OR IGNORE INTO promises (id, state, param_headers, param_data, tags, timeout_at, created_at, settled_at)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8)",
            params![promise_id, state, param_headers, param_data, tags, timeout_at, created_at, settled_at],
        )? > 0;

        let promise = match self.promise_get(promise_id)? {
            Some(p) => p,
            None => return Ok(None),
        };

        let mut task_created = false;
        let mut task_acquired = false;

        if promise_inserted {
            if !already_timedout {
                self.conn.execute(
                    "INSERT OR IGNORE INTO promise_timeouts (timeout_at, id) VALUES (?1, ?2)",
                    params![timeout_at, promise_id],
                )?;
            }
            let task_state = if already_timedout {
                "fulfilled"
            } else {
                "acquired"
            };
            let inserted = self.conn.execute(
                "INSERT OR IGNORE INTO tasks (id, state) VALUES (?1, ?2)",
                params![promise_id, task_state],
            )? > 0;
            if inserted {
                task_created = true;
                if !already_timedout {
                    self.conn.execute(
                        "INSERT OR REPLACE INTO task_timeouts (timeout_at, id, timeout_type, process_id, ttl) VALUES (?1, ?2, 1, ?3, ?4)",
                        params![created_at + ttl, promise_id, pid, ttl],
                    )?;
                }
            }
        } else {
            // Promise already existed — try to acquire pending task
            let acquired = self.conn.execute(
                "UPDATE tasks SET state = 'acquired' WHERE id = ?1 AND state = 'pending'",
                params![promise_id],
            )? > 0;
            if acquired {
                task_acquired = true;
                self.conn.execute(
                    "INSERT OR REPLACE INTO task_timeouts (timeout_at, id, timeout_type, process_id, ttl) VALUES (?1, ?2, 1, ?3, ?4)",
                    params![created_at + ttl, promise_id, pid, ttl],
                )?;
                self.conn.execute(
                    "DELETE FROM callbacks WHERE awaiter_id = ?1 AND ready = 1",
                    params![promise_id],
                )?;
            }
        }

        Ok(Some(TaskCreateResult {
            promise,
            task_created,
            task_acquired,
        }))
    }

    fn task_acquire(&self, params: &TaskAcquireParams) -> StorageResult<TaskAcquireResult> {
        let TaskAcquireParams {
            task_id,
            version,
            time,
            ttl,
            pid,
        } = *params;
        let updated = self.conn.execute(
            "UPDATE tasks SET state = 'acquired' WHERE id = ?1 AND version = ?2 AND state = 'pending'",
            params![task_id, version],
        )?;

        let promise = self.promise_get(task_id)?;
        if promise.is_none() || self.task_get(task_id)?.is_none() {
            return Ok(TaskAcquireResult {
                promise: None,
                was_acquired: false,
            });
        }

        if updated > 0 {
            // Insert/update lease timeout
            self.conn.execute(
                "INSERT INTO task_timeouts (timeout_at, id, timeout_type, process_id, ttl) VALUES (?1, ?2, 1, ?3, ?4)
                 ON CONFLICT (id) DO UPDATE SET timeout_at = ?1, timeout_type = 1, process_id = ?3, ttl = ?4",
                params![time + ttl, task_id, pid, ttl],
            )?;
            // Clean up ready callbacks from previous suspension
            self.conn.execute(
                "DELETE FROM callbacks WHERE awaiter_id = ?1 AND ready = true",
                params![task_id],
            )?;
        }

        Ok(TaskAcquireResult {
            promise,
            was_acquired: updated > 0,
        })
    }

    fn task_fence_create(&self, params: &TaskFenceCreateParams) -> StorageResult<TaskFenceResult> {
        let TaskFenceCreateParams {
            task_id,
            version,
            promise_id,
            state,
            param_headers,
            param_data,
            tags,
            timeout_at,
            created_at,
            settled_at,
            already_timedout,
            address,
        } = *params;
        // Fence check
        let task = self.task_get(task_id)?;
        let task_exists = task.is_some();
        let fence_ok = task.is_some_and(|t| t.state == TaskState::Acquired && t.version == version);

        if !fence_ok {
            return Ok(TaskFenceResult {
                task_exists,
                fence_ok,
                promise: None,
            });
        }

        // Execute inner promise.create
        let promise = self.promise_create(&PromiseCreateParams {
            id: promise_id,
            state,
            param_headers,
            param_data,
            tags,
            timeout_at,
            created_at,
            settled_at,
            already_timedout,
            address,
        })?;

        Ok(TaskFenceResult {
            task_exists,
            fence_ok,
            promise: Some(promise),
        })
    }

    fn task_fence_settle(&self, params: &TaskFenceSettleParams) -> StorageResult<TaskFenceResult> {
        let TaskFenceSettleParams {
            task_id,
            version,
            promise_id,
            state,
            value_headers,
            value_data,
            settled_at,
        } = *params;
        let task = self.task_get(task_id)?;
        let task_exists = task.is_some();
        let fence_ok = task.is_some_and(|t| t.state == TaskState::Acquired && t.version == version);

        if !fence_ok {
            return Ok(TaskFenceResult {
                task_exists,
                fence_ok,
                promise: None,
            });
        }

        // Execute settlement
        settle_promise(
            self.conn,
            promise_id,
            state,
            value_headers,
            value_data,
            settled_at,
            settled_at,
            self.task_retry_timeout,
        )?;

        let promise = self.promise_get(promise_id)?;
        Ok(TaskFenceResult {
            task_exists,
            fence_ok,
            promise,
        })
    }

    fn task_heartbeat(&self, pid: &str, tasks: &[(&str, i64)], time: i64) -> StorageResult<()> {
        for &(task_id, version) in tasks {
            if task_id.is_empty() {
                continue;
            }

            // Update timeout only if task is acquired at right version by right pid
            self.conn.execute(
                "UPDATE task_timeouts SET timeout_at = ?1 + ttl
                 WHERE id = ?2 AND process_id = ?3
                   AND EXISTS (SELECT 1 FROM tasks t WHERE t.id = ?2 AND t.version = ?4 AND t.state = 'acquired')",
                params![time, task_id, pid, version],
            )?;
        }
        Ok(())
    }

    fn task_suspend(
        &self,
        task_id: &str,
        version: i64,
        awaited_ids: &[&str],
    ) -> StorageResult<TaskSuspendResult> {
        // Check task state
        let task = self.task_get(task_id)?;
        let task_matched = task
            .as_ref()
            .is_some_and(|t| t.state == TaskState::Acquired && t.version == version);
        if !task_matched {
            return Ok(TaskSuspendResult {
                task_matched: false,
                was_suspended: false,
                missing_count: 0,
            });
        }

        // Check each awaited promise — count missing and settled
        let mut found_count = 0;
        let mut has_settled = false;
        for aid in awaited_ids {
            if let Some(p) = self.promise_get(aid)? {
                found_count += 1;
                if p.state != PromiseState::Pending {
                    has_settled = true;
                }
            }
        }

        let missing_count = awaited_ids.len() as i32 - found_count;

        // Can only suspend if: task matched, no missing, all pending
        let can_suspend = missing_count == 0 && !has_settled;

        if can_suspend {
            // Register callbacks for all awaited
            for aid in awaited_ids {
                self.conn.execute(
                    "INSERT OR IGNORE INTO callbacks (awaited_id, awaiter_id) VALUES (?1, ?2)",
                    params![aid, task_id],
                )?;
            }

            // Suspend the task
            self.conn.execute(
                "UPDATE tasks SET state = 'suspended' WHERE id = ?1 AND version = ?2 AND state = 'acquired'",
                params![task_id, version],
            )?;
            self.conn
                .execute("DELETE FROM task_timeouts WHERE id = ?1", params![task_id])?;

            Ok(TaskSuspendResult {
                task_matched: true,
                was_suspended: true,
                missing_count: 0,
            })
        } else if missing_count == 0 {
            // Immediate resume — has_settled is true, delete ready callbacks
            self.conn.execute(
                "DELETE FROM callbacks WHERE awaiter_id = ?1 AND ready = true",
                params![task_id],
            )?;
            Ok(TaskSuspendResult {
                task_matched: true,
                was_suspended: false,
                missing_count: 0,
            })
        } else {
            Ok(TaskSuspendResult {
                task_matched: true,
                was_suspended: false,
                missing_count,
            })
        }
    }

    fn task_fulfill(&self, params: &TaskFulfillParams) -> StorageResult<TaskFulfillResult> {
        let TaskFulfillParams {
            task_id,
            version,
            promise_id,
            state,
            value_headers,
            value_data,
            settled_at,
        } = *params;
        // Fulfill the task
        let task_fulfilled = self.conn.execute(
            "UPDATE tasks SET state = 'fulfilled' WHERE id = ?1 AND version = ?2 AND state = 'acquired'",
            params![task_id, version],
        )? > 0;

        if task_fulfilled {
            self.conn
                .execute("DELETE FROM task_timeouts WHERE id = ?1", params![task_id])?;

            // Settle the promise
            settle_promise(
                self.conn,
                promise_id,
                state,
                value_headers,
                value_data,
                settled_at,
                settled_at,
                self.task_retry_timeout,
            )?;

            // Delete callbacks where this task is the awaiter
            self.conn.execute(
                "DELETE FROM callbacks WHERE awaiter_id = ?1",
                params![task_id],
            )?;
        }

        Ok(TaskFulfillResult {
            task_fulfilled,
            promise: self.promise_get(promise_id)?,
        })
    }

    fn task_release(
        &self,
        task_id: &str,
        version: i64,
        time: i64,
        ttl: i64,
    ) -> StorageResult<bool> {
        let released = self.conn.execute(
            "UPDATE tasks SET state = 'pending', version = version + 1 WHERE id = ?1 AND version = ?2 AND state = 'acquired'",
            params![task_id, version],
        )? > 0;

        if released {
            self.conn.execute(
                "UPDATE task_timeouts SET timeout_type = 0, timeout_at = ?1, process_id = NULL WHERE id = ?2",
                params![time + ttl, task_id],
            )?;
            // Insert outgoing execute
            let new_version: i64 = self.conn.query_row(
                "SELECT version FROM tasks WHERE id = ?1",
                params![task_id],
                |r| r.get(0),
            )?;
            let target: Option<String> = self
                .conn
                .query_row(
                    "SELECT target FROM promises WHERE id = ?1",
                    params![task_id],
                    |r| r.get(0),
                )
                .ok()
                .flatten();
            if let Some(target) = target {
                self.conn.execute(
                    "INSERT INTO outgoing_execute (id, version, address) VALUES (?1, ?2, ?3)
                     ON CONFLICT (id) DO UPDATE SET version = EXCLUDED.version, address = EXCLUDED.address",
                    params![task_id, new_version, target],
                )?;
            }
        }
        Ok(released)
    }

    fn task_halt(&self, task_id: &str) -> StorageResult<TaskHaltResult> {
        self.conn.execute(
            "UPDATE tasks SET state = 'halted' WHERE id = ?1 AND state NOT IN ('fulfilled', 'halted')",
            params![task_id],
        )?;
        self.conn.execute(
            "DELETE FROM task_timeouts WHERE id = ?1 AND EXISTS (SELECT 1 FROM tasks WHERE id = ?1 AND state = 'halted')",
            params![task_id],
        )?;
        let row = self.conn.query_row(
            "SELECT
               EXISTS (SELECT 1 FROM tasks WHERE id = ?1) AS task_exists,
               EXISTS (SELECT 1 FROM tasks WHERE id = ?1 AND state = 'fulfilled') AS task_fulfilled",
            params![task_id],
            |r| Ok(TaskHaltResult {
                task_exists: r.get(0)?,
                task_fulfilled: r.get(1)?,
            }),
        )?;
        Ok(row)
    }

    fn task_continue(&self, task_id: &str, time: i64) -> StorageResult<TaskContinueResult> {
        let continued = self.conn.execute(
            "UPDATE tasks SET state = 'pending', version = version + 1 WHERE id = ?1 AND state = 'halted'",
            params![task_id],
        )? > 0;

        if continued {
            self.conn.execute(
                "INSERT INTO task_timeouts (timeout_at, id, timeout_type, ttl) VALUES (?1, ?2, 0, ?3) ON CONFLICT (id) DO NOTHING",
                params![time + self.task_retry_timeout, task_id, self.task_retry_timeout],
            )?;
            let version: i64 = self.conn.query_row(
                "SELECT version FROM tasks WHERE id = ?1",
                params![task_id],
                |r| r.get(0),
            )?;
            let target: Option<String> = self
                .conn
                .query_row(
                    "SELECT target FROM promises WHERE id = ?1",
                    params![task_id],
                    |r| r.get(0),
                )
                .ok()
                .flatten();
            if let Some(target) = target {
                self.conn.execute(
                    "INSERT INTO outgoing_execute (id, version, address) VALUES (?1, ?2, ?3)
                     ON CONFLICT (id) DO UPDATE SET version = EXCLUDED.version, address = EXCLUDED.address",
                    params![task_id, version, target],
                )?;
            }
        }

        match self.task_get(task_id)? {
            Some(t) => Ok(TaskContinueResult {
                state: Some(t.state),
                continued,
            }),
            None => Ok(TaskContinueResult {
                state: None,
                continued: false,
            }),
        }
    }

    fn task_search(
        &self,
        state: Option<&str>,
        cursor: Option<&str>,
        limit: i64,
    ) -> StorageResult<Vec<TaskRecord>> {
        let mut stmt = self.conn.prepare(
            "SELECT t.id, t.state, t.version,
                    CASE WHEN tt.timeout_type = 1 THEN tt.ttl ELSE NULL END,
                    CASE WHEN tt.timeout_type = 1 THEN tt.process_id ELSE NULL END
             FROM tasks t LEFT JOIN task_timeouts tt ON tt.id = t.id
             WHERE (?1 IS NULL OR t.state = ?1) AND (?2 IS NULL OR t.id > ?2)
             ORDER BY t.id ASC LIMIT ?3",
        )?;
        let mut rows = stmt.query(params![state, cursor, limit])?;
        let mut results = Vec::new();
        while let Some(row) = rows.next()? {
            let state_str: String = row.get(1)?;
            results.push(TaskRecord {
                id: row.get(0)?,
                state: parse_task_state(&state_str),
                version: row.get(2)?,
                resumes: 0,
                ttl: row.get::<_, Option<i64>>(3).ok().flatten(),
                pid: row.get::<_, Option<String>>(4).ok().flatten(),
            });
        }
        Ok(results)
    }

    fn compute_preload(&self, promise_id: &str) -> StorageResult<Vec<PromiseRecord>> {
        let branch: Option<String> = self
            .conn
            .query_row(
                "SELECT branch FROM promises WHERE id = ?1",
                params![promise_id],
                |r| r.get(0),
            )
            .ok()
            .flatten();
        let branch = match branch {
            Some(b) => b,
            None => return Ok(Vec::new()),
        };
        let mut stmt = self.conn.prepare(
            "SELECT id, state, param_headers, param_data, value_headers, value_data, tags, timeout_at, created_at, settled_at
             FROM promises WHERE branch = ?1 AND id != ?2 ORDER BY id ASC",
        )?;
        let mut rows = stmt.query(params![branch, promise_id])?;
        let mut results = Vec::new();
        while let Some(row) = rows.next()? {
            results.push(row_to_promise(row)?);
        }
        Ok(results)
    }

    fn schedule_get(&self, id: &str) -> StorageResult<Option<ScheduleRecord>> {
        let mut stmt = self.conn.prepare(
            "SELECT id, cron, promise_id, promise_timeout, promise_param_headers, promise_param_data, promise_tags, created_at, next_run_at, last_run_at FROM schedules WHERE id = ?1",
        )?;
        let mut rows = stmt.query(params![id])?;
        match rows.next()? {
            Some(row) => Ok(Some(row_to_schedule(row)?)),
            None => Ok(None),
        }
    }

    fn schedule_create(&self, params: &ScheduleCreateParams) -> StorageResult<ScheduleRecord> {
        let ScheduleCreateParams {
            id,
            cron,
            promise_id,
            promise_timeout,
            promise_param_headers,
            promise_param_data,
            promise_tags,
            created_at,
            next_run_at,
        } = *params;
        self.conn.execute(
            "INSERT OR IGNORE INTO schedules (id, cron, promise_id, promise_timeout, promise_param_headers, promise_param_data, promise_tags, created_at, next_run_at)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9)",
            params![id, cron, promise_id, promise_timeout, promise_param_headers, promise_param_data, promise_tags, created_at, next_run_at],
        )?;
        Ok(self.schedule_get(id)?.unwrap())
    }

    fn schedule_delete(&self, id: &str) -> StorageResult<bool> {
        Ok(self
            .conn
            .execute("DELETE FROM schedules WHERE id = ?1", params![id])?
            > 0)
    }

    fn schedule_search(
        &self,
        tags: Option<&str>,
        cursor: Option<&str>,
        limit: i64,
    ) -> StorageResult<Vec<ScheduleRecord>> {
        let mut stmt = self.conn.prepare(
            "SELECT id, cron, promise_id, promise_timeout, promise_param_headers, promise_param_data, promise_tags, created_at, next_run_at, last_run_at
             FROM schedules WHERE (?1 IS NULL OR NOT EXISTS (
               SELECT key, value FROM json_each(?1) EXCEPT SELECT key, value FROM json_each(promise_tags)
             )) AND (?2 IS NULL OR id > ?2) ORDER BY id ASC LIMIT ?3",
        )?;
        let mut rows = stmt.query(params![tags, cursor, limit])?;
        let mut results = Vec::new();
        while let Some(row) = rows.next()? {
            results.push(row_to_schedule(row)?);
        }
        Ok(results)
    }

    fn schedule_run(
        &self,
        schedule_id: &str,
        last_run_at: i64,
        next_run_at: i64,
        runs: &[super::ScheduleRun],
    ) -> StorageResult<Option<ScheduleRecord>> {
        let schedule = match self.schedule_get(schedule_id)? {
            Some(s) => s,
            None => return Ok(None),
        };

        for run in runs {
            let id = run.id.as_str();
            let timeout_at = run.timeout_at;
            let created_at = run.created_at;

            let ph = schedule
                .promise_param
                .headers
                .as_ref()
                .map(|h| serde_json::to_string(h).unwrap());
            let tags_json = serde_json::to_string(&schedule.promise_tags).unwrap();

            self.conn.execute(
                "INSERT OR IGNORE INTO promises (id, state, param_headers, param_data, tags, timeout_at, created_at)
                 VALUES (?1, 'pending', ?2, ?3, ?4, ?5, ?6)",
                params![id, ph, schedule.promise_param.data, tags_json, timeout_at, created_at],
            )?;
            if self.conn.changes() > 0 {
                self.conn.execute(
                    "INSERT OR IGNORE INTO promise_timeouts (timeout_at, id) VALUES (?1, ?2)",
                    params![timeout_at, id],
                )?;
            }
        }

        self.conn.execute(
            "UPDATE schedules SET last_run_at = ?2, next_run_at = ?3 WHERE id = ?1",
            params![schedule_id, last_run_at, next_run_at],
        )?;

        self.schedule_get(schedule_id)
    }

    fn get_expired_schedules(&self, time: i64) -> StorageResult<Vec<ScheduleRecord>> {
        let mut stmt = self.conn.prepare(
            "SELECT id, cron, promise_id, promise_timeout, promise_param_headers, promise_param_data, promise_tags, created_at, next_run_at, last_run_at FROM schedules WHERE next_run_at <= ?1",
        )?;
        let mut rows = stmt.query(params![time])?;
        let mut results = Vec::new();
        while let Some(row) = rows.next()? {
            results.push(row_to_schedule(row)?);
        }
        Ok(results)
    }

    fn ping(&self) -> StorageResult<()> {
        self.conn.execute_batch("SELECT 1")?;
        Ok(())
    }

    fn debug_reset(&self) -> StorageResult<()> {
        self.conn.execute_batch(
            "DELETE FROM outgoing_unblock; DELETE FROM outgoing_execute;
             DELETE FROM task_timeouts; DELETE FROM listeners; DELETE FROM callbacks;
             DELETE FROM promise_timeouts; DELETE FROM tasks; DELETE FROM promises;
             DELETE FROM schedules;",
        )?;
        Ok(())
    }

    fn process_timeouts(&self, time: i64) -> StorageResult<()> {
        // Refinement note:
        //   CoordinationModel.ProcessTimeoutBatch models this routine as:
        //   1) ApplyPromiseTimeouts
        //   2) ResumeReadyAwaiters
        //   3) ApplyRetryTimeouts
        //   4) ApplyLeaseTimeouts
        //
        // See proofs/dafny/proofs/CoordinationProofs.dfy:
        //   ProcessTimeoutBatchEqualsSqliteTimeoutStatements
        //
        // The Dafny boundary is semantic rather than line-by-line SQL equivalence,
        // and it does not cover listener-address authorization or callback registration.
        // Statement 1: Process expired promise timeouts
        let mut stmt = self.conn.prepare(
            "SELECT id, timer, timeout_at FROM promises WHERE state = 'pending' AND timeout_at <= ?1"
        )?;
        let expired: Vec<(String, bool, i64)> = {
            let mut rows = stmt.query(params![time])?;
            let mut r = Vec::new();
            while let Some(row) = rows.next()? {
                r.push((row.get(0)?, row.get(1)?, row.get(2)?));
            }
            r
        };

        // Phase 1: Settle all expired promises
        let mut fulfilled_ids = Vec::new();
        for (id, timer, timeout_at) in &expired {
            let new_state = if *timer {
                "resolved"
            } else {
                "rejected_timedout"
            };
            self.conn.execute(
                "UPDATE promises SET state = ?2, settled_at = ?3 WHERE id = ?1 AND state = 'pending'",
                params![id, new_state, timeout_at],
            )?;
            self.conn
                .execute("DELETE FROM promise_timeouts WHERE id = ?1", params![id])?;
        }

        // Phase 2: SettlementEnqueued for all
        for (id, _, _) in &expired {
            if settlement_enqueued(self.conn, id)? {
                fulfilled_ids.push(id.clone());
            }
        }

        // Phase 3: ResumptionEnqueued + ListenerUnblocked
        for (id, _, _) in &expired {
            resumption_enqueued(
                self.conn,
                id,
                time,
                self.task_retry_timeout,
                Some(&fulfilled_ids),
            )?;
            listener_unblocked(self.conn, id)?;
        }

        // Statement 2: Process expired task retry timeouts (type 0)
        let mut stmt = self.conn.prepare(
            "SELECT tt.id FROM task_timeouts tt JOIN tasks t ON t.id = tt.id
             WHERE tt.timeout_type = 0 AND tt.timeout_at <= ?1 AND t.state = 'pending'",
        )?;
        let retry_ids: Vec<String> = {
            let mut rows = stmt.query(params![time])?;
            let mut r = Vec::new();
            while let Some(row) = rows.next()? {
                r.push(row.get(0)?);
            }
            r
        };

        for id in &retry_ids {
            self.conn.execute(
                "UPDATE task_timeouts SET timeout_at = ?1 + ?3, process_id = NULL WHERE id = ?2",
                params![time, id, self.task_retry_timeout],
            )?;
            let version: i64 = self
                .conn
                .query_row(
                    "SELECT version FROM tasks WHERE id = ?1",
                    params![id],
                    |r| r.get(0),
                )
                .unwrap_or(0);
            let target: Option<String> = self
                .conn
                .query_row(
                    "SELECT target FROM promises WHERE id = ?1",
                    params![id],
                    |r| r.get(0),
                )
                .ok()
                .flatten();
            if let Some(target) = target {
                self.conn.execute(
                    "INSERT INTO outgoing_execute (id, version, address) VALUES (?1, ?2, ?3)
                     ON CONFLICT (id) DO UPDATE SET version = EXCLUDED.version, address = EXCLUDED.address",
                    params![id, version, target],
                )?;
            }
        }

        // Statement 3: Process expired task lease timeouts (type 1)
        let mut stmt = self.conn.prepare(
            "SELECT tt.id FROM task_timeouts tt JOIN tasks t ON t.id = tt.id
             WHERE tt.timeout_type = 1 AND tt.timeout_at <= ?1 AND t.state = 'acquired'",
        )?;
        let lease_ids: Vec<String> = {
            let mut rows = stmt.query(params![time])?;
            let mut r = Vec::new();
            while let Some(row) = rows.next()? {
                r.push(row.get(0)?);
            }
            r
        };

        for id in &lease_ids {
            self.conn.execute(
                "UPDATE tasks SET state = 'pending', version = version + 1 WHERE id = ?1",
                params![id],
            )?;
            let version: i64 = self
                .conn
                .query_row(
                    "SELECT version FROM tasks WHERE id = ?1",
                    params![id],
                    |r| r.get(0),
                )
                .unwrap_or(0);
            self.conn.execute(
                "UPDATE task_timeouts SET timeout_at = ?1 + ?3, timeout_type = 0, process_id = NULL, ttl = ?3 WHERE id = ?2",
                params![time, id, self.task_retry_timeout],
            )?;
            let target: Option<String> = self
                .conn
                .query_row(
                    "SELECT target FROM promises WHERE id = ?1",
                    params![id],
                    |r| r.get(0),
                )
                .ok()
                .flatten();
            if let Some(target) = target {
                self.conn.execute(
                    "INSERT INTO outgoing_execute (id, version, address) VALUES (?1, ?2, ?3)
                     ON CONFLICT (id) DO UPDATE SET version = EXCLUDED.version, address = EXCLUDED.address",
                    params![id, version, target],
                )?;
            }
        }

        Ok(())
    }

    fn snap(&self) -> StorageResult<Snapshot> {
        let conn = self.conn;

        let mut stmt = conn.prepare("SELECT id, state, param_headers, param_data, value_headers, value_data, tags, timeout_at, created_at, settled_at FROM promises ORDER BY id")?;
        let promises: Vec<PromiseRecord> = {
            let mut rows = stmt.query([])?;
            let mut r = Vec::new();
            while let Some(row) = rows.next()? {
                r.push(row_to_promise(row)?);
            }
            r
        };

        let mut stmt = conn.prepare("SELECT id, timeout_at FROM promise_timeouts ORDER BY id")?;
        let promise_timeouts: Vec<SnapshotPromiseTimeout> = {
            let mut rows = stmt.query([])?;
            let mut r = Vec::new();
            while let Some(row) = rows.next()? {
                r.push(SnapshotPromiseTimeout {
                    id: row.get(0)?,
                    timeout: row.get(1)?,
                });
            }
            r
        };

        let mut stmt = conn.prepare(
            "SELECT awaiter_id, awaited_id, ready FROM callbacks ORDER BY awaiter_id, awaited_id",
        )?;
        let callbacks: Vec<SnapshotCallback> = {
            let mut rows = stmt.query([])?;
            let mut r = Vec::new();
            while let Some(row) = rows.next()? {
                r.push(SnapshotCallback {
                    awaiter: row.get(0)?,
                    awaited: row.get(1)?,
                    ready: row.get(2)?,
                });
            }
            r
        };

        let mut stmt =
            conn.prepare("SELECT promise_id, address FROM listeners ORDER BY promise_id, address")?;
        let listeners: Vec<SnapshotListener> = {
            let mut rows = stmt.query([])?;
            let mut r = Vec::new();
            while let Some(row) = rows.next()? {
                r.push(SnapshotListener {
                    promise_id: row.get(0)?,
                    address: row.get(1)?,
                });
            }
            r
        };

        let mut stmt = conn.prepare(
            "SELECT t.id, t.state, t.version,
                    CASE WHEN tt.timeout_type = 1 THEN tt.ttl ELSE NULL END,
                    CASE WHEN tt.timeout_type = 1 THEN tt.process_id ELSE NULL END
             FROM tasks t LEFT JOIN task_timeouts tt ON tt.id = t.id ORDER BY t.id",
        )?;
        let tasks: Vec<TaskRecord> = {
            let mut rows = stmt.query([])?;
            let mut r = Vec::new();
            while let Some(row) = rows.next()? {
                let task_id: String = row.get(0)?;
                let resumes = get_resumes(conn, &task_id)?;
                let state_str: String = row.get(1)?;
                r.push(TaskRecord {
                    id: task_id,
                    state: parse_task_state(&state_str),
                    version: row.get(2)?,
                    resumes,
                    ttl: row.get(3)?,
                    pid: row.get(4)?,
                });
            }
            r
        };

        let mut stmt =
            conn.prepare("SELECT id, timeout_type, timeout_at FROM task_timeouts ORDER BY id")?;
        let task_timeouts: Vec<SnapshotTaskTimeout> = {
            let mut rows = stmt.query([])?;
            let mut r = Vec::new();
            while let Some(row) = rows.next()? {
                r.push(SnapshotTaskTimeout {
                    id: row.get(0)?,
                    timeout_type: row.get(1)?,
                    timeout: row.get(2)?,
                });
            }
            r
        };

        let mut messages: Vec<SnapshotMessage> = Vec::new();

        let mut stmt =
            conn.prepare("SELECT id, version, address FROM outgoing_execute ORDER BY id")?;
        {
            let mut rows = stmt.query([])?;
            while let Some(row) = rows.next()? {
                let id: String = row.get(0)?;
                let version: i64 = row.get(1)?;
                let address: String = row.get(2)?;
                messages.push(SnapshotMessage { address, message: serde_json::json!({ "kind": "execute", "head": {}, "data": { "task": { "id": id, "version": version } } }) });
            }
        }

        let mut stmt = conn.prepare(
            "SELECT ou.promise_id, ou.address, p.id, p.state, p.param_headers, p.param_data, p.value_headers, p.value_data, p.tags, p.timeout_at, p.created_at, p.settled_at
             FROM outgoing_unblock ou JOIN promises p ON p.id = ou.promise_id ORDER BY ou.promise_id, ou.address"
        )?;
        {
            let mut rows = stmt.query([])?;
            while let Some(row) = rows.next()? {
                let _promise_id: String = row.get(0)?;
                let address: String = row.get(1)?;
                let promise = row_to_promise_offset(row, 2)?;
                messages.push(SnapshotMessage { address, message: serde_json::json!({ "kind": "unblock", "head": {}, "data": { "promise": promise } }) });
            }
        }

        Ok(Snapshot {
            promises,
            promise_timeouts,
            callbacks,
            listeners,
            tasks,
            task_timeouts,
            messages,
        })
    }

    fn take_outgoing(
        &self,
        batch_size: i64,
    ) -> StorageResult<(Vec<OutgoingExecute>, Vec<OutgoingUnblock>)> {
        // Atomically delete and return a batch of execute messages
        let mut execute_msgs = Vec::new();
        {
            let mut stmt = self.conn.prepare(
                "DELETE FROM outgoing_execute WHERE rowid IN (SELECT rowid FROM outgoing_execute LIMIT ?1) RETURNING id, version, address"
            )?;
            let mut rows = stmt.query(params![batch_size])?;
            while let Some(row) = rows.next()? {
                execute_msgs.push(OutgoingExecute {
                    id: row.get(0)?,
                    version: row.get(1)?,
                    address: row.get(2)?,
                });
            }
        }

        // Delete a batch of unblock messages, then join with promises for payload.
        // SQLite doesn't support DELETE in CTE WITH clauses, so we use two steps
        // within the same transaction: DELETE RETURNING, then SELECT per row.
        let mut deleted_unblocks: Vec<(String, String)> = Vec::new();
        {
            let mut stmt = self.conn.prepare(
                "DELETE FROM outgoing_unblock WHERE rowid IN (SELECT rowid FROM outgoing_unblock LIMIT ?1) RETURNING promise_id, address"
            )?;
            let mut rows = stmt.query(params![batch_size])?;
            while let Some(row) = rows.next()? {
                deleted_unblocks.push((row.get(0)?, row.get(1)?));
            }
        }

        let mut unblock_msgs = Vec::new();
        for (promise_id, address) in deleted_unblocks {
            let mut stmt = self.conn.prepare(
                "SELECT id, state, param_headers, param_data, value_headers, value_data, tags, timeout_at, created_at, settled_at FROM promises WHERE id = ?1"
            )?;
            let mut rows = stmt.query(params![promise_id])?;
            if let Some(row) = rows.next()? {
                let promise = row_to_promise_offset(row, 0)?;
                unblock_msgs.push(OutgoingUnblock { address, promise });
            }
        }

        Ok((execute_msgs, unblock_msgs))
    }
}

/// Get resumes count (number of ready callbacks) for a task
fn get_resumes(tx: &rusqlite::Connection, task_id: &str) -> rusqlite::Result<i64> {
    tx.query_row(
        "SELECT COUNT(*) FROM callbacks WHERE awaiter_id = ?1 AND ready = true",
        params![task_id],
        |row| row.get(0),
    )
}

// === Row mapping helpers ===

fn row_to_promise(row: &rusqlite::Row) -> rusqlite::Result<PromiseRecord> {
    row_to_promise_offset(row, 0)
}

fn row_to_promise_offset(row: &rusqlite::Row, offset: usize) -> rusqlite::Result<PromiseRecord> {
    let param_headers: Option<String> = row.get(offset + 2)?;
    let param_data: Option<String> = row.get(offset + 3)?;
    let value_headers: Option<String> = row.get(offset + 4)?;
    let value_data: Option<String> = row.get(offset + 5)?;
    let tags_str: String = row.get(offset + 6)?;

    let state_str: String = row.get(offset + 1)?;
    Ok(PromiseRecord {
        id: row.get(offset)?,
        state: parse_promise_state(&state_str),
        param: PromiseValue {
            headers: param_headers.map(|h| serde_json::from_str(&h).unwrap_or_default()),
            data: param_data,
        },
        value: PromiseValue {
            headers: value_headers.map(|h| serde_json::from_str(&h).unwrap_or_default()),
            data: value_data,
        },
        tags: serde_json::from_str(&tags_str).unwrap_or_default(),
        timeout_at: row.get(offset + 7)?,
        created_at: row.get(offset + 8)?,
        settled_at: row.get(offset + 9)?,
    })
}

fn row_to_schedule(row: &rusqlite::Row) -> rusqlite::Result<ScheduleRecord> {
    let param_headers: Option<String> = row.get(4)?;
    let param_data: Option<String> = row.get(5)?;
    let tags_str: String = row.get(6)?;

    Ok(ScheduleRecord {
        id: row.get(0)?,
        cron: row.get(1)?,
        promise_id: row.get(2)?,
        promise_timeout: row.get(3)?,
        promise_param: PromiseValue {
            headers: param_headers.map(|h| serde_json::from_str(&h).unwrap_or_default()),
            data: param_data,
        },
        promise_tags: serde_json::from_str(&tags_str).unwrap_or_default(),
        created_at: row.get(7)?,
        next_run_at: row.get(8)?,
        last_run_at: row.get(9)?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::processing::processing_timeouts::process_all_timeouts;
    use crate::persistence::ScheduleRun;
    use crate::types::{PromiseState, Snapshot, TaskState};

    fn with_test_db<T>(f: impl FnOnce(&SqliteDb<'_>) -> T) -> T {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let db = SqliteDb {
            conn: &conn,
            task_retry_timeout: 50,
        };
        f(&db)
    }

    fn selected_retry_timeout_ids(db: &SqliteDb<'_>, now: i64) -> Vec<String> {
        let mut stmt = db
            .conn
            .prepare(
                "SELECT tt.id FROM task_timeouts tt JOIN tasks t ON t.id = tt.id
                 WHERE tt.timeout_type = 0 AND tt.timeout_at <= ?1 AND t.state = 'pending'
                 ORDER BY tt.id",
            )
            .unwrap();
        let mut rows = stmt.query(params![now]).unwrap();
        let mut ids = Vec::new();
        while let Some(row) = rows.next().unwrap() {
            ids.push(row.get(0).unwrap());
        }
        ids
    }

    fn selected_lease_timeout_ids(db: &SqliteDb<'_>, now: i64) -> Vec<String> {
        let mut stmt = db
            .conn
            .prepare(
                "SELECT tt.id FROM task_timeouts tt JOIN tasks t ON t.id = tt.id
                 WHERE tt.timeout_type = 1 AND tt.timeout_at <= ?1 AND t.state = 'acquired'
                 ORDER BY tt.id",
            )
            .unwrap();
        let mut rows = stmt.query(params![now]).unwrap();
        let mut ids = Vec::new();
        while let Some(row) = rows.next().unwrap() {
            ids.push(row.get(0).unwrap());
        }
        ids
    }

    fn snapshot_timeout(snapshot: &Snapshot, id: &str) -> (i32, i64) {
        let row = snapshot
            .task_timeouts
            .iter()
            .find(|tt| tt.id == id)
            .unwrap_or_else(|| panic!("missing task_timeout row for {id}"));
        (row.timeout_type, row.timeout)
    }

    #[test]
    fn settlement_resumes_suspended_awaiter_and_enqueues_execute() {
        with_test_db(|db| {
            db.promise_create(&PromiseCreateParams {
                id: "awaited",
                state: "pending",
                param_headers: None,
                param_data: None,
                tags: "{}",
                timeout_at: 500,
                created_at: 0,
                settled_at: None,
                already_timedout: false,
                address: None,
            })
            .unwrap();

            let created = db
                .task_create(&TaskCreateParams {
                    promise_id: "awaiter",
                    state: "pending",
                    param_headers: None,
                    param_data: None,
                    tags: r#"{"resonate:target":"worker://tests"}"#,
                    timeout_at: 600,
                    created_at: 0,
                    settled_at: None,
                    already_timedout: false,
                    ttl: 25,
                    pid: "worker-1",
                })
                .unwrap()
                .unwrap();
            assert!(created.task_created);
            assert!(!created.task_acquired);

            let suspended = db.task_suspend("awaiter", 0, &["awaited"]).unwrap();
            assert!(suspended.task_matched);
            assert!(suspended.was_suspended);
            assert_eq!(suspended.missing_count, 0);

            let before = db.task_get("awaiter").unwrap().unwrap();
            assert_eq!(before.state, TaskState::Suspended);
            assert_eq!(before.version, 0);
            assert_eq!(before.resumes, 0);

            let settled = db
                .promise_settle(&PromiseSettleParams {
                    id: "awaited",
                    state: "resolved",
                    value_headers: None,
                    value_data: Some("done"),
                    settled_at: 100,
                })
                .unwrap();
            assert!(settled.was_settled);
            assert_eq!(settled.promise.unwrap().state, PromiseState::Resolved);

            let after = db.task_get("awaiter").unwrap().unwrap();
            assert_eq!(after.state, TaskState::Pending);
            assert_eq!(after.version, 1);
            assert_eq!(after.resumes, 1);
            let snapshot = db.snap().unwrap();
            assert!(snapshot.listeners.is_empty());
            assert_eq!(snapshot_timeout(&snapshot, "awaiter"), (0, 150));

            let (execute, unblock) = db.take_outgoing(10).unwrap();
            assert!(unblock.is_empty());
            assert_eq!(execute.len(), 1);
            assert_eq!(execute[0].id, "awaiter");
            assert_eq!(execute[0].version, 1);
            assert_eq!(execute[0].address, "worker://tests");
        });
    }

    #[test]
    fn settlement_unblocks_registered_listeners() {
        with_test_db(|db| {
            db.promise_create(&PromiseCreateParams {
                id: "awaited",
                state: "pending",
                param_headers: None,
                param_data: None,
                tags: "{}",
                timeout_at: 500,
                created_at: 0,
                settled_at: None,
                already_timedout: false,
                address: None,
            })
            .unwrap();

            let promise = db
                .promise_register_listener("awaited", "https://listener.test/hook")
                .unwrap()
                .unwrap();
            assert_eq!(promise.state, PromiseState::Pending);

            db.promise_settle(&PromiseSettleParams {
                id: "awaited",
                state: "resolved",
                value_headers: None,
                value_data: Some("payload"),
                settled_at: 101,
            })
            .unwrap();

            let snapshot = db.snap().unwrap();
            assert!(snapshot.listeners.is_empty());
            let awaited = snapshot
                .promises
                .iter()
                .find(|promise| promise.id == "awaited")
                .unwrap();
            assert_eq!(awaited.state, PromiseState::Resolved);
            assert_eq!(awaited.value.data.as_deref(), Some("payload"));

            let (execute, unblock) = db.take_outgoing(10).unwrap();
            assert!(execute.is_empty());
            assert_eq!(unblock.len(), 1);
            assert_eq!(unblock[0].address, "https://listener.test/hook");
            assert_eq!(unblock[0].promise.id, "awaited");
            assert_eq!(unblock[0].promise.state, PromiseState::Resolved);
            assert_eq!(unblock[0].promise.value.data.as_deref(), Some("payload"));
        });
    }

    #[test]
    fn schedule_run_is_idempotent_and_advances_next_run() {
        with_test_db(|db| {
            let schedule = db
                .schedule_create(&ScheduleCreateParams {
                    id: "sched",
                    cron: "* * * * *",
                    promise_id: "sched-{{.timestamp}}",
                    promise_timeout: 500,
                    promise_param_headers: None,
                    promise_param_data: Some("body"),
                    promise_tags: r#"{"env":"test"}"#,
                    created_at: 0,
                    next_run_at: 1_000,
                })
                .unwrap();
            assert_eq!(schedule.next_run_at, 1_000);
            assert_eq!(schedule.last_run_at, None);

            let runs = vec![
                ScheduleRun {
                    id: "sched-1000".to_string(),
                    timeout_at: 1_500,
                    created_at: 1_000,
                },
                ScheduleRun {
                    id: "sched-2000".to_string(),
                    timeout_at: 2_500,
                    created_at: 2_000,
                },
            ];

            let updated = db
                .schedule_run("sched", 2_000, 3_000, &runs)
                .unwrap()
                .unwrap();
            assert_eq!(updated.last_run_at, Some(2_000));
            assert_eq!(updated.next_run_at, 3_000);

            let snapshot = db.snap().unwrap();
            let created: Vec<_> = snapshot
                .promises
                .iter()
                .filter(|promise| promise.id.starts_with("sched-"))
                .collect();
            assert_eq!(created.len(), 2);
            assert!(created
                .iter()
                .all(|promise| promise.state == PromiseState::Pending));
            assert!(created
                .iter()
                .all(|promise| promise.param.data.as_deref() == Some("body")));
            assert!(created
                .iter()
                .all(|promise| promise.tags.get("env").map(String::as_str) == Some("test")));
            assert_eq!(snapshot.promise_timeouts.len(), 2);

            db.schedule_run("sched", 2_000, 3_000, &runs).unwrap();
            let snapshot = db.snap().unwrap();
            assert_eq!(
                snapshot
                    .promises
                    .iter()
                    .filter(|promise| promise.id.starts_with("sched-"))
                    .count(),
                2
            );
            assert_eq!(snapshot.promise_timeouts.len(), 2);
        });
    }

    #[test]
    fn get_expired_schedules_includes_exactly_due_and_multiple_due_but_excludes_future() {
        with_test_db(|db| {
            for (id, next_run_at) in [("sched-a", 1_000), ("sched-b", 1_000), ("sched-future", 1_001)] {
                db.schedule_create(&ScheduleCreateParams {
                    id,
                    cron: "* * * * *",
                    promise_id: "sched-{{.timestamp}}",
                    promise_timeout: 500,
                    promise_param_headers: None,
                    promise_param_data: Some("body"),
                    promise_tags: r#"{"env":"test"}"#,
                    created_at: 0,
                    next_run_at,
                })
                .unwrap();
            }

            let mut ids: Vec<_> = db
                .get_expired_schedules(1_000)
                .unwrap()
                .into_iter()
                .map(|schedule| schedule.id)
                .collect();
            ids.sort();

            assert_eq!(ids, vec!["sched-a".to_string(), "sched-b".to_string()]);
        });
    }

    #[test]
    fn process_all_timeouts_materializes_overdue_schedule_prefix() {
        with_test_db(|db| {
            db.schedule_create(&ScheduleCreateParams {
                id: "sched",
                cron: "* * * * *",
                promise_id: "sched-{{.timestamp}}",
                promise_timeout: 500,
                promise_param_headers: None,
                promise_param_data: Some("body"),
                promise_tags: r#"{"env":"test"}"#,
                created_at: 0,
                next_run_at: 60_000,
            })
            .unwrap();

            process_all_timeouts(db, 180_000).unwrap();

            let schedule = db.schedule_get("sched").unwrap().unwrap();
            assert_eq!(schedule.last_run_at, Some(180_000));
            assert_eq!(schedule.next_run_at, 240_000);

            let snapshot = db.snap().unwrap();
            let mut ids: Vec<_> = snapshot
                .promises
                .iter()
                .filter(|promise| promise.id.starts_with("sched-"))
                .map(|promise| promise.id.clone())
                .collect();
            ids.sort();
            assert_eq!(ids, vec![
                "sched-120000".to_string(),
                "sched-180000".to_string(),
                "sched-60000".to_string(),
            ]);
            assert_eq!(snapshot.promise_timeouts.len(), 3);
        });
    }

    #[test]
    fn process_timeouts_batches_promise_retry_and_lease_effects() {
        with_test_db(|db| {
            db.promise_create(&PromiseCreateParams {
                id: "awaited-batch",
                state: "pending",
                param_headers: None,
                param_data: None,
                tags: "{}",
                timeout_at: 10,
                created_at: 0,
                settled_at: None,
                already_timedout: false,
                address: None,
            })
            .unwrap();
            db.promise_register_listener("awaited-batch", "https://listener.test/batch")
                .unwrap();

            db.task_create(&TaskCreateParams {
                promise_id: "awaiter-batch",
                state: "pending",
                param_headers: None,
                param_data: None,
                tags: r#"{"resonate:target":"worker://awaiter"}"#,
                timeout_at: 1_000,
                created_at: 0,
                settled_at: None,
                already_timedout: false,
                ttl: 25,
                pid: "worker-a",
            })
            .unwrap();
            let suspended = db
                .task_suspend("awaiter-batch", 0, &["awaited-batch"])
                .unwrap();
            assert!(suspended.was_suspended);

            db.promise_create(&PromiseCreateParams {
                id: "retry-batch",
                state: "pending",
                param_headers: None,
                param_data: None,
                tags: r#"{"resonate:target":"worker://retry"}"#,
                timeout_at: 500,
                created_at: 0,
                settled_at: None,
                already_timedout: false,
                address: Some("worker://retry"),
            })
            .unwrap();
            let _ = db.take_outgoing(10).unwrap();

            db.task_create(&TaskCreateParams {
                promise_id: "lease-batch",
                state: "pending",
                param_headers: None,
                param_data: None,
                tags: r#"{"resonate:target":"worker://lease"}"#,
                timeout_at: 1_000,
                created_at: 0,
                settled_at: None,
                already_timedout: false,
                ttl: 20,
                pid: "worker-l",
            })
            .unwrap();

            db.process_timeouts(100).unwrap();

            let awaited = db.promise_get("awaited-batch").unwrap().unwrap();
            assert_eq!(awaited.state, PromiseState::RejectedTimedout);

            let awaiter = db.task_get("awaiter-batch").unwrap().unwrap();
            assert_eq!(awaiter.state, TaskState::Pending);
            assert_eq!(awaiter.version, 1);
            assert_eq!(awaiter.resumes, 1);

            let retry = db.task_get("retry-batch").unwrap().unwrap();
            assert_eq!(retry.state, TaskState::Pending);
            assert_eq!(retry.version, 0);

            let lease = db.task_get("lease-batch").unwrap().unwrap();
            assert_eq!(lease.state, TaskState::Pending);
            assert_eq!(lease.version, 1);

            let snapshot = db.snap().unwrap();
            assert!(snapshot.listeners.is_empty());
            assert_eq!(snapshot_timeout(&snapshot, "awaiter-batch"), (0, 150));
            assert_eq!(snapshot_timeout(&snapshot, "retry-batch"), (0, 150));
            assert_eq!(snapshot_timeout(&snapshot, "lease-batch"), (0, 150));
            assert!(snapshot.task_timeouts.iter().all(|tt| tt.timeout_type == 0));

            let (mut execute, unblock) = db.take_outgoing(10).unwrap();
            execute.sort_by(|a, b| a.id.cmp(&b.id));
            assert_eq!(execute.len(), 3);
            assert_eq!(execute[0].id, "awaiter-batch");
            assert_eq!(execute[0].version, 1);
            assert_eq!(execute[0].address, "worker://awaiter");
            assert_eq!(execute[1].id, "lease-batch");
            assert_eq!(execute[1].version, 1);
            assert_eq!(execute[1].address, "worker://lease");
            assert_eq!(execute[2].id, "retry-batch");
            assert_eq!(execute[2].version, 0);
            assert_eq!(execute[2].address, "worker://retry");

            assert_eq!(unblock.len(), 1);
            assert_eq!(unblock[0].address, "https://listener.test/batch");
            assert_eq!(unblock[0].promise.id, "awaited-batch");
            assert_eq!(unblock[0].promise.state, PromiseState::RejectedTimedout);
        });
    }

    #[test]
    fn timeout_query_membership_matches_snapshot_predicates() {
        with_test_db(|db| {
            db.promise_create(&PromiseCreateParams {
                id: "retry-due",
                state: "pending",
                param_headers: None,
                param_data: None,
                tags: r#"{"resonate:target":"worker://retry-due"}"#,
                timeout_at: 1_000,
                created_at: 0,
                settled_at: None,
                already_timedout: false,
                address: Some("worker://retry-due"),
            })
            .unwrap();
            db.promise_create(&PromiseCreateParams {
                id: "retry-future",
                state: "pending",
                param_headers: None,
                param_data: None,
                tags: r#"{"resonate:target":"worker://retry-future"}"#,
                timeout_at: 1_000,
                created_at: 60,
                settled_at: None,
                already_timedout: false,
                address: Some("worker://retry-future"),
            })
            .unwrap();
            let _ = db.take_outgoing(10).unwrap();

            db.promise_create(&PromiseCreateParams {
                id: "lease-due",
                state: "pending",
                param_headers: None,
                param_data: None,
                tags: r#"{"resonate:target":"worker://lease-due"}"#,
                timeout_at: 1_000,
                created_at: 0,
                settled_at: None,
                already_timedout: false,
                address: Some("worker://lease-due"),
            })
            .unwrap();
            db.promise_create(&PromiseCreateParams {
                id: "lease-future",
                state: "pending",
                param_headers: None,
                param_data: None,
                tags: r#"{"resonate:target":"worker://lease-future"}"#,
                timeout_at: 1_000,
                created_at: 0,
                settled_at: None,
                already_timedout: false,
                address: Some("worker://lease-future"),
            })
            .unwrap();
            let _ = db.take_outgoing(10).unwrap();
            let acquired_due = db
                .task_acquire(&TaskAcquireParams {
                    task_id: "lease-due",
                    version: 0,
                    time: 80,
                    ttl: 20,
                    pid: "worker-due",
                })
                .unwrap();
            assert!(acquired_due.was_acquired);
            let acquired_future = db
                .task_acquire(&TaskAcquireParams {
                    task_id: "lease-future",
                    version: 0,
                    time: 81,
                    ttl: 20,
                    pid: "worker-future",
                })
                .unwrap();
            assert!(acquired_future.was_acquired);

            let snapshot = db.snap().unwrap();
            let mut expected_retry: Vec<String> = snapshot
                .task_timeouts
                .iter()
                .filter(|tt| tt.timeout_type == 0 && tt.timeout <= 100)
                .filter(|tt| {
                    snapshot
                        .tasks
                        .iter()
                        .find(|task| task.id == tt.id)
                        .map(|task| task.state == TaskState::Pending)
                        .unwrap_or(false)
                })
                .map(|tt| tt.id.clone())
                .collect();
            expected_retry.sort();

            let mut expected_lease: Vec<String> = snapshot
                .task_timeouts
                .iter()
                .filter(|tt| tt.timeout_type == 1 && tt.timeout <= 100)
                .filter(|tt| {
                    snapshot
                        .tasks
                        .iter()
                        .find(|task| task.id == tt.id)
                        .map(|task| task.state == TaskState::Acquired)
                        .unwrap_or(false)
                })
                .map(|tt| tt.id.clone())
                .collect();
            expected_lease.sort();

            assert_eq!(selected_retry_timeout_ids(db, 100), expected_retry);
            assert_eq!(selected_lease_timeout_ids(db, 100), expected_lease);
        });
    }

    #[test]
    fn process_timeouts_updates_due_rows_without_touching_future_timeout_rows() {
        with_test_db(|db| {
            db.promise_create(&PromiseCreateParams {
                id: "retry-due",
                state: "pending",
                param_headers: None,
                param_data: None,
                tags: r#"{"resonate:target":"worker://retry-due"}"#,
                timeout_at: 1_000,
                created_at: 0,
                settled_at: None,
                already_timedout: false,
                address: Some("worker://retry-due"),
            })
            .unwrap();
            db.promise_create(&PromiseCreateParams {
                id: "retry-future",
                state: "pending",
                param_headers: None,
                param_data: None,
                tags: r#"{"resonate:target":"worker://retry-future"}"#,
                timeout_at: 1_000,
                created_at: 60,
                settled_at: None,
                already_timedout: false,
                address: Some("worker://retry-future"),
            })
            .unwrap();
            let _ = db.take_outgoing(10).unwrap();

            db.promise_create(&PromiseCreateParams {
                id: "lease-due",
                state: "pending",
                param_headers: None,
                param_data: None,
                tags: r#"{"resonate:target":"worker://lease-due"}"#,
                timeout_at: 1_000,
                created_at: 0,
                settled_at: None,
                already_timedout: false,
                address: Some("worker://lease-due"),
            })
            .unwrap();
            db.promise_create(&PromiseCreateParams {
                id: "lease-future",
                state: "pending",
                param_headers: None,
                param_data: None,
                tags: r#"{"resonate:target":"worker://lease-future"}"#,
                timeout_at: 1_000,
                created_at: 0,
                settled_at: None,
                already_timedout: false,
                address: Some("worker://lease-future"),
            })
            .unwrap();
            let _ = db.take_outgoing(10).unwrap();

            assert!(
                db.task_acquire(&TaskAcquireParams {
                    task_id: "lease-due",
                    version: 0,
                    time: 80,
                    ttl: 20,
                    pid: "worker-due",
                })
                .unwrap()
                .was_acquired
            );
            assert!(
                db.task_acquire(&TaskAcquireParams {
                    task_id: "lease-future",
                    version: 0,
                    time: 81,
                    ttl: 20,
                    pid: "worker-future",
                })
                .unwrap()
                .was_acquired
            );
            let _ = db.take_outgoing(10).unwrap();

            let before = db.snap().unwrap();
            assert_eq!(snapshot_timeout(&before, "retry-due"), (0, 50));
            assert_eq!(snapshot_timeout(&before, "retry-future"), (0, 110));
            assert_eq!(snapshot_timeout(&before, "lease-due"), (1, 100));
            assert_eq!(snapshot_timeout(&before, "lease-future"), (1, 101));

            db.process_timeouts(100).unwrap();

            let retry_due = db.task_get("retry-due").unwrap().unwrap();
            let retry_future = db.task_get("retry-future").unwrap().unwrap();
            let lease_due = db.task_get("lease-due").unwrap().unwrap();
            let lease_future = db.task_get("lease-future").unwrap().unwrap();
            let after = db.snap().unwrap();

            assert_eq!(snapshot_timeout(&after, "retry-due"), (0, 150));
            assert_eq!(snapshot_timeout(&after, "retry-future"), (0, 110));
            assert_eq!(snapshot_timeout(&after, "lease-due"), (0, 150));
            assert_eq!(snapshot_timeout(&after, "lease-future"), (1, 101));

            assert_eq!(retry_due.state, TaskState::Pending);
            assert_eq!(retry_due.version, 0);
            assert_eq!(retry_future.state, TaskState::Pending);
            assert_eq!(retry_future.version, 0);
            assert_eq!(lease_due.state, TaskState::Pending);
            assert_eq!(lease_due.version, 1);
            assert_eq!(lease_future.state, TaskState::Acquired);
            assert_eq!(lease_future.version, 0);

            let (mut execute, unblock) = db.take_outgoing(10).unwrap();
            execute.sort_by(|a, b| a.id.cmp(&b.id));
            assert_eq!(execute.len(), 2);
            assert_eq!(execute[0].id, "lease-due");
            assert_eq!(execute[0].version, 1);
            assert_eq!(execute[0].address, "worker://lease-due");
            assert_eq!(execute[1].id, "retry-due");
            assert_eq!(execute[1].version, 0);
            assert_eq!(execute[1].address, "worker://retry-due");
            assert!(unblock.is_empty());
        });
    }
}
