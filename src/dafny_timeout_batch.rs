use std::collections::{BTreeMap, BTreeSet};
use std::process::Command;

use crate::persistence::{StorageError, StorageResult};
use crate::types::{PromiseState, Snapshot, SnapshotMessage, TaskState};

const DAFNY_TIMEOUT_BATCH_KERNEL: &str = env!("RESONATE_DAFNY_TIMEOUT_BATCH_KERNEL_DLL");

#[derive(Debug, Clone, PartialEq, Eq)]
struct ProjectedPromise {
    state: PromiseState,
    timer: bool,
    timeout_at: i64,
    has_timeout: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ProjectedTask {
    state: TaskState,
    version: i64,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ProjectedCallback {
    awaited: String,
    awaiter: String,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ProjectedListener {
    promise: String,
    address: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct ProjectedTimeoutBatchState {
    promises: BTreeMap<String, ProjectedPromise>,
    tasks: BTreeMap<String, ProjectedTask>,
    callbacks: BTreeMap<ProjectedCallback, bool>,
    listeners: BTreeSet<ProjectedListener>,
    outgoing_execute: BTreeMap<String, i64>,
    outgoing_unblock: BTreeSet<ProjectedListener>,
    retry_rows: BTreeMap<String, i64>,
    lease_rows: BTreeMap<String, i64>,
}

#[derive(Debug)]
struct TokenMaps {
    id_tokens: BTreeMap<String, i64>,
    ids_by_token: BTreeMap<i64, String>,
    address_tokens: BTreeMap<String, i64>,
    addresses_by_token: BTreeMap<i64, String>,
}

pub(crate) fn validate_timeout_batch_result(
    before: &Snapshot,
    after: &Snapshot,
    now: i64,
    retry_delay: i64,
) -> StorageResult<()> {
    let projected_before = project_snapshot(before)?;
    let projected_after = project_snapshot(after)?;
    let expected = plan_timeout_batch(&projected_before, now, retry_delay)?;

    if projected_after != expected {
        return Err(StorageError::Backend(format!(
            "Dafny timeout-batch mismatch:\nexpected: {expected:#?}\nactual: {projected_after:#?}"
        )));
    }

    Ok(())
}

fn project_snapshot(snapshot: &Snapshot) -> StorageResult<ProjectedTimeoutBatchState> {
    let promise_timeout_ids: BTreeSet<_> = snapshot
        .promise_timeouts
        .iter()
        .map(|row| row.id.clone())
        .collect();

    let promises = snapshot
        .promises
        .iter()
        .map(|promise| {
            (
                promise.id.clone(),
                ProjectedPromise {
                    state: promise.state,
                    timer: promise.tags.get("resonate:timer").map(String::as_str) == Some("true"),
                    timeout_at: promise.timeout_at,
                    has_timeout: promise_timeout_ids.contains(&promise.id),
                },
            )
        })
        .collect();

    let tasks = snapshot
        .tasks
        .iter()
        .map(|task| {
            (
                task.id.clone(),
                ProjectedTask {
                    state: task.state,
                    version: task.version,
                },
            )
        })
        .collect();

    let callbacks = snapshot
        .callbacks
        .iter()
        .map(|callback| {
            (
                ProjectedCallback {
                    awaited: callback.awaited.clone(),
                    awaiter: callback.awaiter.clone(),
                },
                callback.ready,
            )
        })
        .collect();

    let listeners = snapshot
        .listeners
        .iter()
        .map(|listener| ProjectedListener {
            promise: listener.promise_id.clone(),
            address: listener.address.clone(),
        })
        .collect();

    let mut outgoing_execute = BTreeMap::new();
    let mut outgoing_unblock = BTreeSet::new();
    for message in &snapshot.messages {
        project_message(message, &mut outgoing_execute, &mut outgoing_unblock)?;
    }

    let mut retry_rows = BTreeMap::new();
    let mut lease_rows = BTreeMap::new();
    for row in &snapshot.task_timeouts {
        match row.timeout_type {
            0 => {
                retry_rows.insert(row.id.clone(), row.timeout);
            }
            1 => {
                lease_rows.insert(row.id.clone(), row.timeout);
            }
            other => {
                return Err(StorageError::Backend(format!(
                    "unsupported task timeout type {other} for {} in timeout snapshot projection",
                    row.id
                )));
            }
        }
    }

    Ok(ProjectedTimeoutBatchState {
        promises,
        tasks,
        callbacks,
        listeners,
        outgoing_execute,
        outgoing_unblock,
        retry_rows,
        lease_rows,
    })
}

fn project_message(
    message: &SnapshotMessage,
    outgoing_execute: &mut BTreeMap<String, i64>,
    outgoing_unblock: &mut BTreeSet<ProjectedListener>,
) -> StorageResult<()> {
    let kind = message
        .message
        .get("kind")
        .and_then(|value| value.as_str())
        .ok_or_else(|| StorageError::Backend("snapshot message missing kind".to_string()))?;

    match kind {
        "execute" => {
            let task = message
                .message
                .get("data")
                .and_then(|value| value.get("task"))
                .ok_or_else(|| {
                    StorageError::Backend(
                        "execute snapshot message missing task payload".to_string(),
                    )
                })?;
            let id = task
                .get("id")
                .and_then(|value| value.as_str())
                .ok_or_else(|| {
                    StorageError::Backend("execute snapshot message missing task.id".to_string())
                })?;
            let version = task
                .get("version")
                .and_then(|value| value.as_i64())
                .ok_or_else(|| {
                    StorageError::Backend(
                        "execute snapshot message missing task.version".to_string(),
                    )
                })?;
            outgoing_execute.insert(id.to_string(), version);
        }
        "unblock" => {
            let promise = message
                .message
                .get("data")
                .and_then(|value| value.get("promise"))
                .and_then(|value| value.get("id"))
                .and_then(|value| value.as_str())
                .ok_or_else(|| {
                    StorageError::Backend("unblock snapshot message missing promise.id".to_string())
                })?;
            outgoing_unblock.insert(ProjectedListener {
                promise: promise.to_string(),
                address: message.address.clone(),
            });
        }
        other => {
            return Err(StorageError::Backend(format!(
                "unsupported snapshot message kind {other} in timeout projection"
            )));
        }
    }

    Ok(())
}

fn plan_timeout_batch(
    before: &ProjectedTimeoutBatchState,
    now: i64,
    retry_delay: i64,
) -> StorageResult<ProjectedTimeoutBatchState> {
    let tokens = build_tokens(before);
    let mut args = vec![
        "timeout-batch".to_string(),
        to_nat_string(now, "now")?,
        to_nat_string(retry_delay, "retry_delay")?,
        before.promises.len().to_string(),
    ];

    for (id, promise) in &before.promises {
        args.push(tokenize_id(&tokens, id)?.to_string());
        args.push(promise_state_code(promise.state).to_string());
        args.push(bool_code(promise.timer).to_string());
        args.push(to_nat_string(promise.timeout_at, "promise.timeout_at")?);
        args.push(bool_code(promise.has_timeout).to_string());
    }

    args.push(before.tasks.len().to_string());
    for (id, task) in &before.tasks {
        args.push(tokenize_id(&tokens, id)?.to_string());
        args.push(task_state_code(task.state).to_string());
        args.push(to_nat_string(task.version, "task.version")?);
    }

    args.push(before.callbacks.len().to_string());
    for (callback, ready) in &before.callbacks {
        args.push(tokenize_id(&tokens, &callback.awaited)?.to_string());
        args.push(tokenize_id(&tokens, &callback.awaiter)?.to_string());
        args.push(bool_code(*ready).to_string());
    }

    args.push(before.listeners.len().to_string());
    for listener in &before.listeners {
        args.push(tokenize_id(&tokens, &listener.promise)?.to_string());
        args.push(tokenize_address(&tokens, &listener.address)?.to_string());
    }

    args.push(before.outgoing_execute.len().to_string());
    for (id, version) in &before.outgoing_execute {
        args.push(tokenize_id(&tokens, id)?.to_string());
        args.push(to_nat_string(*version, "outgoing_execute.version")?);
    }

    args.push(before.outgoing_unblock.len().to_string());
    for listener in &before.outgoing_unblock {
        args.push(tokenize_id(&tokens, &listener.promise)?.to_string());
        args.push(tokenize_address(&tokens, &listener.address)?.to_string());
    }

    args.push(before.retry_rows.len().to_string());
    for (id, timeout_at) in &before.retry_rows {
        args.push(tokenize_id(&tokens, id)?.to_string());
        args.push(to_nat_string(*timeout_at, "retry_row.timeout_at")?);
    }

    args.push(before.lease_rows.len().to_string());
    for (id, timeout_at) in &before.lease_rows {
        args.push(tokenize_id(&tokens, id)?.to_string());
        args.push(to_nat_string(*timeout_at, "lease_row.timeout_at")?);
    }

    parse_projected_state(run_owned_kernel(args)?, &tokens)
}

fn build_tokens(before: &ProjectedTimeoutBatchState) -> TokenMaps {
    let mut ids = BTreeSet::new();
    ids.extend(before.promises.keys().cloned());
    ids.extend(before.tasks.keys().cloned());
    ids.extend(before.outgoing_execute.keys().cloned());
    ids.extend(before.retry_rows.keys().cloned());
    ids.extend(before.lease_rows.keys().cloned());
    for callback in before.callbacks.keys() {
        ids.insert(callback.awaited.clone());
        ids.insert(callback.awaiter.clone());
    }
    for listener in &before.listeners {
        ids.insert(listener.promise.clone());
    }
    for listener in &before.outgoing_unblock {
        ids.insert(listener.promise.clone());
    }

    let mut addresses = BTreeSet::new();
    addresses.extend(
        before
            .listeners
            .iter()
            .map(|listener| listener.address.clone()),
    );
    addresses.extend(
        before
            .outgoing_unblock
            .iter()
            .map(|listener| listener.address.clone()),
    );

    let id_tokens: BTreeMap<_, _> = ids
        .iter()
        .enumerate()
        .map(|(index, id)| (id.clone(), index as i64))
        .collect();
    let ids_by_token: BTreeMap<_, _> = id_tokens
        .iter()
        .map(|(id, token)| (*token, id.clone()))
        .collect();

    let address_tokens: BTreeMap<_, _> = addresses
        .iter()
        .enumerate()
        .map(|(index, address)| (address.clone(), index as i64))
        .collect();
    let addresses_by_token: BTreeMap<_, _> = address_tokens
        .iter()
        .map(|(address, token)| (*token, address.clone()))
        .collect();

    TokenMaps {
        id_tokens,
        ids_by_token,
        address_tokens,
        addresses_by_token,
    }
}

fn tokenize_id(tokens: &TokenMaps, id: &str) -> StorageResult<i64> {
    tokens
        .id_tokens
        .get(id)
        .copied()
        .ok_or_else(|| StorageError::Backend(format!("missing timeout batch id token for {id}")))
}

fn tokenize_address(tokens: &TokenMaps, address: &str) -> StorageResult<i64> {
    tokens.address_tokens.get(address).copied().ok_or_else(|| {
        StorageError::Backend(format!("missing timeout batch address token for {address}"))
    })
}

fn detokenize_id(token: i64, tokens: &TokenMaps) -> StorageResult<String> {
    tokens.ids_by_token.get(&token).cloned().ok_or_else(|| {
        StorageError::Backend(format!(
            "timeout batch kernel returned unknown id token {token}"
        ))
    })
}

fn detokenize_address(token: i64, tokens: &TokenMaps) -> StorageResult<String> {
    tokens
        .addresses_by_token
        .get(&token)
        .cloned()
        .ok_or_else(|| {
            StorageError::Backend(format!(
                "timeout batch kernel returned unknown address token {token}"
            ))
        })
}

fn parse_projected_state(
    lines: Vec<String>,
    tokens: &TokenMaps,
) -> StorageResult<ProjectedTimeoutBatchState> {
    let mut index = 0;

    let promise_count = parse_usize_line(&lines, &mut index, "promise_count")?;
    let mut promises = BTreeMap::new();
    for _ in 0..promise_count {
        let id = detokenize_id(parse_i64_line(&lines, &mut index, "promise.id")?, tokens)?;
        let state = parse_promise_state_code(parse_i64_line(&lines, &mut index, "promise.state")?)?;
        let timer = parse_bool_line(&lines, &mut index, "promise.timer")?;
        let timeout_at = parse_i64_line(&lines, &mut index, "promise.timeout_at")?;
        let has_timeout = parse_bool_line(&lines, &mut index, "promise.has_timeout")?;
        promises.insert(
            id,
            ProjectedPromise {
                state,
                timer,
                timeout_at,
                has_timeout,
            },
        );
    }

    let task_count = parse_usize_line(&lines, &mut index, "task_count")?;
    let mut tasks = BTreeMap::new();
    for _ in 0..task_count {
        let id = detokenize_id(parse_i64_line(&lines, &mut index, "task.id")?, tokens)?;
        let state = parse_task_state_code(parse_i64_line(&lines, &mut index, "task.state")?)?;
        let version = parse_i64_line(&lines, &mut index, "task.version")?;
        tasks.insert(id, ProjectedTask { state, version });
    }

    let callback_count = parse_usize_line(&lines, &mut index, "callback_count")?;
    let mut callbacks = BTreeMap::new();
    for _ in 0..callback_count {
        let awaited = detokenize_id(
            parse_i64_line(&lines, &mut index, "callback.awaited")?,
            tokens,
        )?;
        let awaiter = detokenize_id(
            parse_i64_line(&lines, &mut index, "callback.awaiter")?,
            tokens,
        )?;
        let ready = parse_bool_line(&lines, &mut index, "callback.ready")?;
        callbacks.insert(ProjectedCallback { awaited, awaiter }, ready);
    }

    let listener_count = parse_usize_line(&lines, &mut index, "listener_count")?;
    let mut listeners = BTreeSet::new();
    for _ in 0..listener_count {
        listeners.insert(ProjectedListener {
            promise: detokenize_id(
                parse_i64_line(&lines, &mut index, "listener.promise")?,
                tokens,
            )?,
            address: detokenize_address(
                parse_i64_line(&lines, &mut index, "listener.address")?,
                tokens,
            )?,
        });
    }

    let outgoing_execute_count = parse_usize_line(&lines, &mut index, "outgoing_execute_count")?;
    let mut outgoing_execute = BTreeMap::new();
    for _ in 0..outgoing_execute_count {
        outgoing_execute.insert(
            detokenize_id(
                parse_i64_line(&lines, &mut index, "outgoing_execute.id")?,
                tokens,
            )?,
            parse_i64_line(&lines, &mut index, "outgoing_execute.version")?,
        );
    }

    let outgoing_unblock_count = parse_usize_line(&lines, &mut index, "outgoing_unblock_count")?;
    let mut outgoing_unblock = BTreeSet::new();
    for _ in 0..outgoing_unblock_count {
        outgoing_unblock.insert(ProjectedListener {
            promise: detokenize_id(
                parse_i64_line(&lines, &mut index, "outgoing_unblock.promise")?,
                tokens,
            )?,
            address: detokenize_address(
                parse_i64_line(&lines, &mut index, "outgoing_unblock.address")?,
                tokens,
            )?,
        });
    }

    let retry_count = parse_usize_line(&lines, &mut index, "retry_count")?;
    let mut retry_rows = BTreeMap::new();
    for _ in 0..retry_count {
        retry_rows.insert(
            detokenize_id(parse_i64_line(&lines, &mut index, "retry_row.id")?, tokens)?,
            parse_i64_line(&lines, &mut index, "retry_row.timeout_at")?,
        );
    }

    let lease_count = parse_usize_line(&lines, &mut index, "lease_count")?;
    let mut lease_rows = BTreeMap::new();
    for _ in 0..lease_count {
        lease_rows.insert(
            detokenize_id(parse_i64_line(&lines, &mut index, "lease_row.id")?, tokens)?,
            parse_i64_line(&lines, &mut index, "lease_row.timeout_at")?,
        );
    }

    if index != lines.len() {
        return Err(StorageError::Backend(
            "timeout batch kernel returned unexpected extra output".to_string(),
        ));
    }

    Ok(ProjectedTimeoutBatchState {
        promises,
        tasks,
        callbacks,
        listeners,
        outgoing_execute,
        outgoing_unblock,
        retry_rows,
        lease_rows,
    })
}

fn run_kernel(args: &[&str]) -> StorageResult<Vec<String>> {
    let output = Command::new("dotnet")
        .arg(DAFNY_TIMEOUT_BATCH_KERNEL)
        .args(args)
        .output()
        .map_err(|e| {
            StorageError::Backend(format!(
                "failed to launch Dafny timeout batch kernel via dotnet {}: {}",
                DAFNY_TIMEOUT_BATCH_KERNEL, e
            ))
        })?;

    if !output.status.success() {
        return Err(StorageError::Backend(format!(
            "Dafny timeout batch kernel exited with status {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }

    let stdout = String::from_utf8(output.stdout).map_err(|e| {
        StorageError::Backend(format!("invalid timeout batch kernel stdout: {}", e))
    })?;
    let lines: Vec<_> = stdout.lines().map(|line| line.trim().to_string()).collect();
    if lines.first().map(String::as_str) == Some("ERR") {
        return Err(StorageError::Backend(
            "timeout batch kernel reported invalid input".to_string(),
        ));
    }
    Ok(lines)
}

fn run_owned_kernel(args: Vec<String>) -> StorageResult<Vec<String>> {
    let borrowed: Vec<&str> = args.iter().map(String::as_str).collect();
    run_kernel(&borrowed)
}

fn parse_string_line(lines: &[String], index: &mut usize, field: &str) -> StorageResult<String> {
    let value = lines
        .get(*index)
        .cloned()
        .ok_or_else(|| StorageError::Backend(format!("timeout batch kernel omitted {field}")))?;
    *index += 1;
    Ok(value)
}

fn parse_i64_line(lines: &[String], index: &mut usize, field: &str) -> StorageResult<i64> {
    let raw = parse_string_line(lines, index, field)?;
    raw.parse::<i64>().map_err(|e| {
        StorageError::Backend(format!(
            "timeout batch kernel field {field} was not an i64: {e}"
        ))
    })
}

fn parse_usize_line(lines: &[String], index: &mut usize, field: &str) -> StorageResult<usize> {
    let raw = parse_string_line(lines, index, field)?;
    raw.parse::<usize>().map_err(|e| {
        StorageError::Backend(format!(
            "timeout batch kernel field {field} was not a usize: {e}"
        ))
    })
}

fn parse_bool_line(lines: &[String], index: &mut usize, field: &str) -> StorageResult<bool> {
    match parse_i64_line(lines, index, field)? {
        0 => Ok(false),
        1 => Ok(true),
        other => Err(StorageError::Backend(format!(
            "timeout batch kernel field {field} was not a bool code: {other}"
        ))),
    }
}

fn to_nat_string(value: i64, field: &str) -> StorageResult<String> {
    if value < 0 {
        return Err(StorageError::Backend(format!(
            "{field} must be non-negative for Dafny timeout batch kernel, got {value}"
        )));
    }
    Ok(value.to_string())
}

fn bool_code(value: bool) -> &'static str {
    if value {
        "1"
    } else {
        "0"
    }
}

fn promise_state_code(state: PromiseState) -> i64 {
    match state {
        PromiseState::Pending => 0,
        PromiseState::Resolved => 1,
        PromiseState::Rejected => 2,
        PromiseState::RejectedCanceled => 3,
        PromiseState::RejectedTimedout => 4,
    }
}

fn parse_promise_state_code(code: i64) -> StorageResult<PromiseState> {
    match code {
        0 => Ok(PromiseState::Pending),
        1 => Ok(PromiseState::Resolved),
        2 => Ok(PromiseState::Rejected),
        3 => Ok(PromiseState::RejectedCanceled),
        4 => Ok(PromiseState::RejectedTimedout),
        _ => Err(StorageError::Backend(format!(
            "timeout batch kernel returned invalid promise-state code {code}"
        ))),
    }
}

fn task_state_code(state: TaskState) -> i64 {
    match state {
        TaskState::Pending => 0,
        TaskState::Acquired => 1,
        TaskState::Suspended => 2,
        TaskState::Halted => 3,
        TaskState::Fulfilled => 4,
    }
}

fn parse_task_state_code(code: i64) -> StorageResult<TaskState> {
    match code {
        0 => Ok(TaskState::Pending),
        1 => Ok(TaskState::Acquired),
        2 => Ok(TaskState::Suspended),
        3 => Ok(TaskState::Halted),
        4 => Ok(TaskState::Fulfilled),
        _ => Err(StorageError::Backend(format!(
            "timeout batch kernel returned invalid task-state code {code}"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::validate_timeout_batch_result;
    use crate::types::{
        PromiseRecord, PromiseState, PromiseValue, Snapshot, SnapshotCallback, SnapshotListener,
        SnapshotMessage, SnapshotPromiseTimeout, SnapshotTaskTimeout, TaskRecord, TaskState,
    };
    use serde_json::json;
    use std::collections::HashMap;

    fn promise(id: &str, state: PromiseState, timeout_at: i64, timer: bool) -> PromiseRecord {
        let mut tags = HashMap::new();
        if timer {
            tags.insert("resonate:timer".to_string(), "true".to_string());
        }
        PromiseRecord {
            id: id.to_string(),
            state,
            param: PromiseValue::default(),
            value: PromiseValue::default(),
            tags,
            timeout_at,
            created_at: 0,
            settled_at: None,
        }
    }

    fn task(id: &str, state: TaskState, version: i64, resumes: i64) -> TaskRecord {
        TaskRecord {
            id: id.to_string(),
            state,
            version,
            resumes,
            ttl: None,
            pid: None,
        }
    }

    #[test]
    fn timeout_batch_kernel_validates_timeout_resume_retry_and_lease_projection() {
        let before = Snapshot {
            promises: vec![
                promise("awaited", PromiseState::Pending, 10, false),
                promise("awaiter", PromiseState::Pending, 500, false),
                promise("retry", PromiseState::Pending, 500, false),
                promise("lease", PromiseState::Pending, 500, false),
            ],
            promise_timeouts: vec![SnapshotPromiseTimeout {
                id: "awaited".to_string(),
                timeout: 10,
            }],
            callbacks: vec![SnapshotCallback {
                awaiter: "awaiter".to_string(),
                awaited: "awaited".to_string(),
                ready: false,
            }],
            listeners: vec![SnapshotListener {
                promise_id: "awaited".to_string(),
                address: "https://listener.test/hook".to_string(),
            }],
            tasks: vec![
                task("awaiter", TaskState::Suspended, 0, 0),
                task("retry", TaskState::Pending, 0, 0),
                task("lease", TaskState::Acquired, 0, 0),
            ],
            task_timeouts: vec![
                SnapshotTaskTimeout {
                    id: "retry".to_string(),
                    timeout_type: 0,
                    timeout: 50,
                },
                SnapshotTaskTimeout {
                    id: "lease".to_string(),
                    timeout_type: 1,
                    timeout: 90,
                },
            ],
            messages: vec![],
        };

        let after = Snapshot {
            promises: vec![
                promise("awaited", PromiseState::RejectedTimedout, 10, false),
                promise("awaiter", PromiseState::Pending, 500, false),
                promise("retry", PromiseState::Pending, 500, false),
                promise("lease", PromiseState::Pending, 500, false),
            ],
            promise_timeouts: vec![],
            callbacks: vec![SnapshotCallback {
                awaiter: "awaiter".to_string(),
                awaited: "awaited".to_string(),
                ready: true,
            }],
            listeners: vec![],
            tasks: vec![
                task("awaiter", TaskState::Pending, 1, 1),
                task("retry", TaskState::Pending, 0, 0),
                task("lease", TaskState::Pending, 1, 0),
            ],
            task_timeouts: vec![
                SnapshotTaskTimeout {
                    id: "awaiter".to_string(),
                    timeout_type: 0,
                    timeout: 150,
                },
                SnapshotTaskTimeout {
                    id: "retry".to_string(),
                    timeout_type: 0,
                    timeout: 150,
                },
                SnapshotTaskTimeout {
                    id: "lease".to_string(),
                    timeout_type: 0,
                    timeout: 150,
                },
            ],
            messages: vec![
                SnapshotMessage {
                    address: "worker://awaiter".to_string(),
                    message: json!({ "kind": "execute", "data": { "task": { "id": "awaiter", "version": 1 } } }),
                },
                SnapshotMessage {
                    address: "worker://retry".to_string(),
                    message: json!({ "kind": "execute", "data": { "task": { "id": "retry", "version": 0 } } }),
                },
                SnapshotMessage {
                    address: "worker://lease".to_string(),
                    message: json!({ "kind": "execute", "data": { "task": { "id": "lease", "version": 1 } } }),
                },
                SnapshotMessage {
                    address: "https://listener.test/hook".to_string(),
                    message: json!({ "kind": "unblock", "data": { "promise": { "id": "awaited" } } }),
                },
            ],
        };

        validate_timeout_batch_result(&before, &after, 100, 50).unwrap();
    }

    #[test]
    fn timeout_batch_kernel_rejects_mismatched_released_lease_version() {
        let before = Snapshot {
            promises: vec![promise("lease", PromiseState::Pending, 500, false)],
            promise_timeouts: vec![],
            callbacks: vec![],
            listeners: vec![],
            tasks: vec![task("lease", TaskState::Acquired, 0, 0)],
            task_timeouts: vec![SnapshotTaskTimeout {
                id: "lease".to_string(),
                timeout_type: 1,
                timeout: 100,
            }],
            messages: vec![],
        };

        let after = Snapshot {
            promises: vec![promise("lease", PromiseState::Pending, 500, false)],
            promise_timeouts: vec![],
            callbacks: vec![],
            listeners: vec![],
            tasks: vec![task("lease", TaskState::Pending, 0, 0)],
            task_timeouts: vec![SnapshotTaskTimeout {
                id: "lease".to_string(),
                timeout_type: 0,
                timeout: 150,
            }],
            messages: vec![SnapshotMessage {
                address: "worker://lease".to_string(),
                message: json!({ "kind": "execute", "data": { "task": { "id": "lease", "version": 0 } } }),
            }],
        };

        let err = validate_timeout_batch_result(&before, &after, 100, 50).unwrap_err();
        assert!(err.to_string().contains("Dafny timeout-batch mismatch"));
    }
}
