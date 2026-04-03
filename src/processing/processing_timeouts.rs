//! Timeout processing — background loop.
//!
//! Periodically processes expired timeouts (promise, task retry, task lease)
//! and expired schedules.

use std::sync::Arc;
use std::time::Duration;

use crate::dafny_timeout_batch;
use crate::dafny_runtime_kernel;
use crate::dafny_schedule_planner;
use crate::metrics;
use crate::persistence::{Db, StorageResult};
use crate::server::Server;
use crate::util;

/// Background timeout processing loop.
pub async fn timeout_processing_loop(
    state: Arc<Server>,
    mut shutdown: tokio::sync::watch::Receiver<bool>,
) {
    let interval = Duration::from_millis(state.config.timeouts.poll_interval);

    loop {
        tokio::select! {
            _ = tokio::time::sleep(interval) => {}
            _ = shutdown.changed() => {
                tracing::info!("Timeout processing loop shutting down");
                return;
            }
        }

        if state.debug_mode.load(std::sync::atomic::Ordering::SeqCst) {
            continue;
        }

        let now = util::system_time_ms();
        if let Err(e) = state
            .storage
            .transact(move |db| process_all_timeouts(db, now))
            .await
        {
            tracing::error!("Background timeout processing failed: {}", e);
        }
    }
}

/// Process all expired timeouts at the given time.
///
/// Called by the background loop and `debug.tick`.
pub fn process_all_timeouts(db: &dyn Db, time: i64) -> StorageResult<()> {
    let before = db.snap()?;

    // Run the three tick CTE statements (promise timeouts, task retry, task lease)
    db.process_timeouts(time)?;

    let after = db.snap()?;
    dafny_timeout_batch::validate_timeout_batch_result(
        &before,
        &after,
        time,
        db.task_retry_timeout(),
    )?;

    // Process expired schedules (application-level cron computation)
    process_schedule_timeouts(db, time)?;

    Ok(())
}

/// Process expired schedule timeouts.
fn process_schedule_timeouts(db: &dyn Db, time: i64) -> StorageResult<()> {
    let expired = db.get_expired_schedules(time)?;
    for schedule in expired {
        let planned = dafny_schedule_planner::plan_schedule_batch_with_final_next(&schedule, time)?;
        let runs = planned.runs;

        if !runs.is_empty() {
            let advance_plan = dafny_runtime_kernel::plan_schedule_advance(
                &schedule,
                &runs,
                planned.final_next_run_at,
            )?;
            if !advance_plan.allowed {
                return Err(crate::persistence::StorageError::Backend(format!(
                    "Dafny schedule advance rejected runtime batch for schedule {}",
                    schedule.id
                )));
            }
            metrics::SCHEDULE_PROMISES_TOTAL.inc_by(runs.len() as f64);
            let updated = db
                .schedule_run(
                    &schedule.id,
                    runs.last().map(|r| r.created_at).unwrap(),
                    planned.final_next_run_at,
                    &runs,
                )?
                .ok_or_else(|| {
                    crate::persistence::StorageError::Backend(format!(
                        "schedule {} disappeared during schedule_run",
                        schedule.id
                    ))
                })?;
            dafny_runtime_kernel::validate_schedule_advance_result(&advance_plan, &updated)?;
        }
    }
    Ok(())
}
