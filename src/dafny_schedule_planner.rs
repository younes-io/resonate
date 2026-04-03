use std::process::Command;

use crate::persistence::{ScheduleRun, StorageError, StorageResult};
use crate::types::ScheduleRecord;
use crate::util;

const MIN_CRON_SPACING_MS: i64 = 60_000;
const DAFNY_SCHEDULE_PLANNER: &str = env!("RESONATE_DAFNY_SCHEDULE_PLANNER_DLL");

pub(crate) struct PlannedScheduleBatch {
    pub(crate) runs: Vec<ScheduleRun>,
    pub(crate) final_next_run_at: i64,
}

#[derive(Debug)]
struct TrustedScheduleCandidateStream {
    candidates: Vec<i64>,
}

pub fn plan_schedule_batch_with_final_next(
    schedule: &ScheduleRecord,
    now: i64,
) -> StorageResult<PlannedScheduleBatch> {
    let candidate_stream = trusted_candidate_run_times(schedule, now)?;
    let candidate_run_times = candidate_stream.candidates;

    let mut command = Command::new("dotnet");
    command.arg(DAFNY_SCHEDULE_PLANNER).arg(now.to_string());
    for candidate in &candidate_run_times {
        command.arg(candidate.to_string());
    }

    let output = command.output().map_err(|e| {
        StorageError::Backend(format!(
            "failed to launch Dafny schedule planner via dotnet {}: {}",
            DAFNY_SCHEDULE_PLANNER, e
        ))
    })?;

    if !output.status.success() {
        return Err(StorageError::Backend(format!(
            "Dafny schedule planner exited with status {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }

    let stdout = String::from_utf8(output.stdout)
        .map_err(|e| StorageError::Backend(format!("invalid planner stdout: {}", e)))?;
    let mut lines = stdout.lines();

    let final_next_run_at = parse_line_i64(lines.next(), "final_next_run_at")?;
    let run_count = parse_line_usize(lines.next(), "run_count")?;
    let mut run_times = Vec::with_capacity(run_count);
    for idx in 0..run_count {
        run_times.push(parse_line_i64(lines.next(), &format!("run_time[{idx}]"))?);
    }

    if lines.next().is_some() {
        return Err(StorageError::Backend(
            "planner returned unexpected extra output".to_string(),
        ));
    }

    if run_times.is_empty() {
        return Err(StorageError::Backend(
            "planner returned an empty run batch for a due schedule".to_string(),
        ));
    }

    validate_planned_times(&candidate_run_times, &run_times, final_next_run_at, now)?;

    let runs = materialize_schedule_runs(schedule, &run_times)?;

    Ok(PlannedScheduleBatch {
        runs,
        final_next_run_at,
    })
}

fn trusted_candidate_run_times(
    schedule: &ScheduleRecord,
    now: i64,
) -> StorageResult<TrustedScheduleCandidateStream> {
    let candidates = trusted_candidate_run_times_with(schedule, now, |cron, current| {
        util::try_compute_next_cron(cron, current).ok_or_else(|| {
            StorageError::Backend(format!(
                "trusted compute_next_cron could not produce a next occurrence for schedule {} at {}",
                schedule.id, current
            ))
        })
    })?;

    Ok(TrustedScheduleCandidateStream { candidates })
}

fn trusted_candidate_run_times_with<F>(
    schedule: &ScheduleRecord,
    now: i64,
    mut next_step: F,
) -> StorageResult<Vec<i64>>
where
    F: FnMut(&str, i64) -> StorageResult<i64>,
{
    if schedule.next_run_at > now {
        return Err(StorageError::Backend(format!(
            "schedule {} is not due at {}",
            schedule.id, now
        )));
    }

    let elapsed = now.checked_sub(schedule.next_run_at).ok_or_else(|| {
        StorageError::Backend(format!(
            "schedule {} next_run_at {} is after planner time {}",
            schedule.id, schedule.next_run_at, now
        ))
    })?;

    let due_upper_bound = elapsed / MIN_CRON_SPACING_MS + 1;
    let due_upper_bound: usize = due_upper_bound.try_into().map_err(|_| {
        StorageError::Backend(format!(
            "schedule {} due upper bound overflowed usize",
            schedule.id
        ))
    })?;

    let mut candidates = Vec::with_capacity(due_upper_bound + 1);
    let mut current = schedule.next_run_at;
    candidates.push(current);

    for _ in 0..due_upper_bound {
        let next = next_step(&schedule.cron, current)?;
        if next <= current {
            return Err(StorageError::Backend(format!(
                "trusted compute_next_cron did not advance for schedule {} ({} -> {})",
                schedule.id, current, next
            )));
        }
        candidates.push(next);
        current = next;
    }

    validate_candidate_stream(schedule, now, &candidates)?;

    Ok(candidates)
}

fn validate_candidate_stream(
    schedule: &ScheduleRecord,
    now: i64,
    candidates: &[i64],
) -> StorageResult<()> {
    let first = candidates.first().copied().ok_or_else(|| {
        StorageError::Backend(format!(
            "trusted candidate generation produced an empty stream for schedule {}",
            schedule.id
        ))
    })?;

    if first != schedule.next_run_at {
        return Err(StorageError::Backend(format!(
            "trusted candidate generation changed schedule {} first run from {} to {}",
            schedule.id, schedule.next_run_at, first
        )));
    }

    if first > now {
        return Err(StorageError::Backend(format!(
            "trusted candidate generation for schedule {} started in the future at {} for now {}",
            schedule.id, first, now
        )));
    }

    for window in candidates.windows(2) {
        if window[1] <= window[0] {
            return Err(StorageError::Backend(format!(
                "trusted candidate generation for schedule {} was not strictly increasing ({} -> {})",
                schedule.id, window[0], window[1]
            )));
        }
    }

    if *candidates.last().unwrap() <= now {
        return Err(StorageError::Backend(format!(
            "trusted candidate generation for schedule {} did not reach a future boundary",
            schedule.id
        )));
    }

    Ok(())
}

fn validate_planned_times(
    candidates: &[i64],
    run_times: &[i64],
    final_next_run_at: i64,
    now: i64,
) -> StorageResult<()> {
    if run_times.len() >= candidates.len() {
        return Err(StorageError::Backend(
            "planner returned a run_count outside the trusted candidate stream".to_string(),
        ));
    }

    if final_next_run_at <= now {
        return Err(StorageError::Backend(format!(
            "planner returned non-future final_next_run_at {} for now {}",
            final_next_run_at, now
        )));
    }

    if run_times[0] != candidates[0] {
        return Err(StorageError::Backend(format!(
            "planner changed first due run from {} to {}",
            candidates[0], run_times[0]
        )));
    }

    for window in run_times.windows(2) {
        if window[1] <= window[0] {
            return Err(StorageError::Backend(format!(
                "planner returned non-increasing run times {} then {}",
                window[0], window[1]
            )));
        }
    }

    for &run_time in run_times {
        if run_time > now {
            return Err(StorageError::Backend(format!(
                "planner returned non-due run_time {} for now {}",
                run_time, now
            )));
        }
    }

    let expected_prefix = &candidates[..run_times.len()];
    if run_times != expected_prefix {
        return Err(StorageError::Backend(
            "planner returned run times that do not match the trusted candidate prefix".to_string(),
        ));
    }

    if candidates.get(run_times.len()).copied() != Some(final_next_run_at) {
        return Err(StorageError::Backend(
            "planner returned a final_next_run_at outside the trusted candidate stream".to_string(),
        ));
    }

    if final_next_run_at <= *run_times.last().unwrap() {
        return Err(StorageError::Backend(format!(
            "planner returned a non-advancing future boundary {} after last due run {}",
            final_next_run_at,
            run_times.last().unwrap()
        )));
    }

    Ok(())
}

fn materialize_schedule_runs(
    schedule: &ScheduleRecord,
    run_times: &[i64],
) -> StorageResult<Vec<ScheduleRun>> {
    run_times
        .iter()
        .copied()
        .map(|created_at| {
            let timeout_at = created_at.checked_add(schedule.promise_timeout).ok_or_else(|| {
                StorageError::Backend(format!(
                    "materialized schedule run overflowed timeout_at for schedule {} at {} with promise_timeout {}",
                    schedule.id, created_at, schedule.promise_timeout
                ))
            })?;

            Ok(ScheduleRun {
                id: schedule
                    .promise_id
                    .replace("{{.id}}", &schedule.id)
                    .replace("{{.timestamp}}", &created_at.to_string()),
                timeout_at,
                created_at,
            })
        })
        .collect()
}

fn parse_line_i64(line: Option<&str>, field: &str) -> StorageResult<i64> {
    let raw = line.ok_or_else(|| {
        StorageError::Backend(format!(
            "planner omitted required output line for {}",
            field
        ))
    })?;
    raw.parse::<i64>().map_err(|e| {
        StorageError::Backend(format!(
            "planner output field {} was not an i64: {}",
            field, e
        ))
    })
}

fn parse_line_usize(line: Option<&str>, field: &str) -> StorageResult<usize> {
    let raw = line.ok_or_else(|| {
        StorageError::Backend(format!(
            "planner omitted required output line for {}",
            field
        ))
    })?;
    raw.parse::<usize>().map_err(|e| {
        StorageError::Backend(format!(
            "planner output field {} was not a usize: {}",
            field, e
        ))
    })
}

#[cfg(test)]
mod tests {
    use super::{
        materialize_schedule_runs, plan_schedule_batch_with_final_next,
        trusted_candidate_run_times, trusted_candidate_run_times_with, validate_planned_times,
    };
    use crate::types::{PromiseValue, ScheduleRecord};

    fn schedule(next_run_at: i64) -> ScheduleRecord {
        ScheduleRecord {
            id: "sched".to_string(),
            cron: "* * * * *".to_string(),
            promise_id: "sched-{{.timestamp}}".to_string(),
            promise_timeout: 500,
            promise_param: PromiseValue::default(),
            promise_tags: Default::default(),
            created_at: 0,
            next_run_at,
            last_run_at: None,
        }
    }

    #[test]
    fn dafny_planner_materializes_due_prefix_and_future_boundary() {
        let planned = plan_schedule_batch_with_final_next(&schedule(60_000), 180_000).unwrap();

        let created_at: Vec<_> = planned.runs.iter().map(|run| run.created_at).collect();
        assert_eq!(created_at, vec![60_000, 120_000, 180_000]);
        assert_eq!(planned.final_next_run_at, 240_000);
    }

    #[test]
    fn dafny_planner_handles_single_due_run() {
        let planned = plan_schedule_batch_with_final_next(&schedule(60_000), 60_000).unwrap();

        let created_at: Vec<_> = planned.runs.iter().map(|run| run.created_at).collect();
        assert_eq!(created_at, vec![60_000]);
        assert_eq!(planned.final_next_run_at, 120_000);
    }

    #[test]
    fn materialized_schedule_runs_preserve_created_at_timeout_offset_and_template_id() {
        let planned = materialize_schedule_runs(&schedule(60_000), &[60_000, 120_000]).unwrap();

        assert_eq!(planned[0].id, "sched-60000");
        assert_eq!(planned[0].created_at, 60_000);
        assert_eq!(planned[0].timeout_at, 60_500);
        assert_eq!(planned[1].id, "sched-120000");
        assert_eq!(planned[1].created_at, 120_000);
        assert_eq!(planned[1].timeout_at, 120_500);
    }

    #[test]
    fn planner_validation_rejects_non_due_output_even_if_prefix_shape_looks_plausible() {
        let err = validate_planned_times(
            &[60_000, 120_000, 180_000],
            &[60_000, 120_000],
            180_000,
            90_000,
        )
        .unwrap_err();

        assert!(err
            .to_string()
            .contains("planner returned non-due run_time 120000 for now 90000"));
    }

    #[test]
    fn trusted_candidate_stream_rejects_invalid_cron_instead_of_using_fallback() {
        let mut invalid = schedule(60_000);
        invalid.cron = "not a cron".to_string();

        let err = trusted_candidate_run_times(&invalid, 60_000).unwrap_err();

        assert!(err
            .to_string()
            .contains("trusted compute_next_cron could not produce a next occurrence"));
    }

    #[test]
    fn trusted_candidate_stream_rejects_non_advancing_oracle_step() {
        let err = trusted_candidate_run_times_with(&schedule(60_000), 60_000, |_cron, current| {
            Ok(current)
        })
        .unwrap_err();

        assert!(err
            .to_string()
            .contains("trusted compute_next_cron did not advance"));
    }

    #[test]
    fn trusted_candidate_stream_requires_a_future_boundary_within_the_bounded_prefix() {
        let err = trusted_candidate_run_times_with(&schedule(60_000), 180_000, |_cron, current| {
            Ok(current + 1)
        })
        .unwrap_err();

        assert!(err.to_string().contains("did not reach a future boundary"));
    }
}
