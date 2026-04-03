use std::process::Command;

use crate::persistence::{ScheduleRun, StorageError, StorageResult};
use crate::types::{PromiseRecord, PromiseState, ScheduleRecord, TaskRecord, TaskState};

const DAFNY_RUNTIME_KERNEL: &str = env!("RESONATE_DAFNY_RUNTIME_KERNEL_DLL");

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PromiseCreatePlan {
    pub(crate) promise_state: PromiseState,
    pub(crate) created_at: i64,
    pub(crate) settled_at: Option<i64>,
    pub(crate) task_state: Option<TaskState>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TaskTransitionPlan {
    pub(crate) allowed: bool,
    pub(crate) next_state: TaskState,
    pub(crate) next_version: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PromiseSettlePlan {
    pub(crate) allowed: bool,
    pub(crate) next_promise_state: PromiseState,
    pub(crate) next_task_state: Option<TaskState>,
    pub(crate) next_task_version: Option<i64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TaskFulfillPlan {
    pub(crate) allowed: bool,
    pub(crate) next_task_state: TaskState,
    pub(crate) next_task_version: i64,
    pub(crate) next_promise_state: PromiseState,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ScheduleCreatePlan {
    pub(crate) has_run: bool,
    pub(crate) last_run_at: Option<i64>,
    pub(crate) next_run_at: i64,
    pub(crate) promise_timeout: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ScheduleAdvancePlan {
    pub(crate) allowed: bool,
    pub(crate) has_run: bool,
    pub(crate) last_run_at: Option<i64>,
    pub(crate) next_run_at: i64,
    pub(crate) promise_timeout: i64,
}

pub(crate) fn plan_promise_create(
    now: i64,
    timeout_at: i64,
    timer: bool,
    has_target: bool,
) -> StorageResult<PromiseCreatePlan> {
    let output = run_owned_kernel(vec![
        "promise-create".to_string(),
        to_nat_string(now, "now")?,
        to_nat_string(timeout_at, "timeout_at")?,
        bool_code(timer).to_string(),
        bool_code(has_target).to_string(),
    ])?;

    let promise_state = parse_promise_state_code(parse_line_i64(output.get(0), "promise_state")?)?;
    let created_at = parse_line_i64(output.get(1), "created_at")?;
    let has_settled = parse_line_bool(output.get(2), "has_settled")?;
    let settled_at_raw = parse_line_i64(output.get(3), "settled_at")?;
    let has_task = parse_line_bool(output.get(4), "has_task")?;
    let task_state = parse_task_state_code(parse_line_i64(output.get(5), "task_state")?)?;

    Ok(PromiseCreatePlan {
        promise_state,
        created_at,
        settled_at: has_settled.then_some(settled_at_raw),
        task_state: has_task.then_some(task_state),
    })
}

pub(crate) fn plan_promise_settle(
    current_promise: PromiseState,
    new_promise: PromiseState,
    current_task: Option<&TaskRecord>,
) -> StorageResult<PromiseSettlePlan> {
    let (has_task, task_state, task_version) = match current_task {
        Some(task) => (true, task.state, task.version),
        None => (false, TaskState::Pending, 0),
    };
    let output = run_owned_kernel(vec![
        "promise-settle".to_string(),
        promise_state_code(current_promise).to_string(),
        promise_state_code(new_promise).to_string(),
        bool_code(has_task).to_string(),
        task_state_code(task_state).to_string(),
        to_nat_string(task_version, "task_version")?,
    ])?;

    Ok(PromiseSettlePlan {
        allowed: parse_line_bool(output.get(0), "allowed")?,
        next_promise_state: parse_promise_state_code(parse_line_i64(
            output.get(1),
            "next_promise_state",
        )?)?,
        next_task_state: if parse_line_bool(output.get(2), "has_task")? {
            Some(parse_task_state_code(parse_line_i64(
                output.get(3),
                "next_task_state",
            )?)?)
        } else {
            None
        },
        next_task_version: if has_task {
            Some(parse_line_i64(output.get(4), "next_task_version")?)
        } else {
            None
        },
    })
}

pub(crate) fn plan_task_acquire(
    current_state: TaskState,
    current_version: i64,
    requested_version: i64,
) -> StorageResult<TaskTransitionPlan> {
    plan_task_transition(
        "task-acquire",
        current_state,
        current_version,
        Some(requested_version),
    )
}

pub(crate) fn plan_task_release(
    current_state: TaskState,
    current_version: i64,
    requested_version: i64,
) -> StorageResult<TaskTransitionPlan> {
    plan_task_transition(
        "task-release",
        current_state,
        current_version,
        Some(requested_version),
    )
}

pub(crate) fn plan_task_halt(
    current_state: TaskState,
    current_version: i64,
) -> StorageResult<TaskTransitionPlan> {
    plan_task_transition("task-halt", current_state, current_version, None)
}

pub(crate) fn plan_task_continue(
    current_state: TaskState,
    current_version: i64,
) -> StorageResult<TaskTransitionPlan> {
    plan_task_transition("task-continue", current_state, current_version, None)
}

pub(crate) fn plan_task_fulfill(
    current_task: &TaskRecord,
    requested_version: i64,
    current_promise: PromiseState,
    new_promise: PromiseState,
) -> StorageResult<TaskFulfillPlan> {
    let output = run_owned_kernel(vec![
        "task-fulfill".to_string(),
        task_state_code(current_task.state).to_string(),
        to_nat_string(current_task.version, "current_version")?,
        to_nat_string(requested_version, "requested_version")?,
        promise_state_code(current_promise).to_string(),
        promise_state_code(new_promise).to_string(),
    ])?;

    Ok(TaskFulfillPlan {
        allowed: parse_line_bool(output.get(0), "allowed")?,
        next_task_state: parse_task_state_code(parse_line_i64(output.get(1), "next_task_state")?)?,
        next_task_version: parse_line_i64(output.get(2), "next_task_version")?,
        next_promise_state: parse_promise_state_code(parse_line_i64(
            output.get(3),
            "next_promise_state",
        )?)?,
    })
}

pub(crate) fn plan_schedule_create(
    next_run_at: i64,
    promise_timeout: i64,
) -> StorageResult<ScheduleCreatePlan> {
    let output = run_owned_kernel(vec![
        "schedule-create".to_string(),
        to_nat_string(next_run_at, "next_run_at")?,
        to_nat_string(promise_timeout, "promise_timeout")?,
    ])?;

    Ok(ScheduleCreatePlan {
        has_run: parse_line_bool(output.get(0), "has_run")?,
        last_run_at: decode_optional_nat(parse_line_i64(output.get(1), "last_run_at")?),
        next_run_at: parse_line_i64(output.get(2), "next_run_at")?,
        promise_timeout: parse_line_i64(output.get(3), "promise_timeout")?,
    })
}

pub(crate) fn plan_schedule_advance(
    schedule: &ScheduleRecord,
    runs: &[ScheduleRun],
    final_next_run_at: i64,
) -> StorageResult<ScheduleAdvancePlan> {
    let has_run = schedule.last_run_at.is_some();
    let mut args = vec![
        "schedule-advance".to_string(),
        to_nat_string(schedule.next_run_at, "schedule.next_run_at")?,
        bool_code(has_run).to_string(),
        schedule.last_run_at.unwrap_or(0).to_string(),
        to_nat_string(schedule.promise_timeout, "schedule.promise_timeout")?,
        runs.len().to_string(),
    ];
    for run in runs {
        args.push(to_nat_string(run.created_at, "run.created_at")?);
    }
    args.push(to_nat_string(final_next_run_at, "final_next_run_at")?);
    let output = run_owned_kernel(args)?;

    Ok(ScheduleAdvancePlan {
        allowed: parse_line_bool(output.get(0), "allowed")?,
        has_run: parse_line_bool(output.get(1), "has_run")?,
        last_run_at: decode_optional_nat(parse_line_i64(output.get(2), "last_run_at")?),
        next_run_at: parse_line_i64(output.get(3), "next_run_at")?,
        promise_timeout: parse_line_i64(output.get(4), "promise_timeout")?,
    })
}

pub(crate) fn validate_promise_create_result(
    plan: &PromiseCreatePlan,
    promise: &PromiseRecord,
) -> StorageResult<()> {
    if promise.state != plan.promise_state {
        return Err(StorageError::Backend(format!(
            "Dafny promise-create state mismatch: runtime {:?}, kernel {:?}",
            promise.state, plan.promise_state
        )));
    }
    if promise.created_at != plan.created_at {
        return Err(StorageError::Backend(format!(
            "Dafny promise-create created_at mismatch: runtime {}, kernel {}",
            promise.created_at, plan.created_at
        )));
    }
    if promise.settled_at != plan.settled_at {
        return Err(StorageError::Backend(format!(
            "Dafny promise-create settled_at mismatch: runtime {:?}, kernel {:?}",
            promise.settled_at, plan.settled_at
        )));
    }
    Ok(())
}

pub(crate) fn validate_task_transition_result(
    label: &str,
    plan: &TaskTransitionPlan,
    task: &TaskRecord,
) -> StorageResult<()> {
    if task.state != plan.next_state || task.version != plan.next_version {
        return Err(StorageError::Backend(format!(
            "Dafny {} mismatch: runtime ({:?}, {}), kernel ({:?}, {})",
            label, task.state, task.version, plan.next_state, plan.next_version
        )));
    }
    Ok(())
}

pub(crate) fn validate_task_fulfill_result(
    plan: &TaskFulfillPlan,
    task: &TaskRecord,
    promise: &PromiseRecord,
) -> StorageResult<()> {
    validate_task_transition_result(
        "task-fulfill",
        &TaskTransitionPlan {
            allowed: plan.allowed,
            next_state: plan.next_task_state,
            next_version: plan.next_task_version,
        },
        task,
    )?;
    if promise.state != plan.next_promise_state {
        return Err(StorageError::Backend(format!(
            "Dafny task-fulfill promise-state mismatch: runtime {:?}, kernel {:?}",
            promise.state, plan.next_promise_state
        )));
    }
    Ok(())
}

pub(crate) fn validate_promise_settle_result(
    plan: &PromiseSettlePlan,
    promise: &PromiseRecord,
    task: Option<&TaskRecord>,
) -> StorageResult<()> {
    if promise.state != plan.next_promise_state {
        return Err(StorageError::Backend(format!(
            "Dafny promise-settle state mismatch: runtime {:?}, kernel {:?}",
            promise.state, plan.next_promise_state
        )));
    }
    match (plan.next_task_state, plan.next_task_version, task) {
        (Some(expected_state), Some(expected_version), Some(actual_task)) => {
            if actual_task.state != expected_state || actual_task.version != expected_version {
                return Err(StorageError::Backend(format!(
                    "Dafny promise-settle task mismatch: runtime ({:?}, {}), kernel ({:?}, {})",
                    actual_task.state, actual_task.version, expected_state, expected_version
                )));
            }
        }
        (None, None, None) => {}
        (Some(_), Some(_), None) => {
            return Err(StorageError::Backend(
                "Dafny promise-settle expected a bound task but runtime had none".to_string(),
            ));
        }
        _ => {}
    }
    Ok(())
}

pub(crate) fn validate_schedule_create_result(
    plan: &ScheduleCreatePlan,
    schedule: &ScheduleRecord,
) -> StorageResult<()> {
    if schedule.last_run_at != plan.last_run_at
        || schedule.next_run_at != plan.next_run_at
        || schedule.promise_timeout != plan.promise_timeout
    {
        return Err(StorageError::Backend(format!(
            "Dafny schedule-create mismatch: runtime(last_run_at={:?}, next_run_at={}, promise_timeout={}), kernel(last_run_at={:?}, next_run_at={}, promise_timeout={})",
            schedule.last_run_at,
            schedule.next_run_at,
            schedule.promise_timeout,
            plan.last_run_at,
            plan.next_run_at,
            plan.promise_timeout
        )));
    }
    Ok(())
}

pub(crate) fn validate_schedule_advance_result(
    plan: &ScheduleAdvancePlan,
    updated: &ScheduleRecord,
) -> StorageResult<()> {
    if updated.last_run_at != plan.last_run_at
        || updated.next_run_at != plan.next_run_at
        || updated.promise_timeout != plan.promise_timeout
    {
        return Err(StorageError::Backend(format!(
            "Dafny schedule-advance mismatch: runtime(last_run_at={:?}, next_run_at={}, promise_timeout={}), kernel(last_run_at={:?}, next_run_at={}, promise_timeout={})",
            updated.last_run_at,
            updated.next_run_at,
            updated.promise_timeout,
            plan.last_run_at,
            plan.next_run_at,
            plan.promise_timeout
        )));
    }
    Ok(())
}

fn plan_task_transition(
    command: &str,
    current_state: TaskState,
    current_version: i64,
    requested_version: Option<i64>,
) -> StorageResult<TaskTransitionPlan> {
    let mut args = vec![
        command.to_string(),
        task_state_code(current_state).to_string(),
        to_nat_string(current_version, "current_version")?,
    ];
    if let Some(version) = requested_version {
        args.push(to_nat_string(version, "requested_version")?);
    }
    let output = run_owned_kernel(args)?;

    Ok(TaskTransitionPlan {
        allowed: parse_line_bool(output.get(0), "allowed")?,
        next_state: parse_task_state_code(parse_line_i64(output.get(1), "next_state")?)?,
        next_version: parse_line_i64(output.get(2), "next_version")?,
    })
}

fn run_kernel(args: &[&str]) -> StorageResult<Vec<String>> {
    let output = Command::new("dotnet")
        .arg(DAFNY_RUNTIME_KERNEL)
        .args(args)
        .output()
        .map_err(|e| {
            StorageError::Backend(format!(
                "failed to launch Dafny runtime kernel via dotnet {}: {}",
                DAFNY_RUNTIME_KERNEL, e
            ))
        })?;

    if !output.status.success() {
        return Err(StorageError::Backend(format!(
            "Dafny runtime kernel exited with status {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }

    let stdout = String::from_utf8(output.stdout)
        .map_err(|e| StorageError::Backend(format!("invalid runtime kernel stdout: {}", e)))?;
    let lines: Vec<_> = stdout.lines().map(|line| line.trim().to_string()).collect();
    if lines.first().map(String::as_str) == Some("ERR") {
        return Err(StorageError::Backend(
            "runtime kernel reported invalid input".to_string(),
        ));
    }
    Ok(lines)
}

fn run_owned_kernel(args: Vec<String>) -> StorageResult<Vec<String>> {
    let borrowed: Vec<&str> = args.iter().map(String::as_str).collect();
    run_kernel(&borrowed)
}

fn to_nat_string(value: i64, field: &str) -> StorageResult<String> {
    if value < 0 {
        return Err(StorageError::Backend(format!(
            "{} must be non-negative for Dafny runtime kernel, got {}",
            field, value
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

fn decode_optional_nat(value: i64) -> Option<i64> {
    (value != 0).then_some(value)
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
            "runtime kernel returned invalid promise-state code {}",
            code
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
            "runtime kernel returned invalid task-state code {}",
            code
        ))),
    }
}

fn parse_line_i64(line: Option<&String>, field: &str) -> StorageResult<i64> {
    let raw = line.ok_or_else(|| {
        StorageError::Backend(format!(
            "runtime kernel omitted required output line for {}",
            field
        ))
    })?;
    raw.parse::<i64>().map_err(|e| {
        StorageError::Backend(format!(
            "runtime kernel field {} was not an i64: {}",
            field, e
        ))
    })
}

fn parse_line_bool(line: Option<&String>, field: &str) -> StorageResult<bool> {
    match parse_line_i64(line, field)? {
        0 => Ok(false),
        1 => Ok(true),
        other => Err(StorageError::Backend(format!(
            "runtime kernel field {} was not a bool code: {}",
            field, other
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::{plan_schedule_create, plan_task_release, PromiseCreatePlan};
    use crate::types::{PromiseState, TaskState};

    #[test]
    fn runtime_kernel_plans_timeout_create_like_model() {
        let plan = super::plan_promise_create(100, 50, false, true).unwrap();
        assert_eq!(
            plan,
            PromiseCreatePlan {
                promise_state: PromiseState::RejectedTimedout,
                created_at: 50,
                settled_at: Some(50),
                task_state: Some(TaskState::Fulfilled),
            }
        );
    }

    #[test]
    fn runtime_kernel_plans_release_version_bump() {
        let plan = plan_task_release(TaskState::Acquired, 7, 7).unwrap();
        assert!(plan.allowed);
        assert_eq!(plan.next_state, TaskState::Pending);
        assert_eq!(plan.next_version, 8);
    }

    #[test]
    fn runtime_kernel_plans_schedule_create_boundary() {
        let plan = plan_schedule_create(120_000, 500).unwrap();
        assert!(!plan.has_run);
        assert_eq!(plan.last_run_at, None);
        assert_eq!(plan.next_run_at, 120_000);
        assert_eq!(plan.promise_timeout, 500);
    }
}
