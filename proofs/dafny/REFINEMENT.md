# Timeout-batch refinement notes

This note explains how the Dafny model relates to Resonate's timeout-processing code.

## Abstract batch model

`model/CoordinationModel.dfy` defines:

- `TimeoutRows`
- `ApplyPromiseTimeouts`
- `ResumeReadyAwaiters`
- `ApplyRetryTimeouts`
- `ApplyLeaseTimeouts`
- `TimeoutStatement1`
- `TimeoutStatement2`
- `TimeoutStatement3`
- `TimeoutRowsAfterStatement1`
- `TimeoutRowsAfterStatement2`
- `TimeoutRowsAfterStatement3`
- `SqliteTimeoutRowsAfterStatement1`
- `SqliteTimeoutRowsAfterStatement2`
- `SqliteTimeoutRowsAfterStatement3`
- `PostgresTimeoutRowsAfterStatement1`
- `PostgresTimeoutRowsAfterStatement2`
- `PostgresTimeoutRowsAfterStatement3`
- `ExpiredPromisesAt`
- `EligibleRetryTimeouts`
- `EligibleLeaseTimeouts`
- `ExpiredRetryTimeoutRowsAt`
- `ExpiredLeaseTimeoutRowsAt`
- `SqliteRetryTimeoutQuery`
- `SqliteLeaseTimeoutQuery`
- `PostgresRetryTimeoutQuery`
- `PostgresLeaseTimeoutQuery`
- `SqliteTimeoutStatements`
- `PostgresTimeoutStatements`
- `ProcessTimeoutBatch`

The intended reading is:

1. settle expired promises
2. resume any newly-ready suspended awaiters
3. re-enqueue expired retry timeouts
4. release expired lease timeouts back to pending and re-enqueue them

That is the smallest Dafny boundary that still captures the correctness-critical semantics of `process_timeouts`.

The statement-shaped helpers make the backend mapping explicit:

- `TimeoutStatement1` = promise settlement + ready-awaiter resumption
- `TimeoutStatement2` = retry timeout re-enqueue
- `TimeoutStatement3` = lease timeout release + re-enqueue
- `ExpiredPromisesAt` and `ReadyAwaiters` = the abstract membership predicates for the promise/ready phases
- `TimeoutRows` = an abstract model of `task_timeouts(id, timeout_type, timeout_at)` row membership/timestamps
- `TimeoutRowsAfterStatement*` = the abstract row effects of each timeout-processing statement
- `SqliteTimeoutRowsAfterStatement*` / `PostgresTimeoutRowsAfterStatement*` = backend-shaped aliases for those row effects
- `ExpiredRetryTimeoutRowsAt` / `ExpiredLeaseTimeoutRowsAt` = the exact time-filtered batch selectors corresponding to `timeout_type = 0/1 AND timeout_at <= now`
- `Sqlite*Query` / `Postgres*Query` = backend-shaped aliases for those exact time-filtered selectors

`SqliteTimeoutStatements` and `PostgresTimeoutStatements` are named aliases over that same abstract phase structure so the proof layer can mirror the concrete backend entry points at the level of semantic phase order.

## Assumed upstream invariants / excluded trust boundary

This refinement layer assumes some facts that are enforced elsewhere in the Rust system and are **not** modeled here:

- normal task creation has already established the `resonate:target` invariants needed for outgoing execution
- listener addresses are treated as opaque values here; authorization/dispatchability is outside the Dafny boundary
- callback-registration and direct-resume behavior outside timeout processing are not proved by these timeout-batch theorems

## Rust correspondence

### SQLite

`src/persistence/persistence_sqlite.rs::process_timeouts`

- Statement 1 / Phase 1:
  - settles expired promises
  - deletes promise timeout rows
- Statement 1 / Phase 2:
  - fulfills same-id tasks
  - clears their callbacks/timeouts
- Statement 1 / Phase 3:
  - resumes ready suspended awaiters
  - refreshes retry task timeouts for resumed tasks
  - enqueues outgoing execute messages
  - unblocks listeners
- Statement 2:
  - refreshes expired retry timeouts
  - re-enqueues execute messages
- Statement 3:
  - releases expired leases to pending
  - bumps version
  - converts lease timeout rows to retry timeout rows
  - re-enqueues execute messages

### Postgres

`src/persistence/persistence_postgres.rs::process_timeouts`

The same semantics are expressed with three SQL CTE statements:

- statement 1: promise settlement + resumption + listener unblock
- statement 2: retry timeout re-enqueue
- statement 3: lease release + retry conversion + re-enqueue

## Schedule-selection contract

The schedule boundary covered by the current model is intentionally narrower than full replay or worker correctness.

- due selection:
  - a schedule is due exactly when `next_run_at <= now`
  - the abstract contract is set membership, not backend row ordering
  - a not-yet-due schedule (`next_run_at > now`) is out of the selected set
- exhausted-prefix materialization:
  - once a due schedule is selected, the runtime repeatedly applies the trusted one-step cron advancement until it reaches the first strictly future cron instant
  - every realized due instant in that exhausted prefix produces one run promise with `created_at` equal to the realized instant and `timeout_at = created_at + promise_timeout`
  - the batch post-state records `last_run_at` as the last realized due instant and `next_run_at` as the first strictly future instant after the exhausted prefix
- `hasRun` mapping:
  - Dafny uses `hasRun` as the semantic bit for whether any run has been materialized
  - Rust persists that same boundary via `last_run_at`: `hasRun == false` corresponds to `last_run_at == None`, and a non-empty run batch corresponds to `last_run_at == Some(last realized run)`

## Trusted assumptions and non-goals

- trusted assumptions:
  - `util::compute_next_cron` is the trusted one-step runtime cron advancement used to exhaust the due prefix
  - SQLite/Postgres transaction semantics preserve the observable batch effects once `get_expired_schedules` and `schedule_run` are called
  - backend `get_expired_schedules` surfaces the due set according to the documented `next_run_at <= now` rule
- non-goals for this cut:
  - no general replay subsystem proof
  - no exactly-once / distributed-worker correctness claim
  - no cron-library proof
  - no line-by-line SQL proof

## What is proved

Current Dafny proofs establish:

- validity is preserved across the whole batch
- timed-out promises settle to the expected abstract state
- listeners for timed-out promises are unblocked and removed
- ready suspended awaiters resume to pending and increment version
- retry timeouts enqueue execution without changing version
- lease timeouts release tasks to pending, increment version, and enqueue execution
- pairwise order-independence for distinct retry, lease, and ready-awaiter batches
- pairwise order-independence for promise-timeout batches when the two promise IDs are coordination-independent in the abstract model
- inductive move-head-to-tail permutation lemmas for duplicate-free retry and lease batches
- block-rotation invariance for duplicate-free retry and lease batches
- full duplicate-free permutation theorems for retry and lease batches
- full permutation theorems for promise-timeout batches whose IDs are batch-independent in the abstract model
- full duplicate-free permutation theorem for ready-awaiter batches
- a `ProcessTimeoutBatch` ordering theorem showing that permuting an independent promise-timeout batch does not change the later resume/retry/lease phases
- `ProcessTimeoutBatchEqualsSqliteTimeoutStatements` and `ProcessTimeoutBatchEqualsPostgresTimeoutStatements`, which show the abstract batch matches the same three-phase semantic shape used by the SQLite/Postgres timeout-processing entry points
- backend-specific promise permutation theorems showing the SQLite/Postgres phase aliases preserve the same independent ordering guarantees as `ProcessTimeoutBatch`
- `TimeoutBatchQueryShape`, which now records the exact time-aware timeout-query inputs using `TimeoutRows`
- preservation of timeout-row validity through statement 1 and statement 2
- exact correspondence between the retry/lease query batches and the timed eligible sets:
  - eligible retry/lease IDs in the current phase state
  - whose modeled `timeout_at` row is `<= now`
- exact correspondence between those timed sets and the named SQLite/Postgres query selectors used in the refinement boundary
- exact equality between the abstract statement-row transformers and the named SQLite/Postgres row-effect aliases
- exact single-row update laws for ready/resumed, retry-expired, and lease-expired timeout rows in the abstract model
- backend-specific selected-row/future-row laws showing:
  - a retry row selected by the SQLite/Postgres query is rewritten to `now + retryDelay`
  - a lease row selected by the SQLite/Postgres query is converted into a retry row at `now + retryDelay`
  - a future retry/lease row excluded from the SQLite/Postgres query remains unchanged by that statement
- backend-specific outgoing-execute version laws showing:
  - resumed awaiters are enqueued at `version + 1`
  - selected retry rows preserve the current task version in `outgoing_execute`
  - selected lease rows enqueue the released task at `version + 1`
- backend-specific statement-1 listener/unblock laws showing:
  - timed-out promise settlement removes the listener from the live listener set
  - the same listener is present in `outgoing_unblock`
  - resumed awaiters from settlement remain reflected in backend-shaped statement-1 enqueue effects
- one-step schedule-state preservation/update laws showing:
  - `ScheduleCreate` preserves coordination validity
  - `ScheduleRun` flips `hasRun`, records `lastRunAt`, advances `nextRunAt`, and inserts the run promise
  - repeating the same modeled `ScheduleRun` is idempotent at the semantic-kernel level
- schedule-batch laws showing the abstract analogue of `process_schedule_timeouts` materialization:
  - an exhausted batch of due runs materializes each run promise in the core state
  - the schedule ends with `lastRunAt` equal to the last realized run in the batch
  - the schedule ends with `nextRunAt` equal to the post-batch next cron boundary supplied by the processing layer
- schedule-selection boundary laws showing:
  - `DueSchedulesAt` models the backend due-selection rule as `nextRunAt <= now`
  - an abstract exhausted due prefix is sufficient to justify `ScheduleRunBatch`
  - the resulting schedule post-state matches the runtime boundary shape: last realized due run in `lastRunAt`, first future cron instant in `nextRunAt`

## Replay terminology boundary

We do not yet model a general replay subsystem. For the current kernel, the precise proved statement is narrower: repeating the same modeled `ScheduleRun` against the already-advanced post-state is an observational no-op. That is the semantic nucleus we can later lift into explicit replay terminology without overclaiming a broader end-to-end replay proof.

## What is not yet proved

- full line-by-line refinement from the exact SQL/SQLite updates to Dafny
- proof that the concrete SQL queries materialize the same `TimeoutRows` object exactly
- order-independence for arbitrary batches with duplicates
- schedule processing as part of one unified refinement theorem
- proof of the cron library itself or of malformed/exhausted schedule handling beyond the trusted boundary above

## Runtime evidence

Repository tests backstop the abstraction:

- SQLite conformance tests run in normal `cargo test`
- the timeout-batch conformance test now asserts the exact post-batch `task_timeouts(timeout_type, timeout_at)` values for resumed/retried/released tasks
- the due-vs-future timeout conformance test now checks that due rows are updated while future retry/lease rows remain untouched
- the SQLite/Postgres runtime conformance tests now also assert the exact `outgoing_execute.address` and version values for resumed, retried, and released tasks
- the direct settlement tests now also assert statement-1 snapshot effects:
  - resumed awaiters get the expected retry timeout row
  - settled promises disappear from the live listener set while preserving the resolved payload in snapshots
- Postgres conformance tests exist as ignored tests and can be run with:

```bash
proofs/dafny/scripts/run-postgres-conformance.sh
```

That script uses `RESONATE_TEST_POSTGRES_URL` if provided, or first tries the repo's `docker compose`
Postgres service when Docker is available. If the compose-backed container cannot initialize cleanly,
the script falls back to a direct disposable Docker Postgres container with a host-mounted data directory.
