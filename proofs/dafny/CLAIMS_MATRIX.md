# Dafny claims matrix for Resonate

This matrix is the intended public/internal boundary for the current Dafny work.

| Claim area | Dafny status | Primary proof/spec anchor | Runtime / code anchor |
|---|---|---|---|
| Promise/task state-machine validity | Proved kernel + executable transition kernel + live runtime validation for promise create/settle and task acquire/release/fulfill/halt/continue | `model/ResonateModel.dfy`, `proofs/PromiseStateMachine.dfy`, `executable/RuntimeStateKernel.dfy` | `src/dafny_runtime_kernel.rs`, `src/server.rs`, `src/types.rs`, `src/persistence/mod.rs` |
| Timeout batch phase ordering | Proved kernel + executable timeout-batch kernel + live runtime validation over timeout snapshot semantics | `model/CoordinationModel.dfy`, `proofs/CoordinationProofs.dfy`, `executable/TimeoutBatchKernel.dfy` | `src/dafny_timeout_batch.rs`, `src/processing/processing_timeouts.rs`, `src/persistence/persistence_sqlite.rs::process_timeouts`, `src/persistence/persistence_postgres.rs::process_timeouts` |
| Retry timeout re-enqueue semantics | Proved kernel + executable timeout-batch kernel + live runtime validation over timeout snapshot semantics | `proofs/TimeoutProofs.dfy`, `proofs/CoordinationProofs.dfy`, `executable/TimeoutBatchKernel.dfy` | `src/dafny_timeout_batch.rs`, `src/processing/processing_timeouts.rs`, `src/persistence/persistence_sqlite.rs`, `src/persistence/persistence_postgres.rs` |
| Lease release + retry conversion semantics | Proved kernel + executable timeout-batch kernel + live runtime validation over timeout snapshot semantics | `proofs/TimeoutProofs.dfy`, `proofs/CoordinationProofs.dfy`, `executable/TimeoutBatchKernel.dfy` | `src/dafny_timeout_batch.rs`, `src/processing/processing_timeouts.rs`, `src/persistence/persistence_sqlite.rs`, `src/persistence/persistence_postgres.rs` |
| Listener unblock and ready-awaiter resumption | Proved kernel + executable timeout-batch kernel + live runtime validation over timeout snapshot semantics | `model/CoordinationModel.dfy`, `proofs/CoordinationProofs.dfy`, `executable/TimeoutBatchKernel.dfy` | `src/dafny_timeout_batch.rs`, `src/processing/processing_timeouts.rs`, timeout-processing statement 1 in both persistence backends |
| Schedule create/run/idempotency state semantics | Proved kernel + executable schedule state kernel + live runtime validation for schedule.create and schedule_run batch post-state | `model/CoordinationModel.dfy`, `proofs/CoordinationProofs.dfy`, `executable/RuntimeStateKernel.dfy` | `src/dafny_runtime_kernel.rs`, `src/server.rs`, `src/processing/processing_timeouts.rs`, `schedule_run` in both persistence backends |
| Due schedule selection + trusted cron-step candidate shaping + exhausted-prefix materialization | Proved kernel + executable planner refinement + runtime conformance over an explicit trusted one-step oracle boundary | `model/CoordinationModel.dfy`, `proofs/CoordinationProofs.dfy`, `proofs/dafny/executable/SchedulePlannerKernel.dfy`, `REFINEMENT.md` | `src/dafny_schedule_planner.rs`, `src/processing/processing_timeouts.rs`, `get_expired_schedules` and `schedule_run` in both persistence backends |
| Concrete SQL equivalence line-by-line | Out of scope / not yet proved | `REFINEMENT.md` | SQLite/Postgres SQL statements |
| HTTP / SSE / PubSub transport behavior | Out of scope | `README.md` proof boundary | transport/runtime layer |
| JWT/auth / listener-address authorization | Out of scope | `README.md` proof boundary | `src/auth.rs` and runtime authorization logic |
| Network faults / Tokio scheduling / wall-clock fairness | Out of scope | `README.md` proof boundary | async runtime / operational environment |

## Verification commands

- `proofs/dafny/scripts/verify.sh`
- `cargo test schedule_run_is_idempotent_and_advances_next_run`
- `cargo test get_expired_schedules_includes_exactly_due_and_multiple_due_but_excludes_future`
- `cargo test process_all_timeouts_materializes_overdue_schedule_prefix`
- `cargo test runtime_kernel_plans_timeout_create_like_model`
- `cargo test runtime_kernel_plans_release_version_bump`
- `cargo test runtime_kernel_plans_schedule_create_boundary`
- `cargo test dafny_planner_materializes_due_prefix_and_future_boundary`
- `cargo test materialized_schedule_runs_preserve_created_at_timeout_offset_and_template_id`
- `cargo test planner_validation_rejects_non_due_output_even_if_prefix_shape_looks_plausible`
- `cargo test trusted_candidate_stream_rejects_invalid_cron_instead_of_using_fallback`
- `cargo test trusted_candidate_stream_rejects_non_advancing_oracle_step`
- `cargo test trusted_candidate_stream_requires_a_future_boundary_within_the_bounded_prefix`
- `cargo test process_timeouts_batches_promise_retry_and_lease_effects`
- `cargo test process_timeouts_updates_due_rows_without_touching_future_timeout_rows`
- `cargo test timeout_batch_kernel_validates_timeout_resume_retry_and_lease_projection`
- `cargo test timeout_batch_kernel_rejects_mismatched_released_lease_version`
