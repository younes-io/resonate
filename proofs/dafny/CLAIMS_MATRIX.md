# Dafny claims matrix for Resonate

This matrix is the intended public/internal boundary for the current Dafny work.

| Claim area | Dafny status | Primary proof/spec anchor | Runtime / code anchor |
|---|---|---|---|
| Promise/task state-machine validity | Proved kernel | `model/ResonateModel.dfy`, `proofs/PromiseStateMachine.dfy` | `src/types.rs`, `src/server.rs`, `src/persistence/mod.rs` |
| Timeout batch phase ordering | Proved kernel | `model/CoordinationModel.dfy`, `proofs/CoordinationProofs.dfy` | `src/persistence/persistence_sqlite.rs::process_timeouts`, `src/persistence/persistence_postgres.rs::process_timeouts` |
| Retry timeout re-enqueue semantics | Proved kernel | `proofs/TimeoutProofs.dfy`, `proofs/CoordinationProofs.dfy` | `src/persistence/persistence_sqlite.rs`, `src/persistence/persistence_postgres.rs` |
| Lease release + retry conversion semantics | Proved kernel | `proofs/TimeoutProofs.dfy`, `proofs/CoordinationProofs.dfy` | `src/persistence/persistence_sqlite.rs`, `src/persistence/persistence_postgres.rs` |
| Listener unblock and ready-awaiter resumption | Proved kernel | `model/CoordinationModel.dfy`, `proofs/CoordinationProofs.dfy` | timeout-processing statement 1 in both persistence backends |
| Schedule create/run/idempotency state semantics | Proved kernel | `model/CoordinationModel.dfy`, `proofs/CoordinationProofs.dfy` | `schedule_run` in both persistence backends |
| Due schedule selection + exhausted-prefix materialization | Partially proved kernel + runtime conformance | `model/CoordinationModel.dfy`, `proofs/CoordinationProofs.dfy`, `REFINEMENT.md` | `src/processing/processing_timeouts.rs`, `get_expired_schedules` and `schedule_run` in both persistence backends |
| Concrete SQL equivalence line-by-line | Out of scope / not yet proved | `REFINEMENT.md` | SQLite/Postgres SQL statements |
| HTTP / SSE / PubSub transport behavior | Out of scope | `README.md` proof boundary | transport/runtime layer |
| JWT/auth / listener-address authorization | Out of scope | `README.md` proof boundary | `src/auth.rs` and runtime authorization logic |
| Network faults / Tokio scheduling / wall-clock fairness | Out of scope | `README.md` proof boundary | async runtime / operational environment |

## Verification commands

- `proofs/dafny/scripts/verify.sh`
- `cargo test schedule_run_is_idempotent_and_advances_next_run`
- `cargo test get_expired_schedules_includes_exactly_due_and_multiple_due_but_excludes_future`
- `cargo test process_all_timeouts_materializes_overdue_schedule_prefix`
- `cargo test process_timeouts_batches_promise_retry_and_lease_effects`
- `cargo test process_timeouts_updates_due_rows_without_touching_future_timeout_rows`
