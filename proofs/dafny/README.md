# Dafny verification workspace for Resonate

This directory contains a **proof-oriented semantic model** of the parts of Resonate that are a good fit for Dafny.

## Why this exists

Resonate's Rust runtime mixes durable state transitions with external effects such as HTTP handling, transports, storage engines, and asynchronous execution. Dafny is best used here to verify the **abstract semantics** that sit underneath those effects.

## What is modeled here

### In scope
- Promise lifecycle semantics inspired by `src/types.rs`, `src/server.rs`, and `src/persistence/*`
- Task lifecycle semantics (pending / acquired / suspended / halted / fulfilled)
- Timeout ownership rules inspired by `src/processing/processing_timeouts.rs`
- Callback/listener resumption and notification semantics from `src/persistence/persistence_sqlite.rs`
- Schedule execution and next-run progression from `src/processing/processing_timeouts.rs` and `src/persistence/persistence_sqlite.rs`
- Abstract storage contracts for the persistence boundary in `src/persistence/mod.rs`

### Out of scope for this first pass
- HTTP / SSE / PubSub transport behavior
- JWT/auth verification logic
- Listener-address authorization / dispatchability
- Proof that every persisted task/promise record satisfies the API-level `resonate:target` invariants
- Concrete SQLite/Postgres SQL behavior
- Tokio scheduling, network faults, or real wall-clock fairness
- A line-by-line proof of the Rust implementation

## Mapping to the Rust codebase

- `model/ResonateModel.dfy`
  - abstracts promise/task state from `src/types.rs`
  - captures core transition intent from `src/server.rs` and `src/persistence/*`
- `model/StorageSpec.dfy`
  - captures the contract boundary represented by `src/persistence/mod.rs`
- `proofs/PromiseStateMachine.dfy`
  - proves invariant preservation for state-machine operations
- `proofs/TimeoutProofs.dfy`
  - proves invariant preservation for timeout-driven transitions inspired by `src/processing/processing_timeouts.rs`
- `model/CoordinationModel.dfy`
  - abstracts callbacks, listeners, resumptions, outgoing notifications, schedule state, timeout-batch processing, named backend statement phases, backend-shaped timeout-row/timeout-query selectors, abstract batch-membership predicates, and modeled `task_timeouts.timeout_at` rows for retry/lease queries
- `proofs/CoordinationProofs.dfy`
  - proves preservation and progress laws for callback/listener notification, timeout batches, backend-phase/row-effect refinement equalities, backend-specific statement-1 listener-unblock/resume-enqueue effects, backend-specific selected-row/future-row timeout effects, backend-specific outgoing-execute version effects, exact timeout-row update laws, time-aware query-shape predicates, full duplicate-free ready/retry/lease permutations, independent promise-timeout permutations, and schedule execution
- `REFINEMENT.md`
  - maps the abstract timeout-batch model onto the SQLite/Postgres `process_timeouts` implementations

## Proof boundary

These proofs are intentionally **semantic**, not implementation-by-translation.
The point is to answer:
- what parts of Resonate are verifiable in Dafny,
- what invariants are worth proving,
- what should stay outside the Dafny boundary.

In particular, the coordination model treats outgoing execution and listener unblock as abstract effects.
It does **not** prove transport-address authorization, listener-address validity, or the callback-registration/direct-resume paths outside timeout processing.

## Running the proofs

If Dafny is installed globally:

```bash
proofs/dafny/scripts/verify.sh
```

The script uses a slightly higher Dafny verification time limit because the stronger permutation lemmas are heavier than the earlier proofs.

If you prefer a repo-local tool install:

```bash
dotnet tool restore
dotnet tool run dafny verify \
  proofs/dafny/model/Collections.dfy \
  proofs/dafny/model/ResonateModel.dfy \
  proofs/dafny/model/CoordinationModel.dfy \
  proofs/dafny/model/StorageSpec.dfy \
  proofs/dafny/proofs/PromiseStateMachine.dfy \
  proofs/dafny/proofs/TimeoutProofs.dfy \
  proofs/dafny/proofs/CoordinationProofs.dfy
```

To run the Postgres backend conformance tests against a live database:

```bash
proofs/dafny/scripts/run-postgres-conformance.sh
```

The script uses `RESONATE_TEST_POSTGRES_URL` if provided. Otherwise it first tries the repo's
`docker compose` Postgres service, and if that container cannot initialize cleanly it falls back to
a direct disposable Docker Postgres container with a host-mounted data directory.

## Next likely expansions
- stronger schedule proofs for multi-run batches rather than one-step schedule updates
- differential/property tests that check Rust backends against the abstract Dafny contract more exhaustively
- a tighter refinement argument showing the concrete SQL updates materialize the modeled timeout-row timestamps exactly
