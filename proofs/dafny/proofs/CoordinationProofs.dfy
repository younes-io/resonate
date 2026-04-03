include "../model/ResonateModel.dfy"
include "../model/CoordinationModel.dfy"
include "../executable/SchedulePlannerKernel.dfy"
include "../executable/RuntimeStateKernel.dfy"
include "../executable/TimeoutBatchKernel.dfy"

module ResonateCoordinationProofs {
  import Core = ResonateModel
  import C = ResonateCoordinationModel
  import K = SchedulePlannerKernel
  import RK = RuntimeStateKernel
  import TK = TimeoutBatchKernel

  function TimeoutKernelPromiseState(state: TK.PromiseState): Core.PromiseState {
    if state == TK.Pending then Core.Pending
    else if state == TK.Resolved then Core.Resolved
    else if state == TK.Rejected then Core.Rejected
    else if state == TK.RejectedCanceled then Core.RejectedCanceled
    else Core.RejectedTimedout
  }

  function TimeoutKernelTaskState(state: TK.TaskState): Core.TaskState {
    if state == TK.TaskPending then Core.TaskPending
    else if state == TK.Acquired then Core.Acquired
    else if state == TK.Suspended then Core.Suspended
    else if state == TK.Halted then Core.Halted
    else Core.Fulfilled
  }

  function TimeoutKernelPromises(promises: map<C.Id, TK.PromiseRec>): map<C.Id, Core.Promise> {
    map id: C.Id | id in promises :: Core.PromiseRec(
      TimeoutKernelPromiseState(promises[id].state),
      promises[id].timeoutAt,
      promises[id].timer)
  }

  function TimeoutKernelTasks(tasks: map<C.Id, TK.TaskRec>): map<C.Id, Core.Task> {
    map id: C.Id | id in tasks :: Core.TaskRec(
      TimeoutKernelTaskState(tasks[id].state),
      tasks[id].version)
  }

  function TimeoutKernelCallbacks(callbacks: set<TK.CallbackKey>): set<C.CallbackKey> {
    set tcb: TK.CallbackKey | tcb in callbacks :: C.CallbackKey(tcb.awaited, tcb.awaiter)
  }

  function TimeoutKernelListeners(listeners: set<TK.ListenerKey>): set<C.ListenerKey> {
    set tl: TK.ListenerKey | tl in listeners :: C.ListenerKey(tl.promise, tl.address)
  }

  function TimeoutKernelRows(rows: TK.TimeoutRows): C.TimeoutRows {
    C.TimeoutRowsRec(rows.retryAt, rows.leaseAt)
  }

  function TimeoutKernelState(state: TK.TimeoutBatchState, rows: TK.TimeoutRows): C.CoordinationState {
    C.State(
      Core.State(
        TimeoutKernelPromises(state.promises),
        TimeoutKernelTasks(state.tasks),
        state.promiseTimeouts,
        set id: C.Id | id in rows.retryAt,
        set id: C.Id | id in rows.leaseAt),
      TimeoutKernelCallbacks(state.callbacks),
      TimeoutKernelCallbacks(state.readyCallbacks),
      TimeoutKernelListeners(state.listeners),
      state.outgoingExec,
      TimeoutKernelListeners(state.outgoingUnblock),
      map[])
  }

  lemma TimeoutKernelHasReadyCallbackMatchesModel(s: TK.TimeoutBatchState, rows: TK.TimeoutRows, awaiter: C.Id)
    ensures TK.HasReadyCallbackFor(s, awaiter) <==> C.HasReadyCallbackFor(TimeoutKernelState(s, rows), awaiter)
  {
    if TK.HasReadyCallbackFor(s, awaiter) {
      var tcb: TK.CallbackKey :| tcb in s.readyCallbacks && tcb.awaiter == awaiter;
      assert C.CallbackKey(tcb.awaited, tcb.awaiter) in TimeoutKernelState(s, rows).readyCallbacks;
    }
    if C.HasReadyCallbackFor(TimeoutKernelState(s, rows), awaiter) {
      var cb: C.CallbackKey :| cb in TimeoutKernelState(s, rows).readyCallbacks && cb.awaiter == awaiter;
      assert cb in TimeoutKernelCallbacks(s.readyCallbacks);
    }
  }

  predicate DistinctIds(xs: seq<C.Id>)
    decreases |xs|
  {
    |xs| == 0 || (xs[0] !in xs[1..] && DistinctIds(xs[1..]))
  }

  lemma DistinctIdsTail(head: C.Id, tail: seq<C.Id>)
    requires DistinctIds([head] + tail)
    ensures DistinctIds(tail)
    ensures |tail| == 0 || head != tail[0]
    ensures |tail| == 0 || DistinctIds([head] + tail[1..])
  {
    if |tail| != 0 {
      assert [head] + tail == [head] + tail;
    }
  }

  lemma EmptyCoordinationStateIsValid()
    ensures C.Valid(C.EmptyState())
  {
  }

  lemma EmptyTimeoutRowsAreValid()
    ensures C.ValidTimeoutRows(C.EmptyState(), C.EmptyTimeoutRows())
  {
  }

  lemma RegisterCallbackPreservesValidity(s: C.CoordinationState, awaited: C.Id, awaiter: C.Id)
    requires C.Valid(s)
    ensures C.Valid(C.RegisterCallback(s, awaited, awaiter))
  {
  }

  lemma RegisterSettledCallbackResumesAwaiter(s: C.CoordinationState, awaited: C.Id, awaiter: C.Id)
    requires C.Valid(s)
    requires awaited in s.core.promises
    requires awaiter in s.core.tasks
    requires s.core.promises[awaited].state != Core.Pending
    requires s.core.tasks[awaiter].state == Core.Suspended
    ensures C.RegisterCallback(s, awaited, awaiter).core.tasks[awaiter].state == Core.TaskPending
    ensures C.RegisterCallback(s, awaited, awaiter).core.tasks[awaiter].version == s.core.tasks[awaiter].version + 1
    ensures awaiter in C.RegisterCallback(s, awaited, awaiter).outgoingExec
  {
  }

  lemma RegisterListenerPreservesValidity(s: C.CoordinationState, promise: C.Id, address: C.Address)
    requires C.Valid(s)
    ensures C.Valid(C.RegisterListener(s, promise, address))
  {
  }

  lemma SettleAndNotifyPreservesValidity(s: C.CoordinationState, id: C.Id, newState: Core.PromiseState)
    requires C.Valid(s)
    ensures C.Valid(C.SettleAndNotify(s, id, newState))
  {
  }

  lemma SettledPromiseReadiesAwaiters(s: C.CoordinationState, awaited: C.Id, awaiter: C.Id)
    requires C.Valid(s)
    requires awaited in s.core.promises
    requires s.core.promises[awaited].state == Core.Pending
    requires C.CallbackKey(awaited, awaiter) in s.callbacks
    requires awaiter != awaited
    ensures C.CallbackKey(awaited, awaiter) in C.SettleAndNotify(s, awaited, Core.Resolved).readyCallbacks
  {
  }

  lemma SettledPromiseUnblocksListeners(s: C.CoordinationState, promise: C.Id, address: C.Address)
    requires C.Valid(s)
    requires promise in s.core.promises
    requires s.core.promises[promise].state == Core.Pending
    requires C.ListenerKey(promise, address) in s.listeners
    ensures C.ListenerKey(promise, address) in C.SettleAndNotify(s, promise, Core.Resolved).outgoingUnblock
    ensures C.ListenerKey(promise, address) !in C.SettleAndNotify(s, promise, Core.Resolved).listeners
  {
  }

  lemma ResumeReadyAwaiterPreservesValidity(s: C.CoordinationState, awaiter: C.Id)
    requires C.Valid(s)
    ensures C.Valid(C.ResumeReadyAwaiter(s, awaiter))
  {
  }

  lemma ReadyAwaiterResumesToPending(s: C.CoordinationState, awaiter: C.Id)
    requires C.Valid(s)
    requires awaiter in s.core.tasks
    requires s.core.tasks[awaiter].state == Core.Suspended
    requires C.HasReadyCallbackFor(s, awaiter)
    ensures C.ResumeReadyAwaiter(s, awaiter).core.tasks[awaiter].state == Core.TaskPending
    ensures C.ResumeReadyAwaiter(s, awaiter).core.tasks[awaiter].version == s.core.tasks[awaiter].version + 1
    ensures awaiter in C.ResumeReadyAwaiter(s, awaiter).outgoingExec
    ensures C.ResumeReadyAwaiter(s, awaiter).outgoingExec[awaiter] == s.core.tasks[awaiter].version + 1
  {
  }

  lemma ExpirePromiseTimeoutPreservesValidity(s: C.CoordinationState, id: C.Id)
    requires C.Valid(s)
    ensures C.Valid(C.ExpirePromiseTimeout(s, id))
  {
  }

  lemma ExpireRetryTimeoutPreservesValidity(s: C.CoordinationState, id: C.Id)
    requires C.Valid(s)
    ensures C.Valid(C.ExpireRetryTimeout(s, id))
  {
  }

  lemma ExpireLeaseTimeoutPreservesValidity(s: C.CoordinationState, id: C.Id)
    requires C.Valid(s)
    ensures C.Valid(C.ExpireLeaseTimeout(s, id))
  {
  }

  lemma ExpirePromiseTimeoutRowsPreservesValidity(s: C.CoordinationState, rows: C.TimeoutRows, id: C.Id)
    requires C.Valid(s)
    requires C.ValidTimeoutRows(s, rows)
    ensures C.ValidTimeoutRows(C.ExpirePromiseTimeout(s, id), C.ExpirePromiseTimeoutRows(s, rows, id))
  {
  }

  lemma ResumeReadyAwaiterRowsPreservesValidity(s: C.CoordinationState, rows: C.TimeoutRows, awaiter: C.Id, now: nat, retryDelay: nat)
    requires C.Valid(s)
    requires C.ValidTimeoutRows(s, rows)
    ensures C.ValidTimeoutRows(C.ResumeReadyAwaiter(s, awaiter), C.ResumeReadyAwaiterRows(s, rows, awaiter, now, retryDelay))
  {
  }

  lemma ExpireRetryTimeoutRowsPreservesValidity(s: C.CoordinationState, rows: C.TimeoutRows, id: C.Id, now: nat, retryDelay: nat)
    requires C.Valid(s)
    requires C.ValidTimeoutRows(s, rows)
    ensures C.ValidTimeoutRows(C.ExpireRetryTimeout(s, id), C.ExpireRetryTimeoutRows(s, rows, id, now, retryDelay))
  {
  }

  lemma ResumeReadyAwaiterRowsSetsRetryTimeout(s: C.CoordinationState, rows: C.TimeoutRows, awaiter: C.Id, now: nat, retryDelay: nat)
    requires awaiter in s.core.tasks
    requires s.core.tasks[awaiter].state == Core.Suspended
    requires C.HasReadyCallbackFor(s, awaiter)
    ensures awaiter in C.ResumeReadyAwaiterRows(s, rows, awaiter, now, retryDelay).retryAt
    ensures C.ResumeReadyAwaiterRows(s, rows, awaiter, now, retryDelay).retryAt[awaiter] == now + retryDelay
    ensures awaiter !in C.ResumeReadyAwaiterRows(s, rows, awaiter, now, retryDelay).leaseAt
  {
  }

  lemma ExpireRetryTimeoutRowsSetsSelectedRetryTimeout(s: C.CoordinationState, rows: C.TimeoutRows, id: C.Id, now: nat, retryDelay: nat)
    requires id in rows.retryAt
    requires id in s.core.tasks
    requires s.core.tasks[id].state == Core.TaskPending
    requires rows.retryAt[id] <= now
    ensures id in C.ExpireRetryTimeoutRows(s, rows, id, now, retryDelay).retryAt
    ensures C.ExpireRetryTimeoutRows(s, rows, id, now, retryDelay).retryAt[id] == now + retryDelay
    ensures C.ExpireRetryTimeoutRows(s, rows, id, now, retryDelay).leaseAt == rows.leaseAt
  {
  }

  lemma ExpireRetryTimeoutRowsPreservesOtherRetryTimeout(s: C.CoordinationState, rows: C.TimeoutRows, id: C.Id, other: C.Id, now: nat, retryDelay: nat)
    requires other in rows.retryAt
    requires other != id
    ensures other in C.ExpireRetryTimeoutRows(s, rows, id, now, retryDelay).retryAt
    ensures C.ExpireRetryTimeoutRows(s, rows, id, now, retryDelay).retryAt[other] == rows.retryAt[other]
  {
  }

  lemma ExpireLeaseTimeoutRowsConvertsLeaseToRetry(s: C.CoordinationState, rows: C.TimeoutRows, id: C.Id, now: nat, retryDelay: nat)
    requires id in rows.leaseAt
    requires id in s.core.tasks
    requires s.core.tasks[id].state == Core.Acquired
    requires rows.leaseAt[id] <= now
    ensures id in C.ExpireLeaseTimeoutRows(s, rows, id, now, retryDelay).retryAt
    ensures C.ExpireLeaseTimeoutRows(s, rows, id, now, retryDelay).retryAt[id] == now + retryDelay
    ensures id !in C.ExpireLeaseTimeoutRows(s, rows, id, now, retryDelay).leaseAt
  {
  }

  lemma ExpireLeaseTimeoutRowsPreservesOtherRetryTimeout(s: C.CoordinationState, rows: C.TimeoutRows, id: C.Id, other: C.Id, now: nat, retryDelay: nat)
    requires other in rows.retryAt
    requires other != id
    ensures other in C.ExpireLeaseTimeoutRows(s, rows, id, now, retryDelay).retryAt
    ensures C.ExpireLeaseTimeoutRows(s, rows, id, now, retryDelay).retryAt[other] == rows.retryAt[other]
  {
  }

  lemma ExpireLeaseTimeoutRowsPreservesOtherLeaseTimeout(s: C.CoordinationState, rows: C.TimeoutRows, id: C.Id, other: C.Id, now: nat, retryDelay: nat)
    requires other in rows.leaseAt
    requires other != id
    ensures other in C.ExpireLeaseTimeoutRows(s, rows, id, now, retryDelay).leaseAt
    ensures C.ExpireLeaseTimeoutRows(s, rows, id, now, retryDelay).leaseAt[other] == rows.leaseAt[other]
  {
  }

  lemma ApplyPromiseTimeoutsPreservesValidity(s: C.CoordinationState, expired: seq<C.Id>)
    requires C.Valid(s)
    ensures C.Valid(C.ApplyPromiseTimeouts(s, expired))
    decreases |expired|
  {
    if |expired| != 0 {
      ExpirePromiseTimeoutPreservesValidity(s, expired[0]);
      ApplyPromiseTimeoutsPreservesValidity(C.ExpirePromiseTimeout(s, expired[0]), expired[1..]);
    }
  }

  lemma ResumeReadyAwaitersPreservesValidity(s: C.CoordinationState, ready: seq<C.Id>)
    requires C.Valid(s)
    ensures C.Valid(C.ResumeReadyAwaiters(s, ready))
    decreases |ready|
  {
    if |ready| != 0 {
      ResumeReadyAwaiterPreservesValidity(s, ready[0]);
      ResumeReadyAwaitersPreservesValidity(C.ResumeReadyAwaiter(s, ready[0]), ready[1..]);
    }
  }

  lemma ApplyRetryTimeoutsPreservesValidity(s: C.CoordinationState, expired: seq<C.Id>)
    requires C.Valid(s)
    ensures C.Valid(C.ApplyRetryTimeouts(s, expired))
    decreases |expired|
  {
    if |expired| != 0 {
      ExpireRetryTimeoutPreservesValidity(s, expired[0]);
      ApplyRetryTimeoutsPreservesValidity(C.ExpireRetryTimeout(s, expired[0]), expired[1..]);
    }
  }

  lemma ApplyLeaseTimeoutsPreservesValidity(s: C.CoordinationState, expired: seq<C.Id>)
    requires C.Valid(s)
    ensures C.Valid(C.ApplyLeaseTimeouts(s, expired))
    decreases |expired|
  {
    if |expired| != 0 {
      ExpireLeaseTimeoutPreservesValidity(s, expired[0]);
      ApplyLeaseTimeoutsPreservesValidity(C.ExpireLeaseTimeout(s, expired[0]), expired[1..]);
    }
  }

  lemma ApplyPromiseTimeoutRowsPreservesValidity(s: C.CoordinationState, rows: C.TimeoutRows, expired: seq<C.Id>)
    requires C.Valid(s)
    requires C.ValidTimeoutRows(s, rows)
    ensures C.ValidTimeoutRows(C.ApplyPromiseTimeouts(s, expired), C.ApplyPromiseTimeoutRows(s, rows, expired))
    decreases |expired|
  {
    if |expired| != 0 {
      ExpirePromiseTimeoutPreservesValidity(s, expired[0]);
      ExpirePromiseTimeoutRowsPreservesValidity(s, rows, expired[0]);
      ApplyPromiseTimeoutRowsPreservesValidity(C.ExpirePromiseTimeout(s, expired[0]), C.ExpirePromiseTimeoutRows(s, rows, expired[0]), expired[1..]);
    }
  }

  lemma ResumeReadyAwaitersRowsPreservesValidity(s: C.CoordinationState, rows: C.TimeoutRows, ready: seq<C.Id>, now: nat, retryDelay: nat)
    requires C.Valid(s)
    requires C.ValidTimeoutRows(s, rows)
    ensures C.ValidTimeoutRows(C.ResumeReadyAwaiters(s, ready), C.ResumeReadyAwaitersRows(s, rows, ready, now, retryDelay))
    decreases |ready|
  {
    if |ready| != 0 {
      ResumeReadyAwaiterPreservesValidity(s, ready[0]);
      ResumeReadyAwaiterRowsPreservesValidity(s, rows, ready[0], now, retryDelay);
      ResumeReadyAwaitersRowsPreservesValidity(C.ResumeReadyAwaiter(s, ready[0]), C.ResumeReadyAwaiterRows(s, rows, ready[0], now, retryDelay), ready[1..], now, retryDelay);
    }
  }

  lemma ApplyRetryTimeoutRowsPreservesValidity(s: C.CoordinationState, rows: C.TimeoutRows, expired: seq<C.Id>, now: nat, retryDelay: nat)
    requires C.Valid(s)
    requires C.ValidTimeoutRows(s, rows)
    ensures C.ValidTimeoutRows(C.ApplyRetryTimeouts(s, expired), C.ApplyRetryTimeoutRows(s, rows, expired, now, retryDelay))
    decreases |expired|
  {
    if |expired| != 0 {
      ExpireRetryTimeoutPreservesValidity(s, expired[0]);
      ExpireRetryTimeoutRowsPreservesValidity(s, rows, expired[0], now, retryDelay);
      ApplyRetryTimeoutRowsPreservesValidity(C.ExpireRetryTimeout(s, expired[0]), C.ExpireRetryTimeoutRows(s, rows, expired[0], now, retryDelay), expired[1..], now, retryDelay);
    }
  }

  lemma ProcessTimeoutBatchPreservesValidity(s: C.CoordinationState, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, expiredLeases: seq<C.Id>)
    requires C.Valid(s)
    ensures C.Valid(C.ProcessTimeoutBatch(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases))
  {
    ApplyPromiseTimeoutsPreservesValidity(s, expiredPromises);
    var settled := C.ApplyPromiseTimeouts(s, expiredPromises);
    ResumeReadyAwaitersPreservesValidity(settled, readyAwaiters);
    var resumed := C.ResumeReadyAwaiters(settled, readyAwaiters);
    ApplyRetryTimeoutsPreservesValidity(resumed, expiredRetries);
    var retried := C.ApplyRetryTimeouts(resumed, expiredRetries);
    ApplyLeaseTimeoutsPreservesValidity(retried, expiredLeases);
  }

  lemma TimeoutStatement1PreservesValidity(s: C.CoordinationState, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>)
    requires C.Valid(s)
    ensures C.Valid(C.TimeoutStatement1(s, expiredPromises, readyAwaiters))
  {
    ApplyPromiseTimeoutsPreservesValidity(s, expiredPromises);
    ResumeReadyAwaitersPreservesValidity(C.ApplyPromiseTimeouts(s, expiredPromises), readyAwaiters);
  }

  lemma BackendTimeoutStatementsPreservesValidity(s: C.CoordinationState, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, expiredLeases: seq<C.Id>)
    requires C.Valid(s)
    ensures C.Valid(C.BackendTimeoutStatements(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases))
  {
    TimeoutStatement1PreservesValidity(s, expiredPromises, readyAwaiters);
    ApplyRetryTimeoutsPreservesValidity(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries);
    ApplyLeaseTimeoutsPreservesValidity(C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries), expiredLeases);
  }

  lemma TimeoutRowsAfterStatement1PreservesValidity(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, now: nat, retryDelay: nat)
    requires C.Valid(s)
    requires C.ValidTimeoutRows(s, rows)
    ensures C.ValidTimeoutRows(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay))
  {
    ApplyPromiseTimeoutsPreservesValidity(s, expiredPromises);
    ApplyPromiseTimeoutRowsPreservesValidity(s, rows, expiredPromises);
    var settledState := C.ApplyPromiseTimeouts(s, expiredPromises);
    var settledRows := C.ApplyPromiseTimeoutRows(s, rows, expiredPromises);
    ResumeReadyAwaitersPreservesValidity(settledState, readyAwaiters);
    ResumeReadyAwaitersRowsPreservesValidity(settledState, settledRows, readyAwaiters, now, retryDelay);
  }

  lemma TimeoutRowsAfterStatement2PreservesValidity(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, now: nat, retryDelay: nat)
    requires C.Valid(s)
    requires C.ValidTimeoutRows(s, rows)
    ensures C.ValidTimeoutRows(C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries), C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay))
  {
    TimeoutRowsAfterStatement1PreservesValidity(s, rows, expiredPromises, readyAwaiters, now, retryDelay);
    TimeoutStatement1PreservesValidity(s, expiredPromises, readyAwaiters);
    var after1State := C.TimeoutStatement1(s, expiredPromises, readyAwaiters);
    var after1Rows := C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay);
    ApplyRetryTimeoutsPreservesValidity(after1State, expiredRetries);
    ApplyRetryTimeoutRowsPreservesValidity(after1State, after1Rows, expiredRetries, now, retryDelay);
  }

  lemma ProcessTimeoutBatchEqualsBackendTimeoutStatements(s: C.CoordinationState, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, expiredLeases: seq<C.Id>)
    ensures C.ProcessTimeoutBatch(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases) ==
            C.BackendTimeoutStatements(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases)
  {
  }

  lemma ProcessTimeoutBatchEqualsSqliteTimeoutStatements(s: C.CoordinationState, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, expiredLeases: seq<C.Id>)
    ensures C.ProcessTimeoutBatch(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases) ==
            C.SqliteTimeoutStatements(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases)
  {
    ProcessTimeoutBatchEqualsBackendTimeoutStatements(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases);
  }

  lemma ProcessTimeoutBatchEqualsPostgresTimeoutStatements(s: C.CoordinationState, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, expiredLeases: seq<C.Id>)
    ensures C.ProcessTimeoutBatch(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases) ==
            C.PostgresTimeoutStatements(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases)
  {
    ProcessTimeoutBatchEqualsBackendTimeoutStatements(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases);
  }

  lemma TimeoutRowsAfterStatement1EqualsSqliteTimeoutRowsAfterStatement1(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, now: nat, retryDelay: nat)
    ensures C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay) ==
            C.SqliteTimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay)
  {
  }

  lemma TimeoutRowsAfterStatement2EqualsSqliteTimeoutRowsAfterStatement2(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, now: nat, retryDelay: nat)
    ensures C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay) ==
            C.SqliteTimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay)
  {
  }

  lemma TimeoutRowsAfterStatement3EqualsSqliteTimeoutRowsAfterStatement3(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, expiredLeases: seq<C.Id>, now: nat, retryDelay: nat)
    ensures C.TimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, expiredLeases, now, retryDelay) ==
            C.SqliteTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, expiredLeases, now, retryDelay)
  {
  }

  lemma TimeoutRowsAfterStatement1EqualsPostgresTimeoutRowsAfterStatement1(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, now: nat, retryDelay: nat)
    ensures C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay) ==
            C.PostgresTimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay)
  {
    TimeoutRowsAfterStatement1EqualsSqliteTimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay);
  }

  lemma TimeoutRowsAfterStatement2EqualsPostgresTimeoutRowsAfterStatement2(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, now: nat, retryDelay: nat)
    ensures C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay) ==
            C.PostgresTimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay)
  {
    TimeoutRowsAfterStatement2EqualsSqliteTimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay);
  }

  lemma TimeoutRowsAfterStatement3EqualsPostgresTimeoutRowsAfterStatement3(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, expiredLeases: seq<C.Id>, now: nat, retryDelay: nat)
    ensures C.TimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, expiredLeases, now, retryDelay) ==
            C.PostgresTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, expiredLeases, now, retryDelay)
  {
    TimeoutRowsAfterStatement3EqualsSqliteTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, expiredLeases, now, retryDelay);
  }

  lemma SqliteSelectedRetryRowGetsRefreshed(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, id: C.Id, now: nat, retryDelay: nat)
    requires id in C.SqliteRetryTimeoutQuery(
      C.TimeoutStatement1(s, expiredPromises, readyAwaiters),
      C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay),
      now)
    ensures id in C.SqliteTimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, [id], now, retryDelay).retryAt
    ensures C.SqliteTimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, [id], now, retryDelay).retryAt[id] == now + retryDelay
  {
    var after1State := C.TimeoutStatement1(s, expiredPromises, readyAwaiters);
    var after1Rows := C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay);
    SqliteRetryTimeoutQueryMatchesTimeoutRows(after1State, after1Rows, now);
    ExpireRetryTimeoutRowsSetsSelectedRetryTimeout(after1State, after1Rows, id, now, retryDelay);
    ApplyRetryTimeoutRowsSingleton(after1State, after1Rows, id, now, retryDelay);
  }

  lemma SqliteFutureRetryRowPreserved(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, selected: C.Id, future: C.Id, now: nat, retryDelay: nat)
    requires future in C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay).retryAt
    requires future != selected
    requires future !in C.SqliteRetryTimeoutQuery(
      C.TimeoutStatement1(s, expiredPromises, readyAwaiters),
      C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay),
      now)
    ensures future in C.SqliteTimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, [selected], now, retryDelay).retryAt
    ensures C.SqliteTimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, [selected], now, retryDelay).retryAt[future] ==
            C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay).retryAt[future]
  {
    var after1State := C.TimeoutStatement1(s, expiredPromises, readyAwaiters);
    var after1Rows := C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay);
    ExpireRetryTimeoutRowsPreservesOtherRetryTimeout(after1State, after1Rows, selected, future, now, retryDelay);
    ApplyRetryTimeoutRowsSingleton(after1State, after1Rows, selected, now, retryDelay);
  }

  lemma SqliteSelectedLeaseRowConvertsToRetry(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, id: C.Id, now: nat, retryDelay: nat)
    requires id in C.SqliteLeaseTimeoutQuery(
      C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries),
      C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay),
      now)
    ensures id in C.SqliteTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, [id], now, retryDelay).retryAt
    ensures C.SqliteTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, [id], now, retryDelay).retryAt[id] == now + retryDelay
    ensures id !in C.SqliteTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, [id], now, retryDelay).leaseAt
  {
    var after2State := C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries);
    var after2Rows := C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay);
    SqliteLeaseTimeoutQueryMatchesTimeoutRows(after2State, after2Rows, now);
    ExpireLeaseTimeoutRowsConvertsLeaseToRetry(after2State, after2Rows, id, now, retryDelay);
    ApplyLeaseTimeoutRowsSingleton(after2State, after2Rows, id, now, retryDelay);
  }

  lemma SqliteFutureLeaseRowPreserved(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, selected: C.Id, future: C.Id, now: nat, retryDelay: nat)
    requires future in C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay).leaseAt
    requires future != selected
    requires future !in C.SqliteLeaseTimeoutQuery(
      C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries),
      C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay),
      now)
    ensures future in C.SqliteTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, [selected], now, retryDelay).leaseAt
    ensures C.SqliteTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, [selected], now, retryDelay).leaseAt[future] ==
            C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay).leaseAt[future]
  {
    var after2State := C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries);
    var after2Rows := C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay);
    ExpireLeaseTimeoutRowsPreservesOtherLeaseTimeout(after2State, after2Rows, selected, future, now, retryDelay);
    ApplyLeaseTimeoutRowsSingleton(after2State, after2Rows, selected, now, retryDelay);
  }

  lemma PostgresSelectedRetryRowGetsRefreshed(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, id: C.Id, now: nat, retryDelay: nat)
    requires id in C.PostgresRetryTimeoutQuery(
      C.TimeoutStatement1(s, expiredPromises, readyAwaiters),
      C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay),
      now)
    ensures id in C.PostgresTimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, [id], now, retryDelay).retryAt
    ensures C.PostgresTimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, [id], now, retryDelay).retryAt[id] == now + retryDelay
  {
    PostgresRetryTimeoutQueryMatchesTimeoutRows(
      C.TimeoutStatement1(s, expiredPromises, readyAwaiters),
      C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay),
      now);
    SqliteSelectedRetryRowGetsRefreshed(s, rows, expiredPromises, readyAwaiters, id, now, retryDelay);
    TimeoutRowsAfterStatement2EqualsPostgresTimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, [id], now, retryDelay);
  }

  lemma PostgresFutureRetryRowPreserved(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, selected: C.Id, future: C.Id, now: nat, retryDelay: nat)
    requires future in C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay).retryAt
    requires future != selected
    requires future !in C.PostgresRetryTimeoutQuery(
      C.TimeoutStatement1(s, expiredPromises, readyAwaiters),
      C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay),
      now)
    ensures future in C.PostgresTimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, [selected], now, retryDelay).retryAt
    ensures C.PostgresTimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, [selected], now, retryDelay).retryAt[future] ==
            C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay).retryAt[future]
  {
    PostgresRetryTimeoutQueryMatchesTimeoutRows(
      C.TimeoutStatement1(s, expiredPromises, readyAwaiters),
      C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay),
      now);
    SqliteFutureRetryRowPreserved(s, rows, expiredPromises, readyAwaiters, selected, future, now, retryDelay);
    TimeoutRowsAfterStatement2EqualsPostgresTimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, [selected], now, retryDelay);
  }

  lemma PostgresSelectedLeaseRowConvertsToRetry(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, id: C.Id, now: nat, retryDelay: nat)
    requires id in C.PostgresLeaseTimeoutQuery(
      C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries),
      C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay),
      now)
    ensures id in C.PostgresTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, [id], now, retryDelay).retryAt
    ensures C.PostgresTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, [id], now, retryDelay).retryAt[id] == now + retryDelay
    ensures id !in C.PostgresTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, [id], now, retryDelay).leaseAt
  {
    PostgresLeaseTimeoutQueryMatchesTimeoutRows(
      C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries),
      C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay),
      now);
    SqliteSelectedLeaseRowConvertsToRetry(s, rows, expiredPromises, readyAwaiters, expiredRetries, id, now, retryDelay);
    TimeoutRowsAfterStatement3EqualsPostgresTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, [id], now, retryDelay);
  }

  lemma PostgresFutureLeaseRowPreserved(s: C.CoordinationState, rows: C.TimeoutRows, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, selected: C.Id, future: C.Id, now: nat, retryDelay: nat)
    requires future in C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay).leaseAt
    requires future != selected
    requires future !in C.PostgresLeaseTimeoutQuery(
      C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries),
      C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay),
      now)
    ensures future in C.PostgresTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, [selected], now, retryDelay).leaseAt
    ensures C.PostgresTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, [selected], now, retryDelay).leaseAt[future] ==
            C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay).leaseAt[future]
  {
    PostgresLeaseTimeoutQueryMatchesTimeoutRows(
      C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries),
      C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay),
      now);
    SqliteFutureLeaseRowPreserved(s, rows, expiredPromises, readyAwaiters, expiredRetries, selected, future, now, retryDelay);
    TimeoutRowsAfterStatement3EqualsPostgresTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, [selected], now, retryDelay);
  }

  lemma ApplyPromiseTimeoutsSingleton(s: C.CoordinationState, id: C.Id)
    ensures C.ApplyPromiseTimeouts(s, [id]) == C.ExpirePromiseTimeout(s, id)
  {
    assert [id][0] == id;
    assert [id][1..] == [];
  }

  lemma ResumeReadyAwaitersSingleton(s: C.CoordinationState, awaiter: C.Id)
    ensures C.ResumeReadyAwaiters(s, [awaiter]) == C.ResumeReadyAwaiter(s, awaiter)
  {
    assert [awaiter][0] == awaiter;
    assert [awaiter][1..] == [];
  }

  lemma ApplyRetryTimeoutsSingleton(s: C.CoordinationState, id: C.Id)
    ensures C.ApplyRetryTimeouts(s, [id]) == C.ExpireRetryTimeout(s, id)
  {
    assert [id][0] == id;
    assert [id][1..] == [];
  }

  lemma ApplyLeaseTimeoutsSingleton(s: C.CoordinationState, id: C.Id)
    ensures C.ApplyLeaseTimeouts(s, [id]) == C.ExpireLeaseTimeout(s, id)
  {
    assert [id][0] == id;
    assert [id][1..] == [];
  }

  lemma ApplyRetryTimeoutRowsSingleton(s: C.CoordinationState, rows: C.TimeoutRows, id: C.Id, now: nat, retryDelay: nat)
    ensures C.ApplyRetryTimeoutRows(s, rows, [id], now, retryDelay) == C.ExpireRetryTimeoutRows(s, rows, id, now, retryDelay)
  {
    assert [id][0] == id;
    assert [id][1..] == [];
  }

  lemma ApplyLeaseTimeoutRowsSingleton(s: C.CoordinationState, rows: C.TimeoutRows, id: C.Id, now: nat, retryDelay: nat)
    ensures C.ApplyLeaseTimeoutRows(s, rows, [id], now, retryDelay) == C.ExpireLeaseTimeoutRows(s, rows, id, now, retryDelay)
  {
    assert [id][0] == id;
    assert [id][1..] == [];
  }

  lemma ApplyRetryTimeoutsAppendSingleton(s: C.CoordinationState, prefix: seq<C.Id>, last: C.Id)
    ensures C.ApplyRetryTimeouts(s, prefix + [last]) == C.ApplyRetryTimeouts(C.ApplyRetryTimeouts(s, prefix), [last])
    decreases |prefix|
  {
    if |prefix| != 0 {
      assert prefix + [last] == [prefix[0]] + (prefix[1..] + [last]);
      ApplyRetryTimeoutsAppendSingleton(C.ExpireRetryTimeout(s, prefix[0]), prefix[1..], last);
    }
  }

  lemma ApplyLeaseTimeoutsAppendSingleton(s: C.CoordinationState, prefix: seq<C.Id>, last: C.Id)
    ensures C.ApplyLeaseTimeouts(s, prefix + [last]) == C.ApplyLeaseTimeouts(C.ApplyLeaseTimeouts(s, prefix), [last])
    decreases |prefix|
  {
    if |prefix| != 0 {
      assert prefix + [last] == [prefix[0]] + (prefix[1..] + [last]);
      ApplyLeaseTimeoutsAppendSingleton(C.ExpireLeaseTimeout(s, prefix[0]), prefix[1..], last);
    }
  }

  lemma ApplyPromiseTimeoutsAppendSingleton(s: C.CoordinationState, prefix: seq<C.Id>, last: C.Id)
    ensures C.ApplyPromiseTimeouts(s, prefix + [last]) == C.ApplyPromiseTimeouts(C.ApplyPromiseTimeouts(s, prefix), [last])
    decreases |prefix|
  {
    if |prefix| != 0 {
      assert prefix + [last] == [prefix[0]] + (prefix[1..] + [last]);
      ApplyPromiseTimeoutsAppendSingleton(C.ExpirePromiseTimeout(s, prefix[0]), prefix[1..], last);
    }
  }

  lemma ResumeReadyAwaitersAppendSingleton(s: C.CoordinationState, prefix: seq<C.Id>, last: C.Id)
    ensures C.ResumeReadyAwaiters(s, prefix + [last]) == C.ResumeReadyAwaiters(C.ResumeReadyAwaiters(s, prefix), [last])
    decreases |prefix|
  {
    if |prefix| != 0 {
      assert prefix + [last] == [prefix[0]] + (prefix[1..] + [last]);
      ResumeReadyAwaitersAppendSingleton(C.ResumeReadyAwaiter(s, prefix[0]), prefix[1..], last);
    }
  }

  predicate PromiseTimeoutIndependent(s: C.CoordinationState, a: C.Id, b: C.Id) {
    a != b &&
    (forall cb: C.CallbackKey :: cb in s.callbacks ==> cb.awaited != a && cb.awaited != b && cb.awaiter != a && cb.awaiter != b) &&
    (forall listener: C.ListenerKey :: listener in s.listeners ==> listener.promise != a && listener.promise != b)
  }

  predicate PromiseTimeoutBatchIndependent(s: C.CoordinationState, xs: seq<C.Id>) {
    DistinctIds(xs) &&
    (forall i: nat :: i < |xs| ==> xs[i] in s.core.promises && s.core.promises[xs[i]].state == Core.Pending) &&
    (forall cb: C.CallbackKey :: cb in s.callbacks ==> cb.awaited !in xs && cb.awaiter !in xs) &&
    (forall listener: C.ListenerKey :: listener in s.listeners ==> listener.promise !in xs)
  }

  lemma DistinctIdsElementsDistinct(xs: seq<C.Id>, i: nat, j: nat)
    requires DistinctIds(xs)
    requires i < j < |xs|
    ensures xs[i] != xs[j]
    decreases |xs|
  {
    if i == 0 {
      assert xs[j] in xs[1..];
    } else {
      DistinctIdsTail(xs[0], xs[1..]);
      DistinctIdsElementsDistinct(xs[1..], i - 1, j - 1);
    }
  }

  lemma PromiseTimeoutBatchIndependentMemberPending(s: C.CoordinationState, xs: seq<C.Id>, id: C.Id)
    requires PromiseTimeoutBatchIndependent(s, xs)
    requires id in multiset(xs)
    ensures id in s.core.promises
    ensures s.core.promises[id].state == Core.Pending
  {
    SeqMemberHasIndex(xs, id);
    var i :| 0 <= i < |xs| && xs[i] == id;
  }

  lemma NotInSequencePreservedByPermutation(xs: seq<C.Id>, ys: seq<C.Id>, x: C.Id)
    requires multiset(xs) == multiset(ys)
    requires x !in xs
    ensures x !in ys
  {
    if x in ys {
      assert x in multiset(ys);
      assert x in multiset(xs);
      SeqMemberHasIndex(xs, x);
    }
  }

  lemma PromiseTimeoutBatchIndependentPermutation(s: C.CoordinationState, xs: seq<C.Id>, ys: seq<C.Id>)
    requires PromiseTimeoutBatchIndependent(s, xs)
    requires DistinctIds(ys)
    requires multiset(xs) == multiset(ys)
    ensures PromiseTimeoutBatchIndependent(s, ys)
  {
    forall i: nat | i < |ys|
      ensures ys[i] in s.core.promises && s.core.promises[ys[i]].state == Core.Pending
    {
      assert ys[i] in multiset(ys);
      assert ys[i] in multiset(xs);
      PromiseTimeoutBatchIndependentMemberPending(s, xs, ys[i]);
    }
    forall cb: C.CallbackKey | cb in s.callbacks
      ensures cb.awaited !in ys
    {
      NotInSequencePreservedByPermutation(xs, ys, cb.awaited);
    }
    forall cb: C.CallbackKey | cb in s.callbacks
      ensures cb.awaiter !in ys
    {
      NotInSequencePreservedByPermutation(xs, ys, cb.awaiter);
    }
    forall listener: C.ListenerKey | listener in s.listeners
      ensures listener.promise !in ys
    {
      NotInSequencePreservedByPermutation(xs, ys, listener.promise);
    }
  }

  lemma PromiseTimeoutBatchIndependentTail(s: C.CoordinationState, head: C.Id, tail: seq<C.Id>)
    requires PromiseTimeoutBatchIndependent(s, [head] + tail)
    ensures PromiseTimeoutBatchIndependent(s, tail)
    ensures head in s.core.promises
    ensures s.core.promises[head].state == Core.Pending
    ensures head !in tail
  {
    DistinctIdsTail(head, tail);
  }

  lemma PromiseTimeoutBatchIndependentPair(s: C.CoordinationState, xs: seq<C.Id>, i: nat, j: nat)
    requires PromiseTimeoutBatchIndependent(s, xs)
    requires i < j < |xs|
    ensures PromiseTimeoutIndependent(s, xs[i], xs[j])
  {
    DistinctIdsElementsDistinct(xs, i, j);
  }

  lemma PromiseTimeoutBatchIndependentAfterExpire(s: C.CoordinationState, head: C.Id, tail: seq<C.Id>)
    requires PromiseTimeoutBatchIndependent(s, [head] + tail)
    ensures PromiseTimeoutBatchIndependent(C.ExpirePromiseTimeout(s, head), tail)
  {
    PromiseTimeoutBatchIndependentTail(s, head, tail);
    forall i: nat | i < |tail|
      ensures tail[i] in C.ExpirePromiseTimeout(s, head).core.promises
    {
      assert head != tail[i];
    }
    forall i: nat | i < |tail|
      ensures C.ExpirePromiseTimeout(s, head).core.promises[tail[i]].state == Core.Pending
    {
      assert head != tail[i];
    }
  }

  lemma ResumeReadyAwaiterCommutesDistinct(s: C.CoordinationState, a: C.Id, b: C.Id)
    requires a != b
    ensures C.ResumeReadyAwaiter(C.ResumeReadyAwaiter(s, a), b) == C.ResumeReadyAwaiter(C.ResumeReadyAwaiter(s, b), a)
  {
  }

  lemma ExpireRetryTimeoutCommutesDistinct(s: C.CoordinationState, a: C.Id, b: C.Id)
    requires a != b
    ensures C.ExpireRetryTimeout(C.ExpireRetryTimeout(s, a), b) == C.ExpireRetryTimeout(C.ExpireRetryTimeout(s, b), a)
  {
  }

  lemma ExpireLeaseTimeoutCommutesDistinct(s: C.CoordinationState, a: C.Id, b: C.Id)
    requires a != b
    ensures C.ExpireLeaseTimeout(C.ExpireLeaseTimeout(s, a), b) == C.ExpireLeaseTimeout(C.ExpireLeaseTimeout(s, b), a)
  {
  }

  lemma ExpirePromiseTimeoutCommutesIndependent(s: C.CoordinationState, a: C.Id, b: C.Id)
    requires PromiseTimeoutIndependent(s, a, b)
    requires a in s.core.promises
    requires b in s.core.promises
    requires s.core.promises[a].state == Core.Pending
    requires s.core.promises[b].state == Core.Pending
    ensures C.ExpirePromiseTimeout(C.ExpirePromiseTimeout(s, a), b) == C.ExpirePromiseTimeout(C.ExpirePromiseTimeout(s, b), a)
  {
  }

  lemma ResumeReadyAwaitersPairSwap(s: C.CoordinationState, a: C.Id, b: C.Id)
    requires a != b
    ensures C.ResumeReadyAwaiters(s, [a, b]) == C.ResumeReadyAwaiters(s, [b, a])
  {
    ResumeReadyAwaitersSingleton(C.ResumeReadyAwaiter(s, a), b);
    ResumeReadyAwaitersSingleton(C.ResumeReadyAwaiter(s, b), a);
    ResumeReadyAwaiterCommutesDistinct(s, a, b);
  }

  lemma ApplyRetryTimeoutsPairSwap(s: C.CoordinationState, a: C.Id, b: C.Id)
    requires a != b
    ensures C.ApplyRetryTimeouts(s, [a, b]) == C.ApplyRetryTimeouts(s, [b, a])
  {
    ApplyRetryTimeoutsSingleton(C.ExpireRetryTimeout(s, a), b);
    ApplyRetryTimeoutsSingleton(C.ExpireRetryTimeout(s, b), a);
    ExpireRetryTimeoutCommutesDistinct(s, a, b);
  }

  lemma ApplyLeaseTimeoutsPairSwap(s: C.CoordinationState, a: C.Id, b: C.Id)
    requires a != b
    ensures C.ApplyLeaseTimeouts(s, [a, b]) == C.ApplyLeaseTimeouts(s, [b, a])
  {
    ApplyLeaseTimeoutsSingleton(C.ExpireLeaseTimeout(s, a), b);
    ApplyLeaseTimeoutsSingleton(C.ExpireLeaseTimeout(s, b), a);
    ExpireLeaseTimeoutCommutesDistinct(s, a, b);
  }

  lemma ApplyPromiseTimeoutsPairSwapIndependent(s: C.CoordinationState, a: C.Id, b: C.Id)
    requires PromiseTimeoutIndependent(s, a, b)
    requires a in s.core.promises
    requires b in s.core.promises
    requires s.core.promises[a].state == Core.Pending
    requires s.core.promises[b].state == Core.Pending
    ensures C.ApplyPromiseTimeouts(s, [a, b]) == C.ApplyPromiseTimeouts(s, [b, a])
  {
    ApplyPromiseTimeoutsSingleton(C.ExpirePromiseTimeout(s, a), b);
    ApplyPromiseTimeoutsSingleton(C.ExpirePromiseTimeout(s, b), a);
    ExpirePromiseTimeoutCommutesIndependent(s, a, b);
  }

  lemma ApplyPromiseTimeoutsMoveHeadToTailIndependent(s: C.CoordinationState, head: C.Id, tail: seq<C.Id>)
    requires PromiseTimeoutBatchIndependent(s, [head] + tail)
    ensures C.ApplyPromiseTimeouts(s, [head] + tail) == C.ApplyPromiseTimeouts(s, tail + [head])
    decreases |tail|
  {
    if |tail| != 0 {
      var next := tail[0];
      var rest := tail[1..];
      PromiseTimeoutBatchIndependentTail(s, head, tail);
      PromiseTimeoutBatchIndependentPair(s, [head] + tail, 0, 1);
      assert tail == [next] + rest;
      ApplyPromiseTimeoutsPairSwapIndependent(s, head, next);
      PromiseTimeoutBatchIndependentAfterExpire(s, next, [head] + rest);
      ApplyPromiseTimeoutsMoveHeadToTailIndependent(C.ExpirePromiseTimeout(s, next), head, rest);
      ApplyPromiseTimeoutsAppendSingleton(C.ExpirePromiseTimeout(s, next), rest, head);
      assert tail + [head] == [next] + (rest + [head]);
      calc {
        C.ApplyPromiseTimeouts(s, [head] + tail);
        == { }
        C.ApplyPromiseTimeouts(C.ExpirePromiseTimeout(s, head), tail);
        == { }
        C.ApplyPromiseTimeouts(C.ExpirePromiseTimeout(C.ExpirePromiseTimeout(s, head), next), rest);
        == { ExpirePromiseTimeoutCommutesIndependent(s, head, next); }
        C.ApplyPromiseTimeouts(C.ExpirePromiseTimeout(C.ExpirePromiseTimeout(s, next), head), rest);
        == { }
        C.ApplyPromiseTimeouts(C.ExpirePromiseTimeout(s, next), [head] + rest);
        == { ApplyPromiseTimeoutsMoveHeadToTailIndependent(C.ExpirePromiseTimeout(s, next), head, rest); }
        C.ApplyPromiseTimeouts(C.ExpirePromiseTimeout(s, next), rest + [head]);
        == { ApplyPromiseTimeoutsAppendSingleton(C.ExpirePromiseTimeout(s, next), rest, head); }
        C.ApplyPromiseTimeouts(C.ApplyPromiseTimeouts(C.ExpirePromiseTimeout(s, next), rest), [head]);
        == { ApplyPromiseTimeoutsSingleton(C.ApplyPromiseTimeouts(C.ExpirePromiseTimeout(s, next), rest), head); }
        C.ExpirePromiseTimeout(C.ApplyPromiseTimeouts(C.ExpirePromiseTimeout(s, next), rest), head);
        == { }
        C.ApplyPromiseTimeouts(s, tail + [head]);
      }
    }
  }

  lemma ResumeReadyAwaitersMoveHeadToTail(s: C.CoordinationState, head: C.Id, tail: seq<C.Id>)
    requires DistinctIds([head] + tail)
    ensures C.ResumeReadyAwaiters(s, [head] + tail) == C.ResumeReadyAwaiters(s, tail + [head])
    decreases |tail|
  {
    if |tail| != 0 {
      var next := tail[0];
      var rest := tail[1..];
      DistinctIdsTail(head, tail);
      assert tail == [next] + rest;
      ResumeReadyAwaitersPairSwap(s, head, next);
      ResumeReadyAwaitersMoveHeadToTail(C.ResumeReadyAwaiter(s, next), head, rest);
      ResumeReadyAwaitersAppendSingleton(C.ResumeReadyAwaiter(s, next), rest, head);
      assert tail + [head] == [next] + (rest + [head]);
      calc {
        C.ResumeReadyAwaiters(s, [head] + tail);
        == { }
        C.ResumeReadyAwaiters(C.ResumeReadyAwaiter(s, head), tail);
        == { }
        C.ResumeReadyAwaiters(C.ResumeReadyAwaiter(C.ResumeReadyAwaiter(s, head), next), rest);
        == { ResumeReadyAwaiterCommutesDistinct(s, head, next); }
        C.ResumeReadyAwaiters(C.ResumeReadyAwaiter(C.ResumeReadyAwaiter(s, next), head), rest);
        == { }
        C.ResumeReadyAwaiters(C.ResumeReadyAwaiter(s, next), [head] + rest);
        == { ResumeReadyAwaitersMoveHeadToTail(C.ResumeReadyAwaiter(s, next), head, rest); }
        C.ResumeReadyAwaiters(C.ResumeReadyAwaiter(s, next), rest + [head]);
        == { ResumeReadyAwaitersAppendSingleton(C.ResumeReadyAwaiter(s, next), rest, head); }
        C.ResumeReadyAwaiters(C.ResumeReadyAwaiters(C.ResumeReadyAwaiter(s, next), rest), [head]);
        == { ResumeReadyAwaitersSingleton(C.ResumeReadyAwaiters(C.ResumeReadyAwaiter(s, next), rest), head); }
        C.ResumeReadyAwaiter(C.ResumeReadyAwaiters(C.ResumeReadyAwaiter(s, next), rest), head);
        == { }
        C.ResumeReadyAwaiters(s, tail + [head]);
      }
    }
  }

  lemma ApplyRetryTimeoutsMoveHeadToTail(s: C.CoordinationState, head: C.Id, tail: seq<C.Id>)
    requires DistinctIds([head] + tail)
    ensures C.ApplyRetryTimeouts(s, [head] + tail) == C.ApplyRetryTimeouts(s, tail + [head])
    decreases |tail|
  {
    if |tail| != 0 {
      var next := tail[0];
      var rest := tail[1..];
      DistinctIdsTail(head, tail);
      assert tail == [next] + rest;
      ApplyRetryTimeoutsPairSwap(s, head, next);
      ApplyRetryTimeoutsMoveHeadToTail(C.ExpireRetryTimeout(s, next), head, rest);
      ApplyRetryTimeoutsAppendSingleton(C.ExpireRetryTimeout(s, next), rest, head);
      assert tail + [head] == [next] + (rest + [head]);
      calc {
        C.ApplyRetryTimeouts(s, [head] + tail);
        == { }
        C.ApplyRetryTimeouts(C.ExpireRetryTimeout(s, head), tail);
        == { }
        C.ApplyRetryTimeouts(C.ExpireRetryTimeout(C.ExpireRetryTimeout(s, head), next), rest);
        == { ExpireRetryTimeoutCommutesDistinct(s, head, next); }
        C.ApplyRetryTimeouts(C.ExpireRetryTimeout(C.ExpireRetryTimeout(s, next), head), rest);
        == { }
        C.ApplyRetryTimeouts(C.ExpireRetryTimeout(s, next), [head] + rest);
        == { ApplyRetryTimeoutsMoveHeadToTail(C.ExpireRetryTimeout(s, next), head, rest); }
        C.ApplyRetryTimeouts(C.ExpireRetryTimeout(s, next), rest + [head]);
        == { ApplyRetryTimeoutsAppendSingleton(C.ExpireRetryTimeout(s, next), rest, head); }
        C.ApplyRetryTimeouts(C.ApplyRetryTimeouts(C.ExpireRetryTimeout(s, next), rest), [head]);
        == { ApplyRetryTimeoutsSingleton(C.ApplyRetryTimeouts(C.ExpireRetryTimeout(s, next), rest), head); }
        C.ExpireRetryTimeout(C.ApplyRetryTimeouts(C.ExpireRetryTimeout(s, next), rest), head);
        == { }
        C.ApplyRetryTimeouts(s, tail + [head]);
      }
    }
  }

  lemma ApplyLeaseTimeoutsMoveHeadToTail(s: C.CoordinationState, head: C.Id, tail: seq<C.Id>)
    requires DistinctIds([head] + tail)
    ensures C.ApplyLeaseTimeouts(s, [head] + tail) == C.ApplyLeaseTimeouts(s, tail + [head])
    decreases |tail|
  {
    if |tail| != 0 {
      var next := tail[0];
      var rest := tail[1..];
      DistinctIdsTail(head, tail);
      assert tail == [next] + rest;
      ApplyLeaseTimeoutsPairSwap(s, head, next);
      ApplyLeaseTimeoutsMoveHeadToTail(C.ExpireLeaseTimeout(s, next), head, rest);
      ApplyLeaseTimeoutsAppendSingleton(C.ExpireLeaseTimeout(s, next), rest, head);
      assert tail + [head] == [next] + (rest + [head]);
      calc {
        C.ApplyLeaseTimeouts(s, [head] + tail);
        == { }
        C.ApplyLeaseTimeouts(C.ExpireLeaseTimeout(s, head), tail);
        == { }
        C.ApplyLeaseTimeouts(C.ExpireLeaseTimeout(C.ExpireLeaseTimeout(s, head), next), rest);
        == { ExpireLeaseTimeoutCommutesDistinct(s, head, next); }
        C.ApplyLeaseTimeouts(C.ExpireLeaseTimeout(C.ExpireLeaseTimeout(s, next), head), rest);
        == { }
        C.ApplyLeaseTimeouts(C.ExpireLeaseTimeout(s, next), [head] + rest);
        == { ApplyLeaseTimeoutsMoveHeadToTail(C.ExpireLeaseTimeout(s, next), head, rest); }
        C.ApplyLeaseTimeouts(C.ExpireLeaseTimeout(s, next), rest + [head]);
        == { ApplyLeaseTimeoutsAppendSingleton(C.ExpireLeaseTimeout(s, next), rest, head); }
        C.ApplyLeaseTimeouts(C.ApplyLeaseTimeouts(C.ExpireLeaseTimeout(s, next), rest), [head]);
        == { ApplyLeaseTimeoutsSingleton(C.ApplyLeaseTimeouts(C.ExpireLeaseTimeout(s, next), rest), head); }
        C.ExpireLeaseTimeout(C.ApplyLeaseTimeouts(C.ExpireLeaseTimeout(s, next), rest), head);
        == { }
        C.ApplyLeaseTimeouts(s, tail + [head]);
      }
    }
  }

  lemma DistinctIdsMoveHeadToTail(head: C.Id, tail: seq<C.Id>)
    requires DistinctIds([head] + tail)
    ensures DistinctIds(tail + [head])
    decreases |tail|
  {
    if |tail| != 0 {
      var next := tail[0];
      var rest := tail[1..];
      DistinctIdsTail(head, tail);
      DistinctIdsMoveHeadToTail(head, rest);
      assert tail + [head] == [next] + (rest + [head]);
    }
  }

  lemma DistinctIdsRotateBlocks(prefix: seq<C.Id>, suffix: seq<C.Id>)
    requires DistinctIds(prefix + suffix)
    ensures DistinctIds(suffix + prefix)
    decreases |prefix|
  {
    if |prefix| != 0 {
      var head := prefix[0];
      var rest := prefix[1..];
      assert prefix + suffix == [head] + (rest + suffix);
      DistinctIdsMoveHeadToTail(head, rest + suffix);
      assert (rest + suffix) + [head] == rest + (suffix + [head]);
      DistinctIdsRotateBlocks(rest, suffix + [head]);
      assert suffix + prefix == (suffix + [head]) + rest;
    } else {
      assert prefix == [];
      assert prefix + suffix == suffix + prefix;
    }
  }

  lemma ApplyPromiseTimeoutsRotateBlocksIndependent(s: C.CoordinationState, prefix: seq<C.Id>, suffix: seq<C.Id>)
    requires PromiseTimeoutBatchIndependent(s, prefix + suffix)
    ensures C.ApplyPromiseTimeouts(s, prefix + suffix) == C.ApplyPromiseTimeouts(s, suffix + prefix)
    decreases |prefix|
  {
    if |prefix| != 0 {
      var head := prefix[0];
      var rest := prefix[1..];
      assert prefix + suffix == [head] + (rest + suffix);
      ApplyPromiseTimeoutsMoveHeadToTailIndependent(s, head, rest + suffix);
      PromiseTimeoutBatchIndependentTail(s, head, rest + suffix);
      DistinctIdsMoveHeadToTail(head, rest + suffix);
      PromiseTimeoutBatchIndependentPermutation(s, prefix + suffix, (rest + suffix) + [head]);
      assert rest + (suffix + [head]) == (rest + suffix) + [head];
      ApplyPromiseTimeoutsRotateBlocksIndependent(s, rest, suffix + [head]);
      assert suffix + prefix == (suffix + [head]) + rest;
      assert C.ApplyPromiseTimeouts(s, prefix + suffix) == C.ApplyPromiseTimeouts(s, [head] + (rest + suffix));
      assert C.ApplyPromiseTimeouts(s, [head] + (rest + suffix)) == C.ApplyPromiseTimeouts(s, (rest + suffix) + [head]);
      assert C.ApplyPromiseTimeouts(s, (rest + suffix) + [head]) == C.ApplyPromiseTimeouts(s, rest + (suffix + [head]));
      assert C.ApplyPromiseTimeouts(s, rest + (suffix + [head])) == C.ApplyPromiseTimeouts(s, (suffix + [head]) + rest);
      assert C.ApplyPromiseTimeouts(s, (suffix + [head]) + rest) == C.ApplyPromiseTimeouts(s, suffix + prefix);
      assert C.ApplyPromiseTimeouts(s, prefix + suffix) == C.ApplyPromiseTimeouts(s, suffix + prefix);
    } else {
      assert prefix == [];
      assert prefix + suffix == suffix + prefix;
    }
  }

  lemma ResumeReadyAwaitersRotateBlocks(s: C.CoordinationState, prefix: seq<C.Id>, suffix: seq<C.Id>)
    requires DistinctIds(prefix + suffix)
    ensures C.ResumeReadyAwaiters(s, prefix + suffix) == C.ResumeReadyAwaiters(s, suffix + prefix)
    decreases |prefix|
  {
    if |prefix| != 0 {
      var head := prefix[0];
      var rest := prefix[1..];
      assert prefix + suffix == [head] + (rest + suffix);
      ResumeReadyAwaitersMoveHeadToTail(s, head, rest + suffix);
      DistinctIdsMoveHeadToTail(head, rest + suffix);
      assert rest + (suffix + [head]) == (rest + suffix) + [head];
      ResumeReadyAwaitersRotateBlocks(s, rest, suffix + [head]);
      assert suffix + prefix == (suffix + [head]) + rest;
      assert C.ResumeReadyAwaiters(s, prefix + suffix) == C.ResumeReadyAwaiters(s, [head] + (rest + suffix));
      assert C.ResumeReadyAwaiters(s, [head] + (rest + suffix)) == C.ResumeReadyAwaiters(s, (rest + suffix) + [head]);
      assert C.ResumeReadyAwaiters(s, (rest + suffix) + [head]) == C.ResumeReadyAwaiters(s, rest + (suffix + [head]));
      assert C.ResumeReadyAwaiters(s, rest + (suffix + [head])) == C.ResumeReadyAwaiters(s, (suffix + [head]) + rest);
      assert C.ResumeReadyAwaiters(s, (suffix + [head]) + rest) == C.ResumeReadyAwaiters(s, suffix + prefix);
      assert C.ResumeReadyAwaiters(s, prefix + suffix) == C.ResumeReadyAwaiters(s, suffix + prefix);
    } else {
      assert prefix == [];
      assert prefix + suffix == suffix + prefix;
    }
  }

  lemma SeqMemberHasIndex(xs: seq<C.Id>, x: C.Id)
    requires x in multiset(xs)
    ensures exists i: nat :: i < |xs| && xs[i] == x
    decreases |xs|
  {
    if |xs| != 0 {
      if xs[0] == x {
      } else {
        assert x in multiset(xs[1..]);
        SeqMemberHasIndex(xs[1..], x);
      }
    }
  }

  lemma ApplyRetryTimeoutsRotateBlocks(s: C.CoordinationState, prefix: seq<C.Id>, suffix: seq<C.Id>)
    requires DistinctIds(prefix + suffix)
    ensures C.ApplyRetryTimeouts(s, prefix + suffix) == C.ApplyRetryTimeouts(s, suffix + prefix)
    decreases |prefix|
  {
    if |prefix| != 0 {
      var head := prefix[0];
      var rest := prefix[1..];
      assert prefix + suffix == [head] + (rest + suffix);
      ApplyRetryTimeoutsMoveHeadToTail(s, head, rest + suffix);
      DistinctIdsMoveHeadToTail(head, rest + suffix);
      assert rest + (suffix + [head]) == (rest + suffix) + [head];
      ApplyRetryTimeoutsRotateBlocks(s, rest, suffix + [head]);
      assert suffix + prefix == (suffix + [head]) + rest;
      assert C.ApplyRetryTimeouts(s, prefix + suffix) == C.ApplyRetryTimeouts(s, [head] + (rest + suffix));
      assert C.ApplyRetryTimeouts(s, [head] + (rest + suffix)) == C.ApplyRetryTimeouts(s, (rest + suffix) + [head]);
      assert C.ApplyRetryTimeouts(s, (rest + suffix) + [head]) == C.ApplyRetryTimeouts(s, rest + (suffix + [head]));
      assert C.ApplyRetryTimeouts(s, rest + (suffix + [head])) == C.ApplyRetryTimeouts(s, (suffix + [head]) + rest);
      assert C.ApplyRetryTimeouts(s, (suffix + [head]) + rest) == C.ApplyRetryTimeouts(s, suffix + prefix);
      assert C.ApplyRetryTimeouts(s, prefix + suffix) == C.ApplyRetryTimeouts(s, suffix + prefix);
    } else {
      assert prefix == [];
      assert prefix + suffix == suffix + prefix;
    }
  }

  lemma ApplyRetryTimeoutsPermutationDistinct(s: C.CoordinationState, xs: seq<C.Id>, ys: seq<C.Id>)
    requires DistinctIds(xs)
    requires DistinctIds(ys)
    requires multiset(xs) == multiset(ys)
    ensures C.ApplyRetryTimeouts(s, xs) == C.ApplyRetryTimeouts(s, ys)
    decreases |xs|
  {
    if |xs| == 0 {
      assert multiset(ys) == multiset([]);
      assert ys == [];
    } else {
      assert |ys| != 0;
      var head := xs[0];
      var rest := xs[1..];
      assert head in multiset(ys);
      SeqMemberHasIndex(ys, head);
      var k :| 0 <= k < |ys| && ys[k] == head;
      var prefix := ys[..k];
      var suffix := ys[k+1..];
      assert ys == prefix + [head] + suffix;
      assert ys == prefix + ([head] + suffix);
      assert DistinctIds(prefix + ([head] + suffix));
      DistinctIdsRotateBlocks(prefix, [head] + suffix);
      assert ([head] + suffix) + prefix == [head] + (suffix + prefix);
      assert DistinctIds([head] + (suffix + prefix));
      DistinctIdsTail(head, suffix + prefix);
      assert DistinctIds(suffix + prefix);
      assert xs == [head] + rest;
      assert multiset(xs) == multiset([head] + rest);
      assert multiset(ys) == multiset(prefix + ([head] + suffix));
      assert multiset(rest) == multiset(xs) - multiset([head]);
      assert multiset(suffix + prefix) == multiset(([head] + suffix) + prefix) - multiset([head]);
      assert multiset(([head] + suffix) + prefix) == multiset(ys);
      assert multiset(rest) == multiset(suffix + prefix);
      ApplyRetryTimeoutsPermutationDistinct(C.ExpireRetryTimeout(s, head), rest, suffix + prefix);
      ApplyRetryTimeoutsRotateBlocks(s, prefix, [head] + suffix);
      calc {
        C.ApplyRetryTimeouts(s, xs);
        == { }
        C.ApplyRetryTimeouts(s, [head] + rest);
        == { }
        C.ApplyRetryTimeouts(C.ExpireRetryTimeout(s, head), rest);
        == { ApplyRetryTimeoutsPermutationDistinct(C.ExpireRetryTimeout(s, head), rest, suffix + prefix); }
        C.ApplyRetryTimeouts(C.ExpireRetryTimeout(s, head), suffix + prefix);
        == { }
        C.ApplyRetryTimeouts(s, [head] + (suffix + prefix));
        == { assert [head] + (suffix + prefix) == ([head] + suffix) + prefix; }
        C.ApplyRetryTimeouts(s, ([head] + suffix) + prefix);
        == { ApplyRetryTimeoutsRotateBlocks(s, prefix, [head] + suffix); }
        C.ApplyRetryTimeouts(s, prefix + ([head] + suffix));
        == { assert prefix + ([head] + suffix) == ys; }
        C.ApplyRetryTimeouts(s, ys);
      }
    }
  }

  lemma ApplyPromiseTimeoutsPermutationIndependent(s: C.CoordinationState, xs: seq<C.Id>, ys: seq<C.Id>)
    requires PromiseTimeoutBatchIndependent(s, xs)
    requires DistinctIds(ys)
    requires multiset(xs) == multiset(ys)
    ensures C.ApplyPromiseTimeouts(s, xs) == C.ApplyPromiseTimeouts(s, ys)
    decreases |xs|
  {
    PromiseTimeoutBatchIndependentPermutation(s, xs, ys);
    if |xs| == 0 {
      assert multiset(ys) == multiset([]);
      assert ys == [];
    } else {
      assert |ys| != 0;
      var head := xs[0];
      var rest := xs[1..];
      assert head in multiset(ys);
      SeqMemberHasIndex(ys, head);
      var k :| 0 <= k < |ys| && ys[k] == head;
      var prefix := ys[..k];
      var suffix := ys[k+1..];
      assert ys == prefix + [head] + suffix;
      assert ys == prefix + ([head] + suffix);
      DistinctIdsRotateBlocks(prefix, [head] + suffix);
      assert ([head] + suffix) + prefix == [head] + (suffix + prefix);
      PromiseTimeoutBatchIndependentPermutation(s, ys, [head] + (suffix + prefix));
      PromiseTimeoutBatchIndependentTail(s, head, rest);
      PromiseTimeoutBatchIndependentTail(s, head, suffix + prefix);
      assert xs == [head] + rest;
      assert multiset(xs) == multiset([head] + rest);
      assert multiset(ys) == multiset(prefix + ([head] + suffix));
      assert multiset(rest) == multiset(xs) - multiset([head]);
      assert multiset(suffix + prefix) == multiset(([head] + suffix) + prefix) - multiset([head]);
      assert multiset(([head] + suffix) + prefix) == multiset(ys);
      assert multiset(rest) == multiset(suffix + prefix);
      PromiseTimeoutBatchIndependentAfterExpire(s, head, rest);
      PromiseTimeoutBatchIndependentAfterExpire(s, head, suffix + prefix);
      ApplyPromiseTimeoutsPermutationIndependent(C.ExpirePromiseTimeout(s, head), rest, suffix + prefix);
      ApplyPromiseTimeoutsRotateBlocksIndependent(s, prefix, [head] + suffix);
      calc {
        C.ApplyPromiseTimeouts(s, xs);
        == { }
        C.ApplyPromiseTimeouts(s, [head] + rest);
        == { }
        C.ApplyPromiseTimeouts(C.ExpirePromiseTimeout(s, head), rest);
        == { ApplyPromiseTimeoutsPermutationIndependent(C.ExpirePromiseTimeout(s, head), rest, suffix + prefix); }
        C.ApplyPromiseTimeouts(C.ExpirePromiseTimeout(s, head), suffix + prefix);
        == { }
        C.ApplyPromiseTimeouts(s, [head] + (suffix + prefix));
        == { assert [head] + (suffix + prefix) == ([head] + suffix) + prefix; }
        C.ApplyPromiseTimeouts(s, ([head] + suffix) + prefix);
        == { ApplyPromiseTimeoutsRotateBlocksIndependent(s, prefix, [head] + suffix); }
        C.ApplyPromiseTimeouts(s, prefix + ([head] + suffix));
        == { assert prefix + ([head] + suffix) == ys; }
        C.ApplyPromiseTimeouts(s, ys);
      }
    }
  }

  lemma ResumeReadyAwaitersPermutationDistinct(s: C.CoordinationState, xs: seq<C.Id>, ys: seq<C.Id>)
    requires DistinctIds(xs)
    requires DistinctIds(ys)
    requires multiset(xs) == multiset(ys)
    ensures C.ResumeReadyAwaiters(s, xs) == C.ResumeReadyAwaiters(s, ys)
    decreases |xs|
  {
    if |xs| == 0 {
      assert multiset(ys) == multiset([]);
      assert ys == [];
    } else {
      assert |ys| != 0;
      var head := xs[0];
      var rest := xs[1..];
      assert head in multiset(ys);
      SeqMemberHasIndex(ys, head);
      var k :| 0 <= k < |ys| && ys[k] == head;
      var prefix := ys[..k];
      var suffix := ys[k+1..];
      assert ys == prefix + [head] + suffix;
      assert ys == prefix + ([head] + suffix);
      assert DistinctIds(prefix + ([head] + suffix));
      DistinctIdsRotateBlocks(prefix, [head] + suffix);
      assert ([head] + suffix) + prefix == [head] + (suffix + prefix);
      assert DistinctIds([head] + (suffix + prefix));
      DistinctIdsTail(head, suffix + prefix);
      assert DistinctIds(suffix + prefix);
      assert xs == [head] + rest;
      assert multiset(xs) == multiset([head] + rest);
      assert multiset(ys) == multiset(prefix + ([head] + suffix));
      assert multiset(rest) == multiset(xs) - multiset([head]);
      assert multiset(suffix + prefix) == multiset(([head] + suffix) + prefix) - multiset([head]);
      assert multiset(([head] + suffix) + prefix) == multiset(ys);
      assert multiset(rest) == multiset(suffix + prefix);
      ResumeReadyAwaitersPermutationDistinct(C.ResumeReadyAwaiter(s, head), rest, suffix + prefix);
      ResumeReadyAwaitersRotateBlocks(s, prefix, [head] + suffix);
      calc {
        C.ResumeReadyAwaiters(s, xs);
        == { }
        C.ResumeReadyAwaiters(s, [head] + rest);
        == { }
        C.ResumeReadyAwaiters(C.ResumeReadyAwaiter(s, head), rest);
        == { ResumeReadyAwaitersPermutationDistinct(C.ResumeReadyAwaiter(s, head), rest, suffix + prefix); }
        C.ResumeReadyAwaiters(C.ResumeReadyAwaiter(s, head), suffix + prefix);
        == { }
        C.ResumeReadyAwaiters(s, [head] + (suffix + prefix));
        == { assert [head] + (suffix + prefix) == ([head] + suffix) + prefix; }
        C.ResumeReadyAwaiters(s, ([head] + suffix) + prefix);
        == { ResumeReadyAwaitersRotateBlocks(s, prefix, [head] + suffix); }
        C.ResumeReadyAwaiters(s, prefix + ([head] + suffix));
        == { assert prefix + ([head] + suffix) == ys; }
        C.ResumeReadyAwaiters(s, ys);
      }
    }
  }

  predicate EnumeratesSet(xs: seq<C.Id>, ids: set<C.Id>) {
    DistinctIds(xs) &&
    (set id: C.Id | id in multiset(xs) :: id) == ids
  }

  lemma ExpiredRetryTimeoutRowsAtMatchesTimedEligible(s: C.CoordinationState, rows: C.TimeoutRows, now: nat)
    requires C.Valid(s)
    requires C.ValidTimeoutRows(s, rows)
    ensures C.ExpiredRetryTimeoutRowsAt(s, rows, now) ==
            (set id: C.Id | id in C.EligibleRetryTimeouts(s) && id in rows.retryAt && rows.retryAt[id] <= now)
  {
  }

  lemma ExpiredLeaseTimeoutRowsAtMatchesTimedEligible(s: C.CoordinationState, rows: C.TimeoutRows, now: nat)
    requires C.Valid(s)
    requires C.ValidTimeoutRows(s, rows)
    ensures C.ExpiredLeaseTimeoutRowsAt(s, rows, now) ==
            (set id: C.Id | id in C.EligibleLeaseTimeouts(s) && id in rows.leaseAt && rows.leaseAt[id] <= now)
  {
  }

  lemma SqliteRetryTimeoutQueryMatchesTimeoutRows(s: C.CoordinationState, rows: C.TimeoutRows, now: nat)
    ensures C.SqliteRetryTimeoutQuery(s, rows, now) == C.ExpiredRetryTimeoutRowsAt(s, rows, now)
  {
  }

  lemma SqliteLeaseTimeoutQueryMatchesTimeoutRows(s: C.CoordinationState, rows: C.TimeoutRows, now: nat)
    ensures C.SqliteLeaseTimeoutQuery(s, rows, now) == C.ExpiredLeaseTimeoutRowsAt(s, rows, now)
  {
  }

  lemma PostgresRetryTimeoutQueryMatchesTimeoutRows(s: C.CoordinationState, rows: C.TimeoutRows, now: nat)
    ensures C.PostgresRetryTimeoutQuery(s, rows, now) == C.ExpiredRetryTimeoutRowsAt(s, rows, now)
  {
    SqliteRetryTimeoutQueryMatchesTimeoutRows(s, rows, now);
  }

  lemma PostgresLeaseTimeoutQueryMatchesTimeoutRows(s: C.CoordinationState, rows: C.TimeoutRows, now: nat)
    ensures C.PostgresLeaseTimeoutQuery(s, rows, now) == C.ExpiredLeaseTimeoutRowsAt(s, rows, now)
  {
    SqliteLeaseTimeoutQueryMatchesTimeoutRows(s, rows, now);
  }

  ghost predicate TimeoutBatchQueryShape(s: C.CoordinationState, rows: C.TimeoutRows, now: nat, retryDelay: nat, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, expiredLeases: seq<C.Id>) {
    C.ValidTimeoutRows(s, rows) &&
    EnumeratesSet(expiredPromises, C.ExpiredPromisesAt(s, now)) &&
    PromiseTimeoutBatchIndependent(s, expiredPromises) &&
    EnumeratesSet(readyAwaiters, C.ReadyAwaiters(C.ApplyPromiseTimeouts(s, expiredPromises))) &&
    EnumeratesSet(expiredRetries, C.ExpiredRetryTimeoutRowsAt(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay), now)) &&
    EnumeratesSet(expiredLeases, C.ExpiredLeaseTimeoutRowsAt(C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries), C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay), now))
  }

  lemma ApplyLeaseTimeoutsRotateBlocks(s: C.CoordinationState, prefix: seq<C.Id>, suffix: seq<C.Id>)
    requires DistinctIds(prefix + suffix)
    ensures C.ApplyLeaseTimeouts(s, prefix + suffix) == C.ApplyLeaseTimeouts(s, suffix + prefix)
    decreases |prefix|
  {
    if |prefix| != 0 {
      var head := prefix[0];
      var rest := prefix[1..];
      assert prefix + suffix == [head] + (rest + suffix);
      ApplyLeaseTimeoutsMoveHeadToTail(s, head, rest + suffix);
      DistinctIdsMoveHeadToTail(head, rest + suffix);
      assert rest + (suffix + [head]) == (rest + suffix) + [head];
      ApplyLeaseTimeoutsRotateBlocks(s, rest, suffix + [head]);
      assert suffix + prefix == (suffix + [head]) + rest;
      assert C.ApplyLeaseTimeouts(s, prefix + suffix) == C.ApplyLeaseTimeouts(s, [head] + (rest + suffix));
      assert C.ApplyLeaseTimeouts(s, [head] + (rest + suffix)) == C.ApplyLeaseTimeouts(s, (rest + suffix) + [head]);
      assert C.ApplyLeaseTimeouts(s, (rest + suffix) + [head]) == C.ApplyLeaseTimeouts(s, rest + (suffix + [head]));
      assert C.ApplyLeaseTimeouts(s, rest + (suffix + [head])) == C.ApplyLeaseTimeouts(s, (suffix + [head]) + rest);
      assert C.ApplyLeaseTimeouts(s, (suffix + [head]) + rest) == C.ApplyLeaseTimeouts(s, suffix + prefix);
      assert C.ApplyLeaseTimeouts(s, prefix + suffix) == C.ApplyLeaseTimeouts(s, suffix + prefix);
    } else {
      assert prefix == [];
      assert prefix + suffix == suffix + prefix;
    }
  }

  lemma ApplyLeaseTimeoutsPermutationDistinct(s: C.CoordinationState, xs: seq<C.Id>, ys: seq<C.Id>)
    requires DistinctIds(xs)
    requires DistinctIds(ys)
    requires multiset(xs) == multiset(ys)
    ensures C.ApplyLeaseTimeouts(s, xs) == C.ApplyLeaseTimeouts(s, ys)
    decreases |xs|
  {
    if |xs| == 0 {
      assert multiset(ys) == multiset([]);
      assert ys == [];
    } else {
      assert |ys| != 0;
      var head := xs[0];
      var rest := xs[1..];
      assert head in multiset(ys);
      SeqMemberHasIndex(ys, head);
      var k :| 0 <= k < |ys| && ys[k] == head;
      var prefix := ys[..k];
      var suffix := ys[k+1..];
      assert ys == prefix + [head] + suffix;
      assert ys == prefix + ([head] + suffix);
      assert DistinctIds(prefix + ([head] + suffix));
      DistinctIdsRotateBlocks(prefix, [head] + suffix);
      assert ([head] + suffix) + prefix == [head] + (suffix + prefix);
      assert DistinctIds([head] + (suffix + prefix));
      DistinctIdsTail(head, suffix + prefix);
      assert DistinctIds(suffix + prefix);
      assert xs == [head] + rest;
      assert multiset(xs) == multiset([head] + rest);
      assert multiset(ys) == multiset(prefix + ([head] + suffix));
      assert multiset(rest) == multiset(xs) - multiset([head]);
      assert multiset(suffix + prefix) == multiset(([head] + suffix) + prefix) - multiset([head]);
      assert multiset(([head] + suffix) + prefix) == multiset(ys);
      assert multiset(rest) == multiset(suffix + prefix);
      ApplyLeaseTimeoutsPermutationDistinct(C.ExpireLeaseTimeout(s, head), rest, suffix + prefix);
      ApplyLeaseTimeoutsRotateBlocks(s, prefix, [head] + suffix);
      calc {
        C.ApplyLeaseTimeouts(s, xs);
        == { }
        C.ApplyLeaseTimeouts(s, [head] + rest);
        == { }
        C.ApplyLeaseTimeouts(C.ExpireLeaseTimeout(s, head), rest);
        == { ApplyLeaseTimeoutsPermutationDistinct(C.ExpireLeaseTimeout(s, head), rest, suffix + prefix); }
        C.ApplyLeaseTimeouts(C.ExpireLeaseTimeout(s, head), suffix + prefix);
        == { }
        C.ApplyLeaseTimeouts(s, [head] + (suffix + prefix));
        == { assert [head] + (suffix + prefix) == ([head] + suffix) + prefix; }
        C.ApplyLeaseTimeouts(s, ([head] + suffix) + prefix);
        == { ApplyLeaseTimeoutsRotateBlocks(s, prefix, [head] + suffix); }
        C.ApplyLeaseTimeouts(s, prefix + ([head] + suffix));
        == { assert prefix + ([head] + suffix) == ys; }
        C.ApplyLeaseTimeouts(s, ys);
      }
    }
  }

  lemma ProcessTimeoutBatchPromisePermutationIndependent(s: C.CoordinationState, xs: seq<C.Id>, ys: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, expiredLeases: seq<C.Id>)
    requires PromiseTimeoutBatchIndependent(s, xs)
    requires DistinctIds(ys)
    requires multiset(xs) == multiset(ys)
    ensures C.ProcessTimeoutBatch(s, xs, readyAwaiters, expiredRetries, expiredLeases) ==
            C.ProcessTimeoutBatch(s, ys, readyAwaiters, expiredRetries, expiredLeases)
  {
    ApplyPromiseTimeoutsPermutationIndependent(s, xs, ys);
  }

  lemma TimeoutBatchQueryShapeMatchesBackendPhaseInputs(s: C.CoordinationState, rows: C.TimeoutRows, now: nat, retryDelay: nat, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, expiredLeases: seq<C.Id>)
    requires C.Valid(s)
    requires TimeoutBatchQueryShape(s, rows, now, retryDelay, expiredPromises, readyAwaiters, expiredRetries, expiredLeases)
    ensures C.ProcessTimeoutBatch(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases) ==
            C.SqliteTimeoutStatements(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases)
    ensures C.ProcessTimeoutBatch(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases) ==
            C.PostgresTimeoutStatements(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases)
    ensures EnumeratesSet(expiredRetries,
            (set id: C.Id |
              id in C.EligibleRetryTimeouts(C.TimeoutStatement1(s, expiredPromises, readyAwaiters)) &&
              id in C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay).retryAt &&
              C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay).retryAt[id] <= now))
    ensures EnumeratesSet(expiredLeases,
            (set id: C.Id |
              id in C.EligibleLeaseTimeouts(C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries)) &&
              id in C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay).leaseAt &&
              C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay).leaseAt[id] <= now))
    ensures EnumeratesSet(expiredRetries,
            C.SqliteRetryTimeoutQuery(
              C.TimeoutStatement1(s, expiredPromises, readyAwaiters),
              C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay),
              now))
    ensures EnumeratesSet(expiredLeases,
            C.SqliteLeaseTimeoutQuery(
              C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries),
              C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay),
              now))
    ensures EnumeratesSet(expiredRetries,
            C.PostgresRetryTimeoutQuery(
              C.TimeoutStatement1(s, expiredPromises, readyAwaiters),
              C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay),
              now))
    ensures EnumeratesSet(expiredLeases,
            C.PostgresLeaseTimeoutQuery(
              C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries),
              C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay),
              now))
  {
    TimeoutStatement1PreservesValidity(s, expiredPromises, readyAwaiters);
    ApplyRetryTimeoutsPreservesValidity(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries);
    TimeoutRowsAfterStatement1PreservesValidity(s, rows, expiredPromises, readyAwaiters, now, retryDelay);
    TimeoutRowsAfterStatement2PreservesValidity(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay);
    SqliteRetryTimeoutQueryMatchesTimeoutRows(
      C.TimeoutStatement1(s, expiredPromises, readyAwaiters),
      C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay),
      now);
    SqliteLeaseTimeoutQueryMatchesTimeoutRows(
      C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries),
      C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay),
      now);
    PostgresRetryTimeoutQueryMatchesTimeoutRows(
      C.TimeoutStatement1(s, expiredPromises, readyAwaiters),
      C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay),
      now);
    PostgresLeaseTimeoutQueryMatchesTimeoutRows(
      C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries),
      C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay),
      now);
    ExpiredRetryTimeoutRowsAtMatchesTimedEligible(
      C.TimeoutStatement1(s, expiredPromises, readyAwaiters),
      C.TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay),
      now);
    ExpiredLeaseTimeoutRowsAtMatchesTimedEligible(
      C.TimeoutStatement2(C.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries),
      C.TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay),
      now);
    ProcessTimeoutBatchEqualsSqliteTimeoutStatements(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases);
    ProcessTimeoutBatchEqualsPostgresTimeoutStatements(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases);
  }

  lemma SqliteTimeoutStatementsPromisePermutationIndependent(s: C.CoordinationState, xs: seq<C.Id>, ys: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, expiredLeases: seq<C.Id>)
    requires PromiseTimeoutBatchIndependent(s, xs)
    requires DistinctIds(ys)
    requires multiset(xs) == multiset(ys)
    ensures C.SqliteTimeoutStatements(s, xs, readyAwaiters, expiredRetries, expiredLeases) ==
            C.SqliteTimeoutStatements(s, ys, readyAwaiters, expiredRetries, expiredLeases)
  {
    ProcessTimeoutBatchEqualsSqliteTimeoutStatements(s, xs, readyAwaiters, expiredRetries, expiredLeases);
    ProcessTimeoutBatchEqualsSqliteTimeoutStatements(s, ys, readyAwaiters, expiredRetries, expiredLeases);
    ProcessTimeoutBatchPromisePermutationIndependent(s, xs, ys, readyAwaiters, expiredRetries, expiredLeases);
  }

  lemma PostgresTimeoutStatementsPromisePermutationIndependent(s: C.CoordinationState, xs: seq<C.Id>, ys: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, expiredLeases: seq<C.Id>)
    requires PromiseTimeoutBatchIndependent(s, xs)
    requires DistinctIds(ys)
    requires multiset(xs) == multiset(ys)
    ensures C.PostgresTimeoutStatements(s, xs, readyAwaiters, expiredRetries, expiredLeases) ==
            C.PostgresTimeoutStatements(s, ys, readyAwaiters, expiredRetries, expiredLeases)
  {
    ProcessTimeoutBatchEqualsPostgresTimeoutStatements(s, xs, readyAwaiters, expiredRetries, expiredLeases);
    ProcessTimeoutBatchEqualsPostgresTimeoutStatements(s, ys, readyAwaiters, expiredRetries, expiredLeases);
    ProcessTimeoutBatchPromisePermutationIndependent(s, xs, ys, readyAwaiters, expiredRetries, expiredLeases);
  }

  lemma SqliteTimeoutStatementsResumesAwaiterAfterSettlement(s: C.CoordinationState, awaited: C.Id, awaiter: C.Id)
    requires C.Valid(s)
    requires awaited in s.core.promises
    requires s.core.promises[awaited].state == Core.Pending
    requires C.CallbackKey(awaited, awaiter) in s.callbacks
    requires awaiter in s.core.tasks
    requires s.core.tasks[awaiter].state == Core.Suspended
    requires awaiter != awaited
    ensures awaiter in C.SqliteTimeoutStatements(s, [awaited], [awaiter], [], []).outgoingExec
    ensures C.SqliteTimeoutStatements(s, [awaited], [awaiter], [], []).outgoingExec[awaiter] == s.core.tasks[awaiter].version + 1
  {
    ProcessTimeoutBatchEqualsSqliteTimeoutStatements(s, [awaited], [awaiter], [], []);
    ProcessTimeoutBatchResumesAwaiterAfterSettlement(s, awaited, awaiter);
  }

  lemma PostgresTimeoutStatementsResumesAwaiterAfterSettlement(s: C.CoordinationState, awaited: C.Id, awaiter: C.Id)
    requires C.Valid(s)
    requires awaited in s.core.promises
    requires s.core.promises[awaited].state == Core.Pending
    requires C.CallbackKey(awaited, awaiter) in s.callbacks
    requires awaiter in s.core.tasks
    requires s.core.tasks[awaiter].state == Core.Suspended
    requires awaiter != awaited
    ensures awaiter in C.PostgresTimeoutStatements(s, [awaited], [awaiter], [], []).outgoingExec
    ensures C.PostgresTimeoutStatements(s, [awaited], [awaiter], [], []).outgoingExec[awaiter] == s.core.tasks[awaiter].version + 1
  {
    ProcessTimeoutBatchEqualsPostgresTimeoutStatements(s, [awaited], [awaiter], [], []);
    ProcessTimeoutBatchResumesAwaiterAfterSettlement(s, awaited, awaiter);
  }

  lemma SqliteTimeoutStatementsUnblocksTimedoutListener(s: C.CoordinationState, id: C.Id, address: C.Address)
    requires C.Valid(s)
    requires id in s.core.promises
    requires s.core.promises[id].state == Core.Pending
    requires !s.core.promises[id].timer
    requires C.ListenerKey(id, address) in s.listeners
    ensures C.ListenerKey(id, address) in C.SqliteTimeoutStatements(s, [id], [], [], []).outgoingUnblock
    ensures C.ListenerKey(id, address) !in C.SqliteTimeoutStatements(s, [id], [], [], []).listeners
  {
    ProcessTimeoutBatchEqualsSqliteTimeoutStatements(s, [id], [], [], []);
    ProcessTimeoutBatchUnblocksTimedoutListener(s, id, address);
  }

  lemma PostgresTimeoutStatementsUnblocksTimedoutListener(s: C.CoordinationState, id: C.Id, address: C.Address)
    requires C.Valid(s)
    requires id in s.core.promises
    requires s.core.promises[id].state == Core.Pending
    requires !s.core.promises[id].timer
    requires C.ListenerKey(id, address) in s.listeners
    ensures C.ListenerKey(id, address) in C.PostgresTimeoutStatements(s, [id], [], [], []).outgoingUnblock
    ensures C.ListenerKey(id, address) !in C.PostgresTimeoutStatements(s, [id], [], [], []).listeners
  {
    ProcessTimeoutBatchEqualsPostgresTimeoutStatements(s, [id], [], [], []);
    ProcessTimeoutBatchUnblocksTimedoutListener(s, id, address);
  }

  lemma SqliteTimeoutStatementsEnqueuesExpiredRetry(s: C.CoordinationState, id: C.Id)
    requires C.Valid(s)
    requires id in s.core.retryTimeouts
    requires id in s.core.tasks
    requires s.core.tasks[id].state == Core.TaskPending
    ensures id in C.SqliteTimeoutStatements(s, [], [], [id], []).outgoingExec
    ensures C.SqliteTimeoutStatements(s, [], [], [id], []).outgoingExec[id] == s.core.tasks[id].version
  {
    ProcessTimeoutBatchEqualsSqliteTimeoutStatements(s, [], [], [id], []);
    ProcessTimeoutBatchEnqueuesExpiredRetry(s, id);
  }

  lemma PostgresTimeoutStatementsEnqueuesExpiredRetry(s: C.CoordinationState, id: C.Id)
    requires C.Valid(s)
    requires id in s.core.retryTimeouts
    requires id in s.core.tasks
    requires s.core.tasks[id].state == Core.TaskPending
    ensures id in C.PostgresTimeoutStatements(s, [], [], [id], []).outgoingExec
    ensures C.PostgresTimeoutStatements(s, [], [], [id], []).outgoingExec[id] == s.core.tasks[id].version
  {
    ProcessTimeoutBatchEqualsPostgresTimeoutStatements(s, [], [], [id], []);
    ProcessTimeoutBatchEnqueuesExpiredRetry(s, id);
  }

  lemma SqliteTimeoutStatementsReleasesExpiredLease(s: C.CoordinationState, id: C.Id)
    requires C.Valid(s)
    requires id in s.core.leaseTimeouts
    requires id in s.core.tasks
    requires s.core.tasks[id].state == Core.Acquired
    ensures id in C.SqliteTimeoutStatements(s, [], [], [], [id]).outgoingExec
    ensures C.SqliteTimeoutStatements(s, [], [], [], [id]).outgoingExec[id] == s.core.tasks[id].version + 1
  {
    ProcessTimeoutBatchEqualsSqliteTimeoutStatements(s, [], [], [], [id]);
    ProcessTimeoutBatchReleasesExpiredLease(s, id);
  }

  lemma PostgresTimeoutStatementsReleasesExpiredLease(s: C.CoordinationState, id: C.Id)
    requires C.Valid(s)
    requires id in s.core.leaseTimeouts
    requires id in s.core.tasks
    requires s.core.tasks[id].state == Core.Acquired
    ensures id in C.PostgresTimeoutStatements(s, [], [], [], [id]).outgoingExec
    ensures C.PostgresTimeoutStatements(s, [], [], [], [id]).outgoingExec[id] == s.core.tasks[id].version + 1
  {
    ProcessTimeoutBatchEqualsPostgresTimeoutStatements(s, [], [], [], [id]);
    ProcessTimeoutBatchReleasesExpiredLease(s, id);
  }

  lemma ProcessTimeoutBatchSettlesTimedoutPromise(s: C.CoordinationState, id: C.Id)
    requires C.Valid(s)
    requires id in s.core.promises
    requires s.core.promises[id].state == Core.Pending
    requires !s.core.promises[id].timer
    ensures id in C.ProcessTimeoutBatch(s, [id], [], [], []).core.promises
    ensures C.ProcessTimeoutBatch(s, [id], [], [], []).core.promises[id].state == Core.RejectedTimedout
  {
    var settled := C.ApplyPromiseTimeouts(s, [id]);
    ApplyPromiseTimeoutsSingleton(s, id);
    assert C.TimeoutSettlementState(s, id) == Core.RejectedTimedout;
    assert settled.core.promises[id].state == Core.RejectedTimedout;
    assert C.ProcessTimeoutBatch(s, [id], [], [], []) == settled;
  }

  lemma ProcessTimeoutBatchUnblocksTimedoutListener(s: C.CoordinationState, id: C.Id, address: C.Address)
    requires C.Valid(s)
    requires id in s.core.promises
    requires s.core.promises[id].state == Core.Pending
    requires !s.core.promises[id].timer
    requires C.ListenerKey(id, address) in s.listeners
    ensures C.ListenerKey(id, address) in C.ProcessTimeoutBatch(s, [id], [], [], []).outgoingUnblock
    ensures C.ListenerKey(id, address) !in C.ProcessTimeoutBatch(s, [id], [], [], []).listeners
  {
    var settled := C.ApplyPromiseTimeouts(s, [id]);
    ApplyPromiseTimeoutsSingleton(s, id);
    assert C.TimeoutSettlementState(s, id) == Core.RejectedTimedout;
    assert C.ListenerKey(id, address) in settled.outgoingUnblock;
    assert C.ListenerKey(id, address) !in settled.listeners;
    assert C.ProcessTimeoutBatch(s, [id], [], [], []) == settled;
  }

  lemma ProcessTimeoutBatchResumesAwaiterAfterSettlement(s: C.CoordinationState, awaited: C.Id, awaiter: C.Id)
    requires C.Valid(s)
    requires awaited in s.core.promises
    requires s.core.promises[awaited].state == Core.Pending
    requires C.CallbackKey(awaited, awaiter) in s.callbacks
    requires awaiter in s.core.tasks
    requires s.core.tasks[awaiter].state == Core.Suspended
    requires awaiter != awaited
    ensures awaiter in C.ProcessTimeoutBatch(s, [awaited], [awaiter], [], []).core.tasks
    ensures C.ProcessTimeoutBatch(s, [awaited], [awaiter], [], []).core.tasks[awaiter].state == Core.TaskPending
    ensures C.ProcessTimeoutBatch(s, [awaited], [awaiter], [], []).core.tasks[awaiter].version == s.core.tasks[awaiter].version + 1
    ensures awaiter in C.ProcessTimeoutBatch(s, [awaited], [awaiter], [], []).outgoingExec
    ensures C.ProcessTimeoutBatch(s, [awaited], [awaiter], [], []).outgoingExec[awaiter] == s.core.tasks[awaiter].version + 1
  {
    var settled := C.ApplyPromiseTimeouts(s, [awaited]);
    ApplyPromiseTimeoutsSingleton(s, awaited);
    ExpirePromiseTimeoutPreservesValidity(s, awaited);
    assert C.Valid(settled);
    assert C.CallbackKey(awaited, awaiter) in settled.readyCallbacks;
    assert C.HasReadyCallbackFor(settled, awaiter);
    ReadyAwaiterResumesToPending(settled, awaiter);
    var resumed := C.ResumeReadyAwaiters(settled, [awaiter]);
    ResumeReadyAwaitersSingleton(settled, awaiter);
    assert resumed.outgoingExec[awaiter] == s.core.tasks[awaiter].version + 1;
    assert C.ProcessTimeoutBatch(s, [awaited], [awaiter], [], []) == resumed;
  }

  lemma ProcessTimeoutBatchEnqueuesExpiredRetry(s: C.CoordinationState, id: C.Id)
    requires C.Valid(s)
    requires id in s.core.retryTimeouts
    requires id in s.core.tasks
    requires s.core.tasks[id].state == Core.TaskPending
    ensures id in C.ProcessTimeoutBatch(s, [], [], [id], []).outgoingExec
    ensures C.ProcessTimeoutBatch(s, [], [], [id], []).outgoingExec[id] == s.core.tasks[id].version
  {
    var retried := C.ApplyRetryTimeouts(s, [id]);
    ApplyRetryTimeoutsSingleton(s, id);
    assert id in retried.outgoingExec;
    assert retried.outgoingExec[id] == s.core.tasks[id].version;
    assert C.ProcessTimeoutBatch(s, [], [], [id], []) == retried;
  }

  lemma ProcessTimeoutBatchReleasesExpiredLease(s: C.CoordinationState, id: C.Id)
    requires C.Valid(s)
    requires id in s.core.leaseTimeouts
    requires id in s.core.tasks
    requires s.core.tasks[id].state == Core.Acquired
    ensures id in C.ProcessTimeoutBatch(s, [], [], [], [id]).core.tasks
    ensures C.ProcessTimeoutBatch(s, [], [], [], [id]).core.tasks[id].state == Core.TaskPending
    ensures C.ProcessTimeoutBatch(s, [], [], [], [id]).core.tasks[id].version == s.core.tasks[id].version + 1
    ensures id in C.ProcessTimeoutBatch(s, [], [], [], [id]).outgoingExec
    ensures C.ProcessTimeoutBatch(s, [], [], [], [id]).outgoingExec[id] == s.core.tasks[id].version + 1
  {
    var released := C.ApplyLeaseTimeouts(s, [id]);
    ApplyLeaseTimeoutsSingleton(s, id);
    assert released.core.tasks[id].state == Core.TaskPending;
    assert released.core.tasks[id].version == s.core.tasks[id].version + 1;
    assert id in released.outgoingExec;
    assert released.outgoingExec[id] == s.core.tasks[id].version + 1;
    assert C.ProcessTimeoutBatch(s, [], [], [], [id]) == released;
  }

  lemma ScheduleCreateAndRunPreserveValidity(s: C.CoordinationState, scheduleId: C.Id, firstRunAt: nat, promiseTimeout: nat, promiseId: C.Id, createdAt: nat, timeoutAt: nat, nextRunAt: nat)
    requires C.Valid(s)
    requires nextRunAt > createdAt
    ensures C.Valid(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout))
    ensures C.Valid(C.ScheduleRun(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, promiseId, createdAt, timeoutAt, nextRunAt))
  {
    var created := C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout);
    if scheduleId !in s.schedules {
      assert created == C.State(s.core, s.callbacks, s.readyCallbacks, s.listeners, s.outgoingExec, s.outgoingUnblock, s.schedules[scheduleId := C.ScheduleRec(firstRunAt, 0, false, promiseTimeout)]);
    }
    var ran := C.ScheduleRun(created, scheduleId, promiseId, createdAt, timeoutAt, nextRunAt);
    assert ran.schedules[scheduleId].hasRun;
    assert ran.schedules[scheduleId].lastRunAt == createdAt;
    assert ran.schedules[scheduleId].nextRunAt == nextRunAt;
  }

  lemma ScheduleRunAdvancesNextRun(s: C.CoordinationState, scheduleId: C.Id, firstRunAt: nat, promiseTimeout: nat, promiseId: C.Id, createdAt: nat, timeoutAt: nat, nextRunAt: nat)
    requires C.Valid(s)
    requires nextRunAt > createdAt
    ensures C.ScheduleRun(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, promiseId, createdAt, timeoutAt, nextRunAt).schedules[scheduleId].hasRun
    ensures C.ScheduleRun(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, promiseId, createdAt, timeoutAt, nextRunAt).schedules[scheduleId].lastRunAt == createdAt
    ensures C.ScheduleRun(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, promiseId, createdAt, timeoutAt, nextRunAt).schedules[scheduleId].nextRunAt == nextRunAt
    ensures promiseId in C.ScheduleRun(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, promiseId, createdAt, timeoutAt, nextRunAt).core.promises
  {
    var created := C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout);
    var ran := C.ScheduleRun(created, scheduleId, promiseId, createdAt, timeoutAt, nextRunAt);
    assert ran.schedules[scheduleId].hasRun;
    assert ran.schedules[scheduleId].lastRunAt == createdAt;
    assert ran.schedules[scheduleId].nextRunAt == nextRunAt;
    assert ran.core == C.InsertRunPromise(created.core, promiseId, timeoutAt, createdAt);
    assert promiseId in ran.core.promises;
  }

  lemma ScheduleRunIsIdempotent(s: C.CoordinationState, scheduleId: C.Id, firstRunAt: nat, promiseTimeout: nat, promiseId: C.Id, createdAt: nat, timeoutAt: nat, nextRunAt: nat)
    requires C.Valid(s)
    requires nextRunAt > createdAt
    ensures C.ScheduleRun(
      C.ScheduleRun(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, promiseId, createdAt, timeoutAt, nextRunAt),
      scheduleId,
      promiseId,
      createdAt,
      timeoutAt,
      nextRunAt) ==
      C.ScheduleRun(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, promiseId, createdAt, timeoutAt, nextRunAt)
  {
    var created := C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout);
    var firstRun := C.ScheduleRun(created, scheduleId, promiseId, createdAt, timeoutAt, nextRunAt);
    assert promiseId in firstRun.core.promises;
    assert firstRun.schedules[scheduleId] == C.ScheduleRec(nextRunAt, createdAt, true, created.schedules[scheduleId].promiseTimeout);
    assert C.InsertRunPromise(firstRun.core, promiseId, timeoutAt, createdAt) == firstRun.core;
    assert C.ScheduleRun(firstRun, scheduleId, promiseId, createdAt, timeoutAt, nextRunAt) ==
      C.State(firstRun.core, firstRun.callbacks, firstRun.readyCallbacks, firstRun.listeners, firstRun.outgoingExec, firstRun.outgoingUnblock,
        firstRun.schedules[scheduleId := C.ScheduleRec(nextRunAt, createdAt, true, firstRun.schedules[scheduleId].promiseTimeout)]);
    assert firstRun.schedules[scheduleId].promiseTimeout == created.schedules[scheduleId].promiseTimeout;
  }

  lemma ScheduleRunDuplicateInvocationIsObservationalNoOp(s: C.CoordinationState, scheduleId: C.Id, firstRunAt: nat, promiseTimeout: nat, promiseId: C.Id, createdAt: nat, timeoutAt: nat, nextRunAt: nat)
    requires C.Valid(s)
    requires nextRunAt > createdAt
    ensures C.ScheduleRun(
      C.ScheduleRun(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, promiseId, createdAt, timeoutAt, nextRunAt),
      scheduleId,
      promiseId,
      createdAt,
      timeoutAt,
      nextRunAt).core ==
      C.ScheduleRun(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, promiseId, createdAt, timeoutAt, nextRunAt).core
    ensures C.ScheduleRun(
      C.ScheduleRun(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, promiseId, createdAt, timeoutAt, nextRunAt),
      scheduleId,
      promiseId,
      createdAt,
      timeoutAt,
      nextRunAt).outgoingExec ==
      C.ScheduleRun(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, promiseId, createdAt, timeoutAt, nextRunAt).outgoingExec
    ensures C.ScheduleRun(
      C.ScheduleRun(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, promiseId, createdAt, timeoutAt, nextRunAt),
      scheduleId,
      promiseId,
      createdAt,
      timeoutAt,
      nextRunAt).outgoingUnblock ==
      C.ScheduleRun(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, promiseId, createdAt, timeoutAt, nextRunAt).outgoingUnblock
    ensures C.ScheduleRun(
      C.ScheduleRun(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, promiseId, createdAt, timeoutAt, nextRunAt),
      scheduleId,
      promiseId,
      createdAt,
      timeoutAt,
      nextRunAt).schedules ==
      C.ScheduleRun(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, promiseId, createdAt, timeoutAt, nextRunAt).schedules
  {
    ScheduleRunIsIdempotent(s, scheduleId, firstRunAt, promiseTimeout, promiseId, createdAt, timeoutAt, nextRunAt);
  }

  lemma ApplyScheduleRunPromisesContainsRun(core: Core.ResonateState, runs: seq<C.ScheduleRunRequest>, index: nat)
    requires index < |runs|
    ensures runs[index].promiseId in C.ApplyScheduleRunPromises(core, runs).promises
    decreases |runs|
  {
    if index == 0 {
      var inserted := C.InsertRunPromise(core, runs[0].promiseId, runs[0].timeoutAt, runs[0].createdAt);
      assert C.ApplyScheduleRunPromises(core, runs) == C.ApplyScheduleRunPromises(inserted, runs[1..]);
      assert runs[0].promiseId in inserted.promises;
      ApplyScheduleRunPromisesPreservesExistingPromise(inserted, runs[1..], runs[0].promiseId);
    } else {
      assert C.ApplyScheduleRunPromises(core, runs) == C.ApplyScheduleRunPromises(
        C.InsertRunPromise(core, runs[0].promiseId, runs[0].timeoutAt, runs[0].createdAt),
        runs[1..]);
      ApplyScheduleRunPromisesContainsRun(
        C.InsertRunPromise(core, runs[0].promiseId, runs[0].timeoutAt, runs[0].createdAt),
        runs[1..],
        index - 1);
    }
  }

  lemma ApplyScheduleRunPromisesPreservesExistingPromise(core: Core.ResonateState, runs: seq<C.ScheduleRunRequest>, promiseId: C.Id)
    requires promiseId in core.promises
    ensures promiseId in C.ApplyScheduleRunPromises(core, runs).promises
    decreases |runs|
  {
    if |runs| != 0 {
      var inserted := C.InsertRunPromise(core, runs[0].promiseId, runs[0].timeoutAt, runs[0].createdAt);
      assert promiseId in inserted.promises;
      ApplyScheduleRunPromisesPreservesExistingPromise(inserted, runs[1..], promiseId);
    }
  }

  function PlannerKernelRunRequests(scheduleId: C.Id, promiseTimeout: nat, runTimes: seq<nat>): seq<C.ScheduleRunRequest>
    decreases |runTimes|
  {
    if |runTimes| == 0 then []
    else ([C.ScheduleRunRequest(scheduleId + runTimes[0] + 1, runTimes[0], runTimes[0] + promiseTimeout)] +
      PlannerKernelRunRequests(scheduleId, promiseTimeout, runTimes[1..]))
  }

  lemma PlannerKernelRunRequestsAt(scheduleId: C.Id, promiseTimeout: nat, runTimes: seq<nat>, index: nat)
    requires index < |runTimes|
    ensures |PlannerKernelRunRequests(scheduleId, promiseTimeout, runTimes)| == |runTimes|
    ensures PlannerKernelRunRequests(scheduleId, promiseTimeout, runTimes)[index].createdAt == runTimes[index]
    ensures PlannerKernelRunRequests(scheduleId, promiseTimeout, runTimes)[index].timeoutAt == runTimes[index] + promiseTimeout
    decreases |runTimes|
  {
    if index == 0 {
    } else {
      PlannerKernelRunRequestsAt(scheduleId, promiseTimeout, runTimes[1..], index - 1);
    }
  }

  lemma PlannerKernelBoundaryImpliesExhaustedRunPrefix(scheduleId: C.Id, promiseTimeout: nat, now: nat, candidates: seq<nat>, runTimes: seq<nat>, finalNextRunAt: nat)
    requires K.ValidScheduleCandidateStream(now, candidates)
    requires K.ExhaustedDuePrefixBoundary(now, candidates, runTimes, finalNextRunAt)
    ensures C.ExhaustedRunPrefix(C.ScheduleRec(candidates[0], 0, false, promiseTimeout), now, PlannerKernelRunRequests(scheduleId, promiseTimeout, runTimes), finalNextRunAt)
  {
    assert |runTimes| > 0;
    PlannerKernelRunRequestsAt(scheduleId, promiseTimeout, runTimes, 0);
    assert PlannerKernelRunRequests(scheduleId, promiseTimeout, runTimes)[0].createdAt == runTimes[0];
    assert runTimes[0] == candidates[0];
    forall i: nat | i < |PlannerKernelRunRequests(scheduleId, promiseTimeout, runTimes)|
      ensures PlannerKernelRunRequests(scheduleId, promiseTimeout, runTimes)[i].createdAt <= now
    {
      PlannerKernelRunRequestsAt(scheduleId, promiseTimeout, runTimes, i);
    }
    forall i: nat | i + 1 < |PlannerKernelRunRequests(scheduleId, promiseTimeout, runTimes)|
      ensures PlannerKernelRunRequests(scheduleId, promiseTimeout, runTimes)[i].createdAt < PlannerKernelRunRequests(scheduleId, promiseTimeout, runTimes)[i + 1].createdAt
    {
      PlannerKernelRunRequestsAt(scheduleId, promiseTimeout, runTimes, i);
      PlannerKernelRunRequestsAt(scheduleId, promiseTimeout, runTimes, i + 1);
      assert runTimes[i] < runTimes[i + 1];
    }
  }

  lemma ExecutablePlannerRefinesExhaustedRunPrefix(scheduleId: C.Id, promiseTimeout: nat, now: nat, candidates: seq<nat>)
    requires K.ValidScheduleCandidateStream(now, candidates)
    ensures |K.PlannedRunTimes(now, candidates)| > 0
    ensures C.ExhaustedRunPrefix(
      C.ScheduleRec(candidates[0], 0, false, promiseTimeout),
      now,
      PlannerKernelRunRequests(scheduleId, promiseTimeout, K.PlannedRunTimes(now, candidates)),
      K.PlannedFinalNextRunAt(now, candidates))
  {
    K.ValidStreamPlannedBoundary(now, candidates);
    PlannerKernelBoundaryImpliesExhaustedRunPrefix(
      scheduleId,
      promiseTimeout,
      now,
      candidates,
      K.PlannedRunTimes(now, candidates),
      K.PlannedFinalNextRunAt(now, candidates));
  }

  lemma ScheduleRunBatchMaterializesRunsAndAdvancesSchedule(s: C.CoordinationState, scheduleId: C.Id, firstRunAt: nat, promiseTimeout: nat, runs: seq<C.ScheduleRunRequest>, finalNextRunAt: nat)
    requires C.Valid(s)
    requires |runs| > 0
    requires finalNextRunAt > runs[|runs| - 1].createdAt
    ensures C.ScheduleRunBatch(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, runs, finalNextRunAt).schedules[scheduleId].hasRun
    ensures C.ScheduleRunBatch(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, runs, finalNextRunAt).schedules[scheduleId].lastRunAt == runs[|runs| - 1].createdAt
    ensures C.ScheduleRunBatch(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, runs, finalNextRunAt).schedules[scheduleId].nextRunAt == finalNextRunAt
    ensures forall i: nat :: i < |runs| ==> runs[i].promiseId in C.ScheduleRunBatch(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, runs, finalNextRunAt).core.promises
  {
    var created := C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout);
    var batched := C.ScheduleRunBatch(created, scheduleId, runs, finalNextRunAt);
    assert batched.schedules[scheduleId].hasRun;
    assert batched.schedules[scheduleId].lastRunAt == runs[|runs| - 1].createdAt;
    assert batched.schedules[scheduleId].nextRunAt == finalNextRunAt;
    forall i: nat | i < |runs|
      ensures runs[i].promiseId in batched.core.promises
    {
      ApplyScheduleRunPromisesContainsRun(created.core, runs, i);
    }
  }

  lemma DueScheduleSelectionAndExhaustedPrefixAdvanceBatch(s: C.CoordinationState, scheduleId: C.Id, firstRunAt: nat, promiseTimeout: nat, now: nat, runs: seq<C.ScheduleRunRequest>, finalNextRunAt: nat)
    requires C.Valid(s)
    requires C.ExhaustedRunPrefix(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout).schedules[scheduleId], now, runs, finalNextRunAt)
    ensures scheduleId in C.DueSchedulesAt(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), now)
    ensures C.ScheduleRunBatch(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, runs, finalNextRunAt).schedules[scheduleId].hasRun
    ensures C.ScheduleRunBatch(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, runs, finalNextRunAt).schedules[scheduleId].lastRunAt == runs[|runs| - 1].createdAt
    ensures C.ScheduleRunBatch(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, runs, finalNextRunAt).schedules[scheduleId].nextRunAt == finalNextRunAt
    ensures forall i: nat :: i < |runs| ==> runs[i].promiseId in C.ScheduleRunBatch(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), scheduleId, runs, finalNextRunAt).core.promises
  {
    var created := C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout);
    assert scheduleId in created.schedules;
    assert created.schedules[scheduleId].nextRunAt == runs[0].createdAt;
    assert runs[0].createdAt <= now;
    assert scheduleId in C.DueSchedulesAt(created, now);
    assert finalNextRunAt > runs[|runs| - 1].createdAt;
    ScheduleRunBatchMaterializesRunsAndAdvancesSchedule(s, scheduleId, firstRunAt, promiseTimeout, runs, finalNextRunAt);
  }

  lemma ExecutablePlannerAdvanceBatchFromDueSchedule(s: C.CoordinationState, scheduleId: C.Id, firstRunAt: nat, promiseTimeout: nat, now: nat, candidates: seq<nat>) returns (runs: seq<C.ScheduleRunRequest>, finalNextRunAt: nat)
    requires C.Valid(s)
    requires scheduleId !in s.schedules
    requires K.ValidScheduleCandidateStream(now, candidates)
    requires candidates[0] == firstRunAt
    ensures |K.PlannedRunTimes(now, candidates)| > 0
    ensures runs == PlannerKernelRunRequests(scheduleId, promiseTimeout, K.PlannedRunTimes(now, candidates))
    ensures |runs| > 0
    ensures finalNextRunAt == K.PlannedFinalNextRunAt(now, candidates)
    ensures C.ExhaustedRunPrefix(
      C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout).schedules[scheduleId],
      now,
      runs,
      finalNextRunAt)
    ensures scheduleId in C.DueSchedulesAt(C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout), now)
    ensures C.ScheduleRunBatch(
      C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout),
      scheduleId,
      runs,
      finalNextRunAt).schedules[scheduleId].hasRun
    ensures C.ScheduleRunBatch(
      C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout),
      scheduleId,
      runs,
      finalNextRunAt).schedules[scheduleId].lastRunAt == runs[|runs| - 1].createdAt
    ensures C.ScheduleRunBatch(
      C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout),
      scheduleId,
      runs,
      finalNextRunAt).schedules[scheduleId].nextRunAt == finalNextRunAt
  {
    var created := C.ScheduleCreate(s, scheduleId, firstRunAt, promiseTimeout);
    runs := PlannerKernelRunRequests(scheduleId, promiseTimeout, K.PlannedRunTimes(now, candidates));
    finalNextRunAt := K.PlannedFinalNextRunAt(now, candidates);
    ExecutablePlannerRefinesExhaustedRunPrefix(scheduleId, promiseTimeout, now, candidates);
    assert created.schedules[scheduleId] == C.ScheduleRec(firstRunAt, 0, false, promiseTimeout);
    DueScheduleSelectionAndExhaustedPrefixAdvanceBatch(s, scheduleId, firstRunAt, promiseTimeout, now, runs, finalNextRunAt);
  }

  lemma TrustedSchedulePlannerInputAdvanceBatchFromDueSchedule(s: C.CoordinationState, scheduleId: C.Id, cron: string, promiseTimeout: nat, now: nat, candidates: seq<nat>) returns (runs: seq<C.ScheduleRunRequest>, finalNextRunAt: nat)
    requires C.Valid(s)
    requires scheduleId !in s.schedules
    requires |candidates| > 0
    requires C.TrustedSchedulePlannerInput(C.ScheduleRec(candidates[0], 0, false, promiseTimeout), cron, now, candidates)
    ensures runs == PlannerKernelRunRequests(scheduleId, promiseTimeout, K.PlannedRunTimes(now, candidates))
    ensures |runs| > 0
    ensures finalNextRunAt == K.PlannedFinalNextRunAt(now, candidates)
    ensures C.ExhaustedRunPrefix(
      C.ScheduleCreate(s, scheduleId, candidates[0], promiseTimeout).schedules[scheduleId],
      now,
      runs,
      finalNextRunAt)
    ensures scheduleId in C.DueSchedulesAt(C.ScheduleCreate(s, scheduleId, candidates[0], promiseTimeout), now)
    ensures C.ScheduleRunBatch(
      C.ScheduleCreate(s, scheduleId, candidates[0], promiseTimeout),
      scheduleId,
      runs,
      finalNextRunAt).schedules[scheduleId].hasRun
    ensures C.ScheduleRunBatch(
      C.ScheduleCreate(s, scheduleId, candidates[0], promiseTimeout),
      scheduleId,
      runs,
      finalNextRunAt).schedules[scheduleId].lastRunAt == runs[|runs| - 1].createdAt
    ensures C.ScheduleRunBatch(
      C.ScheduleCreate(s, scheduleId, candidates[0], promiseTimeout),
      scheduleId,
      runs,
      finalNextRunAt).schedules[scheduleId].nextRunAt == finalNextRunAt
  {
    K.TrustedCronCandidateStreamIsValid(now, candidates[0], candidates);
    runs, finalNextRunAt := ExecutablePlannerAdvanceBatchFromDueSchedule(s, scheduleId, candidates[0], promiseTimeout, now, candidates);
  }

  lemma ExecutableTimeoutKernelPreservesPhaseOrder(s: TK.TimeoutBatchState, expiredPromises: seq<C.Id>, readyAwaiters: seq<C.Id>, expiredRetries: seq<C.Id>, expiredLeases: seq<C.Id>)
    ensures TK.ProcessTimeoutBatch(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases) ==
            TK.TimeoutStatement3(TK.TimeoutStatement2(TK.TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries), expiredLeases)
  {
  }

  lemma ExecutableRetryTimeoutRowsRefineAbstractLaw(s: TK.TimeoutBatchState, rows: TK.TimeoutRows, id: C.Id, now: nat, retryDelay: nat)
    ensures TimeoutKernelRows(TK.ExpireRetryTimeoutRows(s, rows, id, now, retryDelay)) ==
            C.ExpireRetryTimeoutRows(TimeoutKernelState(s, rows), TimeoutKernelRows(rows), id, now, retryDelay)
  {
  }

  lemma ExecutableLeaseTimeoutRowsRefineAbstractLaw(s: TK.TimeoutBatchState, rows: TK.TimeoutRows, id: C.Id, now: nat, retryDelay: nat)
    ensures TimeoutKernelRows(TK.ExpireLeaseTimeoutRows(s, rows, id, now, retryDelay)) ==
            C.ExpireLeaseTimeoutRows(TimeoutKernelState(s, rows), TimeoutKernelRows(rows), id, now, retryDelay)
  {
  }

  lemma ExecutableStatement1ReadyAwaiterRefinesAbstractLaw(s: TK.TimeoutBatchState, rows: TK.TimeoutRows, awaiter: C.Id, now: nat, retryDelay: nat)
    ensures TimeoutKernelState(TK.ResumeReadyAwaiter(s, awaiter), TK.ResumeReadyAwaiterRows(s, rows, awaiter, now, retryDelay)).outgoingExec ==
            C.ResumeReadyAwaiter(TimeoutKernelState(s, rows), awaiter).outgoingExec
    ensures TimeoutKernelRows(TK.ResumeReadyAwaiterRows(s, rows, awaiter, now, retryDelay)) ==
            C.ResumeReadyAwaiterRows(TimeoutKernelState(s, rows), TimeoutKernelRows(rows), awaiter, now, retryDelay)
  {
    TimeoutKernelHasReadyCallbackMatchesModel(s, rows, awaiter);
    if awaiter !in s.tasks || s.tasks[awaiter].state != TK.Suspended || !TK.HasReadyCallbackFor(s, awaiter) {
      assert TK.ResumeReadyAwaiter(s, awaiter) == s;
      assert TK.ResumeReadyAwaiterRows(s, rows, awaiter, now, retryDelay) == rows;
      assert C.ResumeReadyAwaiter(TimeoutKernelState(s, rows), awaiter) == TimeoutKernelState(s, rows);
      assert C.ResumeReadyAwaiterRows(TimeoutKernelState(s, rows), TimeoutKernelRows(rows), awaiter, now, retryDelay) == TimeoutKernelRows(rows);
    } else {
      assert TK.ResumeReadyAwaiter(s, awaiter).outgoingExec == s.outgoingExec[awaiter := s.tasks[awaiter].version + 1];
      assert C.ResumeReadyAwaiter(TimeoutKernelState(s, rows), awaiter).outgoingExec == TimeoutKernelState(s, rows).outgoingExec[awaiter := TimeoutKernelState(s, rows).core.tasks[awaiter].version + 1];
      assert TimeoutKernelState(s, rows).core.tasks[awaiter].version == s.tasks[awaiter].version;
      assert TK.ResumeReadyAwaiterRows(s, rows, awaiter, now, retryDelay) == TK.TimeoutRowsRec(rows.retryAt[awaiter := now + retryDelay], rows.leaseAt - {awaiter});
      assert C.ResumeReadyAwaiterRows(TimeoutKernelState(s, rows), TimeoutKernelRows(rows), awaiter, now, retryDelay) == C.TimeoutRowsRec(rows.retryAt[awaiter := now + retryDelay], rows.leaseAt - {awaiter});
    }
  }

  lemma ExecutableStatement1ListenerUnblockRefinesAbstractLaw(s: TK.TimeoutBatchState, rows: TK.TimeoutRows, id: C.Id)
    ensures TimeoutKernelState(TK.ExpirePromiseTimeout(s, id), TK.ExpirePromiseTimeoutRows(s, rows, id)).outgoingUnblock ==
            C.ExpirePromiseTimeout(TimeoutKernelState(s, rows), id).outgoingUnblock
  {
    if id !in s.promises || s.promises[id].state != TK.Pending {
      assert TK.ExpirePromiseTimeout(s, id) == s;
      assert C.ExpirePromiseTimeout(TimeoutKernelState(s, rows), id) == TimeoutKernelState(s, rows);
    } else {
      assert TK.ExpirePromiseTimeout(s, id).outgoingUnblock == s.outgoingUnblock + TK.ListenersFor(s.listeners, id);
      assert C.ExpirePromiseTimeout(TimeoutKernelState(s, rows), id).outgoingUnblock == TimeoutKernelState(s, rows).outgoingUnblock + C.ListenersFor(TimeoutKernelState(s, rows).listeners, id);
      assert TimeoutKernelListeners(TK.ListenersFor(s.listeners, id)) == C.ListenersFor(TimeoutKernelState(s, rows).listeners, id);
    }
  }

  lemma ExecutableScheduleCreateMatchesBoundary(firstRunAt: nat, promiseTimeout: nat)
    ensures RK.ScheduleCreate(firstRunAt, promiseTimeout) == RK.ScheduleRec(firstRunAt, 0, false, promiseTimeout)
  {
  }

  lemma ExecutableScheduleAdvanceMatchesBoundary(nextRunAt: nat, lastRunAt: nat, hasRun: bool, promiseTimeout: nat, runTimes: seq<nat>, finalNextRunAt: nat)
    requires RK.ValidScheduleAdvanceInput(RK.ScheduleRec(nextRunAt, lastRunAt, hasRun, promiseTimeout), runTimes, finalNextRunAt)
    ensures RK.ScheduleAdvance(RK.ScheduleRec(nextRunAt, lastRunAt, hasRun, promiseTimeout), runTimes, finalNextRunAt).hasRun
    ensures RK.ScheduleAdvance(RK.ScheduleRec(nextRunAt, lastRunAt, hasRun, promiseTimeout), runTimes, finalNextRunAt).lastRunAt == runTimes[|runTimes| - 1]
    ensures RK.ScheduleAdvance(RK.ScheduleRec(nextRunAt, lastRunAt, hasRun, promiseTimeout), runTimes, finalNextRunAt).nextRunAt == finalNextRunAt
  {
  }
}
