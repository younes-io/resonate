module TimeoutBatchKernel {
  datatype PromiseState = Pending | Resolved | Rejected | RejectedCanceled | RejectedTimedout
  datatype TaskState = TaskPending | Acquired | Suspended | Halted | Fulfilled
  datatype PromiseRec = PromiseRec(state: PromiseState, timer: bool, timeoutAt: nat)
  datatype TaskRec = TaskRec(state: TaskState, version: nat)
  datatype CallbackKey = CallbackKey(awaited: nat, awaiter: nat)
  datatype ListenerKey = ListenerKey(promise: nat, address: nat)
  datatype TimeoutRows = TimeoutRowsRec(retryAt: map<nat, nat>, leaseAt: map<nat, nat>)
  datatype TimeoutBatchState = State(
    promises: map<nat, PromiseRec>,
    tasks: map<nat, TaskRec>,
    promiseTimeouts: set<nat>,
    callbacks: set<CallbackKey>,
    readyCallbacks: set<CallbackKey>,
    listeners: set<ListenerKey>,
    outgoingExec: map<nat, nat>,
    outgoingUnblock: set<ListenerKey>)

  function CallbacksByAwaiter(callbacks: set<CallbackKey>, awaiter: nat): set<CallbackKey> {
    set cb: CallbackKey | cb in callbacks && cb.awaiter == awaiter
  }

  function CallbacksByAwaited(callbacks: set<CallbackKey>, awaited: nat): set<CallbackKey> {
    set cb: CallbackKey | cb in callbacks && cb.awaited == awaited
  }

  function ListenersFor(listeners: set<ListenerKey>, promise: nat): set<ListenerKey> {
    set listener: ListenerKey | listener in listeners && listener.promise == promise
  }

  predicate HasReadyCallbackFor(s: TimeoutBatchState, awaiter: nat) {
    exists cb: CallbackKey :: cb in s.readyCallbacks && cb.awaiter == awaiter
  }

  function TimeoutSettlementState(s: TimeoutBatchState, id: nat): PromiseState
    requires id in s.promises
  {
    if s.promises[id].timer then Resolved else RejectedTimedout
  }

  function ResumeSuspendedTask(s: TimeoutBatchState, awaiter: nat): TimeoutBatchState {
    if awaiter !in s.tasks || s.tasks[awaiter].state != Suspended then s
    else
      State(
        s.promises,
        s.tasks[awaiter := TaskRec(TaskPending, s.tasks[awaiter].version + 1)],
        s.promiseTimeouts,
        s.callbacks,
        s.readyCallbacks,
        s.listeners,
        s.outgoingExec,
        s.outgoingUnblock)
  }

  function SettlePromise(s: TimeoutBatchState, id: nat, newState: PromiseState): TimeoutBatchState {
    if id !in s.promises || s.promises[id].state != Pending || newState == Pending then s
    else
      var nextTaskState :=
        if id in s.tasks then
          if s.tasks[id].state == Fulfilled then s.tasks[id] else TaskRec(Fulfilled, s.tasks[id].version)
        else TaskRec(TaskPending, 0);
      State(
        s.promises[id := PromiseRec(newState, s.promises[id].timer, s.promises[id].timeoutAt)],
        if id in s.tasks then s.tasks[id := nextTaskState] else s.tasks,
        s.promiseTimeouts - {id},
        s.callbacks - CallbacksByAwaiter(s.callbacks, id),
        s.readyCallbacks - CallbacksByAwaiter(s.readyCallbacks, id),
        s.listeners,
        s.outgoingExec,
        s.outgoingUnblock)
  }

  function SettleAndNotify(s: TimeoutBatchState, id: nat, newState: PromiseState): TimeoutBatchState {
    if id !in s.promises || s.promises[id].state != Pending || newState == Pending then s
    else
      var settled := SettlePromise(s, id, newState);
      State(
        settled.promises,
        settled.tasks,
        settled.promiseTimeouts,
        settled.callbacks,
        settled.readyCallbacks + (CallbacksByAwaited(s.callbacks, id) - CallbacksByAwaiter(s.callbacks, id)),
        s.listeners - ListenersFor(s.listeners, id),
        settled.outgoingExec,
        s.outgoingUnblock + ListenersFor(s.listeners, id))
  }

  function ResumeReadyAwaiter(s: TimeoutBatchState, awaiter: nat): TimeoutBatchState {
    if awaiter !in s.tasks || s.tasks[awaiter].state != Suspended || !HasReadyCallbackFor(s, awaiter) then s
    else
      var resumed := ResumeSuspendedTask(s, awaiter);
      State(
        resumed.promises,
        resumed.tasks,
        resumed.promiseTimeouts,
        resumed.callbacks,
        resumed.readyCallbacks,
        resumed.listeners,
        resumed.outgoingExec[awaiter := resumed.tasks[awaiter].version],
        resumed.outgoingUnblock)
  }

  function ExpirePromiseTimeout(s: TimeoutBatchState, id: nat): TimeoutBatchState {
    if id !in s.promises || s.promises[id].state != Pending then s
    else SettleAndNotify(s, id, TimeoutSettlementState(s, id))
  }

  function ExpireRetryTimeout(s: TimeoutBatchState, id: nat): TimeoutBatchState {
    if id !in s.tasks || s.tasks[id].state != TaskPending then s
    else if id !in s.outgoingExec then
      State(
        s.promises,
        s.tasks,
        s.promiseTimeouts,
        s.callbacks,
        s.readyCallbacks,
        s.listeners,
        s.outgoingExec[id := s.tasks[id].version],
        s.outgoingUnblock)
    else State(s.promises, s.tasks, s.promiseTimeouts, s.callbacks, s.readyCallbacks, s.listeners, s.outgoingExec[id := s.tasks[id].version], s.outgoingUnblock)
  }

  function ExpireLeaseTimeout(s: TimeoutBatchState, id: nat): TimeoutBatchState {
    if id !in s.tasks || s.tasks[id].state != Acquired then s
    else
      var releasedTasks := s.tasks[id := TaskRec(TaskPending, s.tasks[id].version + 1)];
      State(
        s.promises,
        releasedTasks,
        s.promiseTimeouts,
        s.callbacks,
        s.readyCallbacks,
        s.listeners,
        s.outgoingExec[id := releasedTasks[id].version],
        s.outgoingUnblock)
  }

  function ExpirePromiseTimeoutRows(s: TimeoutBatchState, rows: TimeoutRows, id: nat): TimeoutRows {
    if id !in s.promises || s.promises[id].state != Pending then rows
    else TimeoutRowsRec(rows.retryAt - {id}, rows.leaseAt - {id})
  }

  function ResumeReadyAwaiterRows(s: TimeoutBatchState, rows: TimeoutRows, awaiter: nat, now: nat, retryDelay: nat): TimeoutRows {
    if awaiter !in s.tasks || s.tasks[awaiter].state != Suspended || !HasReadyCallbackFor(s, awaiter) then rows
    else TimeoutRowsRec(rows.retryAt[awaiter := now + retryDelay], rows.leaseAt - {awaiter})
  }

  function ExpireRetryTimeoutRows(s: TimeoutBatchState, rows: TimeoutRows, id: nat, now: nat, retryDelay: nat): TimeoutRows {
    if id !in rows.retryAt || id !in s.tasks || s.tasks[id].state != TaskPending || rows.retryAt[id] > now then rows
    else TimeoutRowsRec(rows.retryAt[id := now + retryDelay], rows.leaseAt)
  }

  function ExpireLeaseTimeoutRows(s: TimeoutBatchState, rows: TimeoutRows, id: nat, now: nat, retryDelay: nat): TimeoutRows {
    if id !in rows.leaseAt || id !in s.tasks || s.tasks[id].state != Acquired || rows.leaseAt[id] > now then rows
    else TimeoutRowsRec(rows.retryAt[id := now + retryDelay], rows.leaseAt - {id})
  }

  function ApplyPromiseTimeouts(s: TimeoutBatchState, expired: seq<nat>): TimeoutBatchState
    decreases |expired|
  {
    if |expired| == 0 then s
    else ApplyPromiseTimeouts(ExpirePromiseTimeout(s, expired[0]), expired[1..])
  }

  function ResumeReadyAwaiters(s: TimeoutBatchState, ready: seq<nat>): TimeoutBatchState
    decreases |ready|
  {
    if |ready| == 0 then s
    else ResumeReadyAwaiters(ResumeReadyAwaiter(s, ready[0]), ready[1..])
  }

  function ApplyRetryTimeouts(s: TimeoutBatchState, expired: seq<nat>): TimeoutBatchState
    decreases |expired|
  {
    if |expired| == 0 then s
    else ApplyRetryTimeouts(ExpireRetryTimeout(s, expired[0]), expired[1..])
  }

  function ApplyLeaseTimeouts(s: TimeoutBatchState, expired: seq<nat>): TimeoutBatchState
    decreases |expired|
  {
    if |expired| == 0 then s
    else ApplyLeaseTimeouts(ExpireLeaseTimeout(s, expired[0]), expired[1..])
  }

  function ApplyPromiseTimeoutRows(s: TimeoutBatchState, rows: TimeoutRows, expired: seq<nat>): TimeoutRows
    decreases |expired|
  {
    if |expired| == 0 then rows
    else ApplyPromiseTimeoutRows(ExpirePromiseTimeout(s, expired[0]), ExpirePromiseTimeoutRows(s, rows, expired[0]), expired[1..])
  }

  function ResumeReadyAwaitersRows(s: TimeoutBatchState, rows: TimeoutRows, ready: seq<nat>, now: nat, retryDelay: nat): TimeoutRows
    decreases |ready|
  {
    if |ready| == 0 then rows
    else ResumeReadyAwaitersRows(ResumeReadyAwaiter(s, ready[0]), ResumeReadyAwaiterRows(s, rows, ready[0], now, retryDelay), ready[1..], now, retryDelay)
  }

  function ApplyRetryTimeoutRows(s: TimeoutBatchState, rows: TimeoutRows, expired: seq<nat>, now: nat, retryDelay: nat): TimeoutRows
    decreases |expired|
  {
    if |expired| == 0 then rows
    else ApplyRetryTimeoutRows(ExpireRetryTimeout(s, expired[0]), ExpireRetryTimeoutRows(s, rows, expired[0], now, retryDelay), expired[1..], now, retryDelay)
  }

  function ApplyLeaseTimeoutRows(s: TimeoutBatchState, rows: TimeoutRows, expired: seq<nat>, now: nat, retryDelay: nat): TimeoutRows
    decreases |expired|
  {
    if |expired| == 0 then rows
    else ApplyLeaseTimeoutRows(ExpireLeaseTimeout(s, expired[0]), ExpireLeaseTimeoutRows(s, rows, expired[0], now, retryDelay), expired[1..], now, retryDelay)
  }

  function TimeoutStatement1(s: TimeoutBatchState, expiredPromises: seq<nat>, readyAwaiters: seq<nat>): TimeoutBatchState {
    ResumeReadyAwaiters(ApplyPromiseTimeouts(s, expiredPromises), readyAwaiters)
  }

  function TimeoutStatement2(s: TimeoutBatchState, expiredRetries: seq<nat>): TimeoutBatchState {
    ApplyRetryTimeouts(s, expiredRetries)
  }

  function TimeoutStatement3(s: TimeoutBatchState, expiredLeases: seq<nat>): TimeoutBatchState {
    ApplyLeaseTimeouts(s, expiredLeases)
  }

  function TimeoutRowsAfterStatement1(s: TimeoutBatchState, rows: TimeoutRows, expiredPromises: seq<nat>, readyAwaiters: seq<nat>, now: nat, retryDelay: nat): TimeoutRows {
    var settledRows := ApplyPromiseTimeoutRows(s, rows, expiredPromises);
    var settledState := ApplyPromiseTimeouts(s, expiredPromises);
    ResumeReadyAwaitersRows(settledState, settledRows, readyAwaiters, now, retryDelay)
  }

  function TimeoutRowsAfterStatement2(s: TimeoutBatchState, rows: TimeoutRows, expiredPromises: seq<nat>, readyAwaiters: seq<nat>, expiredRetries: seq<nat>, now: nat, retryDelay: nat): TimeoutRows {
    var after1State := TimeoutStatement1(s, expiredPromises, readyAwaiters);
    var after1Rows := TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay);
    ApplyRetryTimeoutRows(after1State, after1Rows, expiredRetries, now, retryDelay)
  }

  function TimeoutRowsAfterStatement3(s: TimeoutBatchState, rows: TimeoutRows, expiredPromises: seq<nat>, readyAwaiters: seq<nat>, expiredRetries: seq<nat>, expiredLeases: seq<nat>, now: nat, retryDelay: nat): TimeoutRows {
    var after2State := TimeoutStatement2(TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries);
    var after2Rows := TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay);
    ApplyLeaseTimeoutRows(after2State, after2Rows, expiredLeases, now, retryDelay)
  }

  function ProcessTimeoutBatch(s: TimeoutBatchState, expiredPromises: seq<nat>, readyAwaiters: seq<nat>, expiredRetries: seq<nat>, expiredLeases: seq<nat>): TimeoutBatchState {
    var settled := ApplyPromiseTimeouts(s, expiredPromises);
    var resumed := ResumeReadyAwaiters(settled, readyAwaiters);
    var retried := ApplyRetryTimeouts(resumed, expiredRetries);
    ApplyLeaseTimeouts(retried, expiredLeases)
  }

  function OrderedExpiredPromises(promiseIds: seq<nat>, s: TimeoutBatchState, now: nat): seq<nat>
    decreases |promiseIds|
  {
    if |promiseIds| == 0 then []
    else if promiseIds[0] in s.promises && s.promises[promiseIds[0]].state == Pending && s.promises[promiseIds[0]].timeoutAt <= now
      then [promiseIds[0]] + OrderedExpiredPromises(promiseIds[1..], s, now)
      else OrderedExpiredPromises(promiseIds[1..], s, now)
  }

  function OrderedReadyAwaiters(taskIds: seq<nat>, s: TimeoutBatchState): seq<nat>
    decreases |taskIds|
  {
    if |taskIds| == 0 then []
    else if taskIds[0] in s.tasks && s.tasks[taskIds[0]].state == Suspended && HasReadyCallbackFor(s, taskIds[0])
      then [taskIds[0]] + OrderedReadyAwaiters(taskIds[1..], s)
      else OrderedReadyAwaiters(taskIds[1..], s)
  }

  function OrderedExpiredRetries(taskIds: seq<nat>, s: TimeoutBatchState, rows: TimeoutRows, now: nat): seq<nat>
    decreases |taskIds|
  {
    if |taskIds| == 0 then []
    else if taskIds[0] in rows.retryAt && taskIds[0] in s.tasks && s.tasks[taskIds[0]].state == TaskPending && rows.retryAt[taskIds[0]] <= now
      then [taskIds[0]] + OrderedExpiredRetries(taskIds[1..], s, rows, now)
      else OrderedExpiredRetries(taskIds[1..], s, rows, now)
  }

  function OrderedExpiredLeases(taskIds: seq<nat>, s: TimeoutBatchState, rows: TimeoutRows, now: nat): seq<nat>
    decreases |taskIds|
  {
    if |taskIds| == 0 then []
    else if taskIds[0] in rows.leaseAt && taskIds[0] in s.tasks && s.tasks[taskIds[0]].state == Acquired && rows.leaseAt[taskIds[0]] <= now
      then [taskIds[0]] + OrderedExpiredLeases(taskIds[1..], s, rows, now)
      else OrderedExpiredLeases(taskIds[1..], s, rows, now)
  }

  function PlannedPostState(s: TimeoutBatchState, rows: TimeoutRows, promiseIds: seq<nat>, taskIds: seq<nat>, now: nat, retryDelay: nat): TimeoutBatchState {
    var expiredPromises := OrderedExpiredPromises(promiseIds, s, now);
    var after1 := ApplyPromiseTimeouts(s, expiredPromises);
    var readyAwaiters := OrderedReadyAwaiters(taskIds, after1);
    var after1Full := ResumeReadyAwaiters(after1, readyAwaiters);
    var after1Rows := TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay);
    var expiredRetries := OrderedExpiredRetries(taskIds, after1Full, after1Rows, now);
    var after2 := ApplyRetryTimeouts(after1Full, expiredRetries);
    var after2Rows := TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay);
    var expiredLeases := OrderedExpiredLeases(taskIds, after2, after2Rows, now);
    ProcessTimeoutBatch(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases)
  }

  function PlannedPostRows(s: TimeoutBatchState, rows: TimeoutRows, promiseIds: seq<nat>, taskIds: seq<nat>, now: nat, retryDelay: nat): TimeoutRows {
    var expiredPromises := OrderedExpiredPromises(promiseIds, s, now);
    var after1 := ApplyPromiseTimeouts(s, expiredPromises);
    var readyAwaiters := OrderedReadyAwaiters(taskIds, after1);
    var after1Full := ResumeReadyAwaiters(after1, readyAwaiters);
    var after1Rows := TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay);
    var expiredRetries := OrderedExpiredRetries(taskIds, after1Full, after1Rows, now);
    var after2 := ApplyRetryTimeouts(after1Full, expiredRetries);
    var after2Rows := TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay);
    var expiredLeases := OrderedExpiredLeases(taskIds, after2, after2Rows, now);
    TimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, expiredLeases, now, retryDelay)
  }

  method PlanTimeoutBatch(s: TimeoutBatchState, rows: TimeoutRows, promiseIds: seq<nat>, taskIds: seq<nat>, now: nat, retryDelay: nat) returns (postState: TimeoutBatchState, postRows: TimeoutRows)
    ensures postState == PlannedPostState(s, rows, promiseIds, taskIds, now, retryDelay)
    ensures postRows == PlannedPostRows(s, rows, promiseIds, taskIds, now, retryDelay)
  {
    var expiredPromises := OrderedExpiredPromises(promiseIds, s, now);
    var settled := ApplyPromiseTimeouts(s, expiredPromises);
    var readyAwaiters := OrderedReadyAwaiters(taskIds, settled);
    var resumed := ResumeReadyAwaiters(settled, readyAwaiters);
    var after1Rows := TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay);
    var expiredRetries := OrderedExpiredRetries(taskIds, resumed, after1Rows, now);
    var retried := ApplyRetryTimeouts(resumed, expiredRetries);
    var after2Rows := TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay);
    var expiredLeases := OrderedExpiredLeases(taskIds, retried, after2Rows, now);
    postState := ProcessTimeoutBatch(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases);
    postRows := TimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, expiredLeases, now, retryDelay);
  }

  function PromiseStateCode(state: PromiseState): nat {
    match state
    case Pending => 0
    case Resolved => 1
    case Rejected => 2
    case RejectedCanceled => 3
    case RejectedTimedout => 4
  }

  function TaskStateCode(state: TaskState): nat {
    match state
    case TaskPending => 0
    case Acquired => 1
    case Suspended => 2
    case Halted => 3
    case Fulfilled => 4
  }

  function ParsePromiseStateCode(code: nat): PromiseState {
    if code == 0 then Pending
    else if code == 1 then Resolved
    else if code == 2 then Rejected
    else if code == 3 then RejectedCanceled
    else RejectedTimedout
  }

  function ParseTaskStateCode(code: nat): TaskState {
    if code == 0 then TaskPending
    else if code == 1 then Acquired
    else if code == 2 then Suspended
    else if code == 3 then Halted
    else Fulfilled
  }

  method ParseNat(s: string) returns (ok: bool, value: nat)
  {
    ok := |s| > 0;
    value := 0;
    if !ok {
      return;
    }
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant ok
    {
      var c := s[i];
      if c < '0' || c > '9' {
        ok := false;
        return;
      }
      value := value * 10 + (((c as int) - ('0' as int)) as nat);
      i := i + 1;
    }
  }

  method ParseBoolCode(s: string) returns (ok: bool, value: bool)
  {
    var parsedOk, parsed := ParseNat(s);
    ok := parsedOk && (parsed == 0 || parsed == 1);
    value := parsed == 1;
  }

  method PrintBoolCode(value: bool)
  {
    if value {
      print "1\n";
    } else {
      print "0\n";
    }
  }

  method Main(args: seq<string>) {
    if |args| < 9 {
      print "ERR\n";
      return;
    }

    var start := 0;
    var command := args[0];
    if command != "timeout-batch" && |args| > 1 {
      start := 1;
      command := args[1];
    }
    if command != "timeout-batch" {
      print "ERR\n";
      return;
    }

    var okNow, now := ParseNat(args[start + 1]);
    var okRetryDelay, retryDelay := ParseNat(args[start + 2]);
    var okPromiseCount, promiseCount := ParseNat(args[start + 3]);
    if !(okNow && okRetryDelay && okPromiseCount) {
      print "ERR\n";
      return;
    }

    var i := start + 4;
    var promiseIds: seq<nat> := [];
    var promises: map<nat, PromiseRec> := map[];
    var promiseTimeouts: set<nat> := {};
    var parsedPromises := 0;
    while parsedPromises < promiseCount
      invariant start + 4 <= i <= |args|
      invariant parsedPromises <= promiseCount
      invariant |promiseIds| == parsedPromises
    {
      if i + 4 >= |args| {
        print "ERR\n";
        return;
      }
      var okId, id := ParseNat(args[i]);
      var okState, stateCode := ParseNat(args[i + 1]);
      var okTimer, timer := ParseBoolCode(args[i + 2]);
      var okTimeoutAt, timeoutAt := ParseNat(args[i + 3]);
      var okHasPromiseTimeout, hasPromiseTimeout := ParseBoolCode(args[i + 4]);
      if !(okId && okState && okTimer && okTimeoutAt && okHasPromiseTimeout) {
        print "ERR\n";
        return;
      }
      promises := promises[id := PromiseRec(ParsePromiseStateCode(stateCode), timer, timeoutAt)];
      promiseIds := promiseIds + [id];
      if hasPromiseTimeout {
        promiseTimeouts := promiseTimeouts + {id};
      }
      parsedPromises := parsedPromises + 1;
      i := i + 5;
    }

    if i >= |args| {
      print "ERR\n";
      return;
    }
    var okTaskCount, taskCount := ParseNat(args[i]);
    if !okTaskCount {
      print "ERR\n";
      return;
    }
    i := i + 1;
    var taskIds: seq<nat> := [];
    var tasks: map<nat, TaskRec> := map[];
    while |taskIds| < taskCount
      invariant 0 <= |taskIds| <= taskCount
    {
      if i + 2 >= |args| {
        print "ERR\n";
        return;
      }
      var okId, id := ParseNat(args[i]);
      var okState, stateCode := ParseNat(args[i + 1]);
      var okVersion, version := ParseNat(args[i + 2]);
      if !(okId && okState && okVersion) {
        print "ERR\n";
        return;
      }
      tasks := tasks[id := TaskRec(ParseTaskStateCode(stateCode), version)];
      taskIds := taskIds + [id];
      i := i + 3;
    }

    if i >= |args| {
      print "ERR\n";
      return;
    }
    var okCallbackCount, callbackCount := ParseNat(args[i]);
    if !okCallbackCount {
      print "ERR\n";
      return;
    }
    i := i + 1;
    var callbacks: set<CallbackKey> := {};
    var readyCallbacks: set<CallbackKey> := {};
    var callbackDomain: seq<CallbackKey> := [];
    while |callbackDomain| < callbackCount
      invariant 0 <= |callbackDomain| <= callbackCount
    {
      if i + 2 >= |args| {
        print "ERR\n";
        return;
      }
      var okAwaited, awaited := ParseNat(args[i]);
      var okAwaiter, awaiter := ParseNat(args[i + 1]);
      var okReady, ready := ParseBoolCode(args[i + 2]);
      if !(okAwaited && okAwaiter && okReady) {
        print "ERR\n";
        return;
      }
      var key := CallbackKey(awaited, awaiter);
      callbacks := callbacks + {key};
      if ready {
        readyCallbacks := readyCallbacks + {key};
      }
      callbackDomain := callbackDomain + [key];
      i := i + 3;
    }

    if i >= |args| {
      print "ERR\n";
      return;
    }
    var okListenerCount, listenerCount := ParseNat(args[i]);
    if !okListenerCount {
      print "ERR\n";
      return;
    }
    i := i + 1;
    var listeners: set<ListenerKey> := {};
    var listenerDomain: seq<ListenerKey> := [];
    while |listenerDomain| < listenerCount
      invariant 0 <= |listenerDomain| <= listenerCount
    {
      if i + 1 >= |args| {
        print "ERR\n";
        return;
      }
      var okPromise, promise := ParseNat(args[i]);
      var okAddress, address := ParseNat(args[i + 1]);
      if !(okPromise && okAddress) {
        print "ERR\n";
        return;
      }
      var key := ListenerKey(promise, address);
      listeners := listeners + {key};
      listenerDomain := listenerDomain + [key];
      i := i + 2;
    }

    if i >= |args| {
      print "ERR\n";
      return;
    }
    var okOutgoingExecCount, outgoingExecCount := ParseNat(args[i]);
    if !okOutgoingExecCount {
      print "ERR\n";
      return;
    }
    i := i + 1;
    var outgoingExec: map<nat, nat> := map[];
    var parsedOutgoingExec := 0;
    while parsedOutgoingExec < outgoingExecCount
      invariant parsedOutgoingExec <= outgoingExecCount
    {
      if i + 1 >= |args| {
        print "ERR\n";
        return;
      }
      var okId, id := ParseNat(args[i]);
      var okVersion, version := ParseNat(args[i + 1]);
      if !(okId && okVersion) {
        print "ERR\n";
        return;
      }
      outgoingExec := outgoingExec[id := version];
      parsedOutgoingExec := parsedOutgoingExec + 1;
      i := i + 2;
    }

    if i >= |args| {
      print "ERR\n";
      return;
    }
    var okOutgoingUnblockCount, outgoingUnblockCount := ParseNat(args[i]);
    if !okOutgoingUnblockCount {
      print "ERR\n";
      return;
    }
    i := i + 1;
    var outgoingUnblock: set<ListenerKey> := {};
    var outgoingUnblockDomain: seq<ListenerKey> := [];
    while |outgoingUnblockDomain| < outgoingUnblockCount
      invariant 0 <= |outgoingUnblockDomain| <= outgoingUnblockCount
    {
      if i + 1 >= |args| {
        print "ERR\n";
        return;
      }
      var okPromise, promise := ParseNat(args[i]);
      var okAddress, address := ParseNat(args[i + 1]);
      if !(okPromise && okAddress) {
        print "ERR\n";
        return;
      }
      var key := ListenerKey(promise, address);
      outgoingUnblock := outgoingUnblock + {key};
      outgoingUnblockDomain := outgoingUnblockDomain + [key];
      i := i + 2;
    }

    if i >= |args| {
      print "ERR\n";
      return;
    }
    var okRetryCount, retryCount := ParseNat(args[i]);
    if !okRetryCount {
      print "ERR\n";
      return;
    }
    i := i + 1;
    var retryAt: map<nat, nat> := map[];
    var parsedRetry := 0;
    while parsedRetry < retryCount
      invariant parsedRetry <= retryCount
    {
      if i + 1 >= |args| {
        print "ERR\n";
        return;
      }
      var okId, id := ParseNat(args[i]);
      var okTimeout, timeoutAt := ParseNat(args[i + 1]);
      if !(okId && okTimeout) {
        print "ERR\n";
        return;
      }
      retryAt := retryAt[id := timeoutAt];
      parsedRetry := parsedRetry + 1;
      i := i + 2;
    }

    if i >= |args| {
      print "ERR\n";
      return;
    }
    var okLeaseCount, leaseCount := ParseNat(args[i]);
    if !okLeaseCount {
      print "ERR\n";
      return;
    }
    i := i + 1;
    var leaseAt: map<nat, nat> := map[];
    var parsedLease := 0;
    while parsedLease < leaseCount
      invariant parsedLease <= leaseCount
    {
      if i + 1 >= |args| {
        print "ERR\n";
        return;
      }
      var okId, id := ParseNat(args[i]);
      var okTimeout, timeoutAt := ParseNat(args[i + 1]);
      if !(okId && okTimeout) {
        print "ERR\n";
        return;
      }
      leaseAt := leaseAt[id := timeoutAt];
      parsedLease := parsedLease + 1;
      i := i + 2;
    }

    if i != |args| {
      print "ERR\n";
      return;
    }

    var state := State(promises, tasks, promiseTimeouts, callbacks, readyCallbacks, listeners, outgoingExec, outgoingUnblock);
    var rows := TimeoutRowsRec(retryAt, leaseAt);
    var postState, postRows := PlanTimeoutBatch(state, rows, promiseIds, taskIds, now, retryDelay);

    var promiseOutCount := 0;
    var j := 0;
    while j < |promiseIds|
      invariant 0 <= j <= |promiseIds|
    {
      if promiseIds[j] in postState.promises {
        promiseOutCount := promiseOutCount + 1;
      }
      j := j + 1;
    }
    print promiseOutCount, "\n";
    j := 0;
    while j < |promiseIds|
      invariant 0 <= j <= |promiseIds|
    {
      var id := promiseIds[j];
      if id in postState.promises {
        print id, "\n";
        print PromiseStateCode(postState.promises[id].state), "\n";
        PrintBoolCode(postState.promises[id].timer);
        print postState.promises[id].timeoutAt, "\n";
        PrintBoolCode(id in postState.promiseTimeouts);
      }
      j := j + 1;
    }

    var taskOutCount := 0;
    j := 0;
    while j < |taskIds|
      invariant 0 <= j <= |taskIds|
    {
      if taskIds[j] in postState.tasks {
        taskOutCount := taskOutCount + 1;
      }
      j := j + 1;
    }
    print taskOutCount, "\n";
    j := 0;
    while j < |taskIds|
      invariant 0 <= j <= |taskIds|
    {
      var id := taskIds[j];
      if id in postState.tasks {
        print id, "\n";
        print TaskStateCode(postState.tasks[id].state), "\n";
        print postState.tasks[id].version, "\n";
      }
      j := j + 1;
    }

    var callbackOutCount := 0;
    j := 0;
    while j < |callbackDomain|
      invariant 0 <= j <= |callbackDomain|
    {
      if callbackDomain[j] in postState.callbacks {
        callbackOutCount := callbackOutCount + 1;
      }
      j := j + 1;
    }
    print callbackOutCount, "\n";
    j := 0;
    while j < |callbackDomain|
      invariant 0 <= j <= |callbackDomain|
    {
      var cb := callbackDomain[j];
      if cb in postState.callbacks {
        print cb.awaited, "\n";
        print cb.awaiter, "\n";
        PrintBoolCode(cb in postState.readyCallbacks);
      }
      j := j + 1;
    }

    var listenerOutCount := 0;
    j := 0;
    while j < |listenerDomain|
      invariant 0 <= j <= |listenerDomain|
    {
      if listenerDomain[j] in postState.listeners {
        listenerOutCount := listenerOutCount + 1;
      }
      j := j + 1;
    }
    print listenerOutCount, "\n";
    j := 0;
    while j < |listenerDomain|
      invariant 0 <= j <= |listenerDomain|
    {
      var listener := listenerDomain[j];
      if listener in postState.listeners {
        print listener.promise, "\n";
        print listener.address, "\n";
      }
      j := j + 1;
    }

    var executeOutCount := 0;
    j := 0;
    while j < |taskIds|
      invariant 0 <= j <= |taskIds|
    {
      if taskIds[j] in postState.outgoingExec {
        executeOutCount := executeOutCount + 1;
      }
      j := j + 1;
    }
    print executeOutCount, "\n";
    j := 0;
    while j < |taskIds|
      invariant 0 <= j <= |taskIds|
    {
      var id := taskIds[j];
      if id in postState.outgoingExec {
        print id, "\n";
        print postState.outgoingExec[id], "\n";
      }
      j := j + 1;
    }

    var unblockOutCount := 0;
    j := 0;
    while j < |outgoingUnblockDomain|
      invariant 0 <= j <= |outgoingUnblockDomain|
    {
      if outgoingUnblockDomain[j] in postState.outgoingUnblock {
        unblockOutCount := unblockOutCount + 1;
      }
      j := j + 1;
    }
    var k := 0;
    while k < |listenerDomain|
      invariant 0 <= k <= |listenerDomain|
    {
      if listenerDomain[k] in postState.outgoingUnblock && listenerDomain[k] !in outgoingUnblock {
        unblockOutCount := unblockOutCount + 1;
      }
      k := k + 1;
    }
    print unblockOutCount, "\n";
    j := 0;
    while j < |outgoingUnblockDomain|
      invariant 0 <= j <= |outgoingUnblockDomain|
    {
      var listener := outgoingUnblockDomain[j];
      if listener in postState.outgoingUnblock {
        print listener.promise, "\n";
        print listener.address, "\n";
      }
      j := j + 1;
    }
    k := 0;
    while k < |listenerDomain|
      invariant 0 <= k <= |listenerDomain|
    {
      var listener := listenerDomain[k];
      if listener in postState.outgoingUnblock && listener !in outgoingUnblock {
        print listener.promise, "\n";
        print listener.address, "\n";
      }
      k := k + 1;
    }

    var retryOutCount := 0;
    j := 0;
    while j < |taskIds|
      invariant 0 <= j <= |taskIds|
    {
      if taskIds[j] in postRows.retryAt {
        retryOutCount := retryOutCount + 1;
      }
      j := j + 1;
    }
    print retryOutCount, "\n";
    j := 0;
    while j < |taskIds|
      invariant 0 <= j <= |taskIds|
    {
      var id := taskIds[j];
      if id in postRows.retryAt {
        print id, "\n";
        print postRows.retryAt[id], "\n";
      }
      j := j + 1;
    }

    var leaseOutCount := 0;
    j := 0;
    while j < |taskIds|
      invariant 0 <= j <= |taskIds|
    {
      if taskIds[j] in postRows.leaseAt {
        leaseOutCount := leaseOutCount + 1;
      }
      j := j + 1;
    }
    print leaseOutCount, "\n";
    j := 0;
    while j < |taskIds|
      invariant 0 <= j <= |taskIds|
    {
      var id := taskIds[j];
      if id in postRows.leaseAt {
        print id, "\n";
        print postRows.leaseAt[id], "\n";
      }
      j := j + 1;
    }
  }
}
