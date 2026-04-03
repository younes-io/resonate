include "ResonateModel.dfy"

module ResonateCoordinationModel {
  import Core = ResonateModel

  type Id = Core.Id
  type Address = nat

  datatype CallbackKey = CallbackKey(awaited: Id, awaiter: Id)
  datatype ListenerKey = ListenerKey(promise: Id, address: Address)
  datatype Schedule = ScheduleRec(nextRunAt: nat, lastRunAt: nat, hasRun: bool, promiseTimeout: nat)
  datatype ScheduleRunRequest = ScheduleRunRequest(promiseId: Id, createdAt: nat, timeoutAt: nat)
  datatype TimeoutRows = TimeoutRowsRec(retryAt: map<Id, nat>, leaseAt: map<Id, nat>)

  datatype CoordinationState = State(
    core: Core.ResonateState,
    callbacks: set<CallbackKey>,
    readyCallbacks: set<CallbackKey>,
    listeners: set<ListenerKey>,
    outgoingExec: map<Id, nat>,
    outgoingUnblock: set<ListenerKey>,
    schedules: map<Id, Schedule>
  )

  function EmptyState(): CoordinationState {
    State(Core.EmptyState(), {}, {}, {}, map[], {}, map[])
  }

  function EmptyTimeoutRows(): TimeoutRows {
    TimeoutRowsRec(map[], map[])
  }

  function CallbacksByAwaiter(callbacks: set<CallbackKey>, awaiter: Id): set<CallbackKey> {
    set cb: CallbackKey | cb in callbacks && cb.awaiter == awaiter
  }

  function CallbacksByAwaited(callbacks: set<CallbackKey>, awaited: Id): set<CallbackKey> {
    set cb: CallbackKey | cb in callbacks && cb.awaited == awaited
  }

  function ListenersFor(listeners: set<ListenerKey>, promise: Id): set<ListenerKey> {
    set listener: ListenerKey | listener in listeners && listener.promise == promise
  }

  function ReadyAwaiters(s: CoordinationState): set<Id> {
    set id: Id | id in s.core.tasks && s.core.tasks[id].state == Core.Suspended && HasReadyCallbackFor(s, id)
  }

  function ExpiredPromisesAt(s: CoordinationState, now: nat): set<Id> {
    set id: Id | id in s.core.promises && s.core.promises[id].state == Core.Pending && s.core.promises[id].timeoutAt <= now
  }

  function EligibleRetryTimeouts(s: CoordinationState): set<Id> {
    set id: Id | id in s.core.retryTimeouts && id in s.core.tasks && s.core.tasks[id].state == Core.TaskPending
  }

  function EligibleLeaseTimeouts(s: CoordinationState): set<Id> {
    set id: Id | id in s.core.leaseTimeouts && id in s.core.tasks && s.core.tasks[id].state == Core.Acquired
  }

  ghost predicate ValidTimeoutRows(s: CoordinationState, rows: TimeoutRows) {
    (forall id: Id :: id in rows.retryAt <==> id in s.core.retryTimeouts) &&
    (forall id: Id :: id in rows.leaseAt <==> id in s.core.leaseTimeouts)
  }

  function ExpiredRetryTimeoutRowsAt(s: CoordinationState, rows: TimeoutRows, now: nat): set<Id> {
    set id: Id | id in rows.retryAt && id in s.core.tasks && s.core.tasks[id].state == Core.TaskPending && rows.retryAt[id] <= now
  }

  function ExpiredLeaseTimeoutRowsAt(s: CoordinationState, rows: TimeoutRows, now: nat): set<Id> {
    set id: Id | id in rows.leaseAt && id in s.core.tasks && s.core.tasks[id].state == Core.Acquired && rows.leaseAt[id] <= now
  }

  function SqliteRetryTimeoutQuery(s: CoordinationState, rows: TimeoutRows, now: nat): set<Id> {
    ExpiredRetryTimeoutRowsAt(s, rows, now)
  }

  function SqliteLeaseTimeoutQuery(s: CoordinationState, rows: TimeoutRows, now: nat): set<Id> {
    ExpiredLeaseTimeoutRowsAt(s, rows, now)
  }

  function PostgresRetryTimeoutQuery(s: CoordinationState, rows: TimeoutRows, now: nat): set<Id> {
    ExpiredRetryTimeoutRowsAt(s, rows, now)
  }

  function PostgresLeaseTimeoutQuery(s: CoordinationState, rows: TimeoutRows, now: nat): set<Id> {
    ExpiredLeaseTimeoutRowsAt(s, rows, now)
  }

  predicate HasReadyCallbackFor(s: CoordinationState, awaiter: Id) {
    exists cb: CallbackKey :: cb in s.readyCallbacks && cb.awaiter == awaiter
  }

  predicate Valid(s: CoordinationState) {
    Core.Valid(s.core) &&
    s.readyCallbacks <= s.callbacks &&
    (forall cb: CallbackKey :: cb in s.callbacks ==>
      cb.awaited in s.core.promises &&
      cb.awaiter in s.core.promises &&
      cb.awaiter in s.core.tasks &&
      s.core.promises[cb.awaiter].state == Core.Pending &&
      s.core.tasks[cb.awaiter].state != Core.Fulfilled) &&
    (forall cb: CallbackKey :: cb in s.readyCallbacks ==> Core.PromiseTerminal(s.core.promises[cb.awaited].state)) &&
    (forall listener: ListenerKey :: listener in s.listeners ==>
      listener.promise in s.core.promises &&
      s.core.promises[listener.promise].state == Core.Pending) &&
    (forall id: Id :: id in s.outgoingExec ==> id in s.core.tasks) &&
    (forall listener: ListenerKey :: listener in s.outgoingUnblock ==>
      listener.promise in s.core.promises &&
      Core.PromiseTerminal(s.core.promises[listener.promise].state)) &&
    (forall scheduleId: Id :: scheduleId in s.schedules ==>
      s.schedules[scheduleId].hasRun ==> s.schedules[scheduleId].lastRunAt < s.schedules[scheduleId].nextRunAt)
  }

  function ResumeSuspendedTask(core: Core.ResonateState, awaiter: Id): Core.ResonateState {
    if awaiter !in core.tasks || core.tasks[awaiter].state != Core.Suspended then core
    else
      Core.State(
        core.promises,
        core.tasks[awaiter := Core.TaskRec(Core.TaskPending, core.tasks[awaiter].version + 1)],
        core.promiseTimeouts,
        core.retryTimeouts + {awaiter},
        core.leaseTimeouts - {awaiter})
  }

  function RegisterCallback(s: CoordinationState, awaited: Id, awaiter: Id): CoordinationState {
    if awaited !in s.core.promises || awaiter !in s.core.promises then s
    else if s.core.promises[awaited].state == Core.Pending && awaiter in s.core.tasks && s.core.promises[awaiter].state == Core.Pending then
      State(s.core, s.callbacks + {CallbackKey(awaited, awaiter)}, s.readyCallbacks, s.listeners, s.outgoingExec, s.outgoingUnblock, s.schedules)
    else if s.core.promises[awaited].state != Core.Pending && awaiter in s.core.tasks && s.core.tasks[awaiter].state == Core.Suspended then
      var resumed := ResumeSuspendedTask(s.core, awaiter);
      State(
        resumed,
        s.callbacks,
        s.readyCallbacks,
        s.listeners,
        s.outgoingExec[awaiter := resumed.tasks[awaiter].version],
        s.outgoingUnblock,
        s.schedules)
    else s
  }

  function RegisterListener(s: CoordinationState, promise: Id, address: Address): CoordinationState {
    if promise in s.core.promises && s.core.promises[promise].state == Core.Pending then
      State(s.core, s.callbacks, s.readyCallbacks, s.listeners + {ListenerKey(promise, address)}, s.outgoingExec, s.outgoingUnblock, s.schedules)
    else s
  }

  function SettleAndNotify(s: CoordinationState, id: Id, newState: Core.PromiseState): CoordinationState {
    if id !in s.core.promises || s.core.promises[id].state != Core.Pending || newState == Core.Pending then s
    else
      State(
        Core.SettlePromise(s.core, id, newState),
        s.callbacks - CallbacksByAwaiter(s.callbacks, id),
        (s.readyCallbacks - CallbacksByAwaiter(s.readyCallbacks, id)) + (CallbacksByAwaited(s.callbacks, id) - CallbacksByAwaiter(s.callbacks, id)),
        s.listeners - ListenersFor(s.listeners, id),
        s.outgoingExec,
        s.outgoingUnblock + ListenersFor(s.listeners, id),
        s.schedules)
  }

  function ResumeReadyAwaiter(s: CoordinationState, awaiter: Id): CoordinationState {
    if awaiter !in s.core.tasks || s.core.tasks[awaiter].state != Core.Suspended || !HasReadyCallbackFor(s, awaiter) then s
    else
      var resumed := ResumeSuspendedTask(s.core, awaiter);
      State(
        resumed,
        s.callbacks,
        s.readyCallbacks,
        s.listeners,
        s.outgoingExec[awaiter := resumed.tasks[awaiter].version],
        s.outgoingUnblock,
        s.schedules)
  }

  function TimeoutSettlementState(s: CoordinationState, id: Id): Core.PromiseState
    requires id in s.core.promises
  {
    if s.core.promises[id].timer then Core.Resolved else Core.RejectedTimedout
  }

  function ExpirePromiseTimeout(s: CoordinationState, id: Id): CoordinationState {
    if id !in s.core.promises || s.core.promises[id].state != Core.Pending then s
    else SettleAndNotify(s, id, TimeoutSettlementState(s, id))
  }

  function ExpireRetryTimeout(s: CoordinationState, id: Id): CoordinationState {
    if id !in s.core.retryTimeouts || id !in s.core.tasks || s.core.tasks[id].state != Core.TaskPending then s
    else
      State(
        s.core,
        s.callbacks,
        s.readyCallbacks,
        s.listeners,
        s.outgoingExec[id := s.core.tasks[id].version],
        s.outgoingUnblock,
        s.schedules)
  }

  function ExpireLeaseTimeout(s: CoordinationState, id: Id): CoordinationState {
    if id !in s.core.leaseTimeouts || id !in s.core.tasks || s.core.tasks[id].state != Core.Acquired then s
    else
      var released := Core.ExpireLease(s.core, id);
      State(
        released,
        s.callbacks,
        s.readyCallbacks,
        s.listeners,
        s.outgoingExec[id := released.tasks[id].version],
        s.outgoingUnblock,
        s.schedules)
  }

  function ExpirePromiseTimeoutRows(s: CoordinationState, rows: TimeoutRows, id: Id): TimeoutRows {
    if id !in s.core.promises || s.core.promises[id].state != Core.Pending then rows
    else TimeoutRowsRec(rows.retryAt - {id}, rows.leaseAt - {id})
  }

  function ResumeReadyAwaiterRows(s: CoordinationState, rows: TimeoutRows, awaiter: Id, now: nat, retryDelay: nat): TimeoutRows {
    if awaiter !in s.core.tasks || s.core.tasks[awaiter].state != Core.Suspended || !HasReadyCallbackFor(s, awaiter) then rows
    else TimeoutRowsRec(rows.retryAt[awaiter := now + retryDelay], rows.leaseAt - {awaiter})
  }

  function ExpireRetryTimeoutRows(s: CoordinationState, rows: TimeoutRows, id: Id, now: nat, retryDelay: nat): TimeoutRows {
    if id !in rows.retryAt || id !in s.core.tasks || s.core.tasks[id].state != Core.TaskPending || rows.retryAt[id] > now then rows
    else TimeoutRowsRec(rows.retryAt[id := now + retryDelay], rows.leaseAt)
  }

  function ExpireLeaseTimeoutRows(s: CoordinationState, rows: TimeoutRows, id: Id, now: nat, retryDelay: nat): TimeoutRows {
    if id !in rows.leaseAt || id !in s.core.tasks || s.core.tasks[id].state != Core.Acquired || rows.leaseAt[id] > now then rows
    else TimeoutRowsRec(rows.retryAt[id := now + retryDelay], rows.leaseAt - {id})
  }

  function ApplyPromiseTimeouts(s: CoordinationState, expired: seq<Id>): CoordinationState
    decreases |expired|
  {
    if |expired| == 0 then s
    else ApplyPromiseTimeouts(ExpirePromiseTimeout(s, expired[0]), expired[1..])
  }

  function ResumeReadyAwaiters(s: CoordinationState, ready: seq<Id>): CoordinationState
    decreases |ready|
  {
    if |ready| == 0 then s
    else ResumeReadyAwaiters(ResumeReadyAwaiter(s, ready[0]), ready[1..])
  }

  function ApplyRetryTimeouts(s: CoordinationState, expired: seq<Id>): CoordinationState
    decreases |expired|
  {
    if |expired| == 0 then s
    else ApplyRetryTimeouts(ExpireRetryTimeout(s, expired[0]), expired[1..])
  }

  function ApplyLeaseTimeouts(s: CoordinationState, expired: seq<Id>): CoordinationState
    decreases |expired|
  {
    if |expired| == 0 then s
    else ApplyLeaseTimeouts(ExpireLeaseTimeout(s, expired[0]), expired[1..])
  }

  function ApplyPromiseTimeoutRows(s: CoordinationState, rows: TimeoutRows, expired: seq<Id>): TimeoutRows
    decreases |expired|
  {
    if |expired| == 0 then rows
    else ApplyPromiseTimeoutRows(ExpirePromiseTimeout(s, expired[0]), ExpirePromiseTimeoutRows(s, rows, expired[0]), expired[1..])
  }

  function ResumeReadyAwaitersRows(s: CoordinationState, rows: TimeoutRows, ready: seq<Id>, now: nat, retryDelay: nat): TimeoutRows
    decreases |ready|
  {
    if |ready| == 0 then rows
    else ResumeReadyAwaitersRows(ResumeReadyAwaiter(s, ready[0]), ResumeReadyAwaiterRows(s, rows, ready[0], now, retryDelay), ready[1..], now, retryDelay)
  }

  function ApplyRetryTimeoutRows(s: CoordinationState, rows: TimeoutRows, expired: seq<Id>, now: nat, retryDelay: nat): TimeoutRows
    decreases |expired|
  {
    if |expired| == 0 then rows
    else ApplyRetryTimeoutRows(ExpireRetryTimeout(s, expired[0]), ExpireRetryTimeoutRows(s, rows, expired[0], now, retryDelay), expired[1..], now, retryDelay)
  }

  function ApplyLeaseTimeoutRows(s: CoordinationState, rows: TimeoutRows, expired: seq<Id>, now: nat, retryDelay: nat): TimeoutRows
    decreases |expired|
  {
    if |expired| == 0 then rows
    else ApplyLeaseTimeoutRows(ExpireLeaseTimeout(s, expired[0]), ExpireLeaseTimeoutRows(s, rows, expired[0], now, retryDelay), expired[1..], now, retryDelay)
  }

  function TimeoutStatement1(s: CoordinationState, expiredPromises: seq<Id>, readyAwaiters: seq<Id>): CoordinationState {
    ResumeReadyAwaiters(ApplyPromiseTimeouts(s, expiredPromises), readyAwaiters)
  }

  function TimeoutStatement2(s: CoordinationState, expiredRetries: seq<Id>): CoordinationState {
    ApplyRetryTimeouts(s, expiredRetries)
  }

  function TimeoutStatement3(s: CoordinationState, expiredLeases: seq<Id>): CoordinationState {
    ApplyLeaseTimeouts(s, expiredLeases)
  }

  function TimeoutRowsAfterStatement1(s: CoordinationState, rows: TimeoutRows, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, now: nat, retryDelay: nat): TimeoutRows {
    var settled := ApplyPromiseTimeoutRows(s, rows, expiredPromises);
    var settledState := ApplyPromiseTimeouts(s, expiredPromises);
    ResumeReadyAwaitersRows(settledState, settled, readyAwaiters, now, retryDelay)
  }

  function TimeoutRowsAfterStatement2(s: CoordinationState, rows: TimeoutRows, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, expiredRetries: seq<Id>, now: nat, retryDelay: nat): TimeoutRows {
    var after1State := TimeoutStatement1(s, expiredPromises, readyAwaiters);
    var after1Rows := TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay);
    ApplyRetryTimeoutRows(after1State, after1Rows, expiredRetries, now, retryDelay)
  }

  function TimeoutRowsAfterStatement3(s: CoordinationState, rows: TimeoutRows, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, expiredRetries: seq<Id>, expiredLeases: seq<Id>, now: nat, retryDelay: nat): TimeoutRows {
    var after2State := TimeoutStatement2(TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries);
    var after2Rows := TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay);
    ApplyLeaseTimeoutRows(after2State, after2Rows, expiredLeases, now, retryDelay)
  }

  function BackendTimeoutRowsAfterStatement1(s: CoordinationState, rows: TimeoutRows, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, now: nat, retryDelay: nat): TimeoutRows {
    TimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay)
  }

  function BackendTimeoutRowsAfterStatement2(s: CoordinationState, rows: TimeoutRows, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, expiredRetries: seq<Id>, now: nat, retryDelay: nat): TimeoutRows {
    TimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay)
  }

  function BackendTimeoutRowsAfterStatement3(s: CoordinationState, rows: TimeoutRows, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, expiredRetries: seq<Id>, expiredLeases: seq<Id>, now: nat, retryDelay: nat): TimeoutRows {
    TimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, expiredLeases, now, retryDelay)
  }

  function SqliteTimeoutRowsAfterStatement1(s: CoordinationState, rows: TimeoutRows, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, now: nat, retryDelay: nat): TimeoutRows {
    BackendTimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay)
  }

  function SqliteTimeoutRowsAfterStatement2(s: CoordinationState, rows: TimeoutRows, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, expiredRetries: seq<Id>, now: nat, retryDelay: nat): TimeoutRows {
    BackendTimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay)
  }

  function SqliteTimeoutRowsAfterStatement3(s: CoordinationState, rows: TimeoutRows, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, expiredRetries: seq<Id>, expiredLeases: seq<Id>, now: nat, retryDelay: nat): TimeoutRows {
    BackendTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, expiredLeases, now, retryDelay)
  }

  function PostgresTimeoutRowsAfterStatement1(s: CoordinationState, rows: TimeoutRows, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, now: nat, retryDelay: nat): TimeoutRows {
    BackendTimeoutRowsAfterStatement1(s, rows, expiredPromises, readyAwaiters, now, retryDelay)
  }

  function PostgresTimeoutRowsAfterStatement2(s: CoordinationState, rows: TimeoutRows, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, expiredRetries: seq<Id>, now: nat, retryDelay: nat): TimeoutRows {
    BackendTimeoutRowsAfterStatement2(s, rows, expiredPromises, readyAwaiters, expiredRetries, now, retryDelay)
  }

  function PostgresTimeoutRowsAfterStatement3(s: CoordinationState, rows: TimeoutRows, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, expiredRetries: seq<Id>, expiredLeases: seq<Id>, now: nat, retryDelay: nat): TimeoutRows {
    BackendTimeoutRowsAfterStatement3(s, rows, expiredPromises, readyAwaiters, expiredRetries, expiredLeases, now, retryDelay)
  }

  function BackendTimeoutStatements(s: CoordinationState, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, expiredRetries: seq<Id>, expiredLeases: seq<Id>): CoordinationState {
    TimeoutStatement3(TimeoutStatement2(TimeoutStatement1(s, expiredPromises, readyAwaiters), expiredRetries), expiredLeases)
  }

  function SqliteTimeoutStatements(s: CoordinationState, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, expiredRetries: seq<Id>, expiredLeases: seq<Id>): CoordinationState {
    BackendTimeoutStatements(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases)
  }

  function PostgresTimeoutStatements(s: CoordinationState, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, expiredRetries: seq<Id>, expiredLeases: seq<Id>): CoordinationState {
    BackendTimeoutStatements(s, expiredPromises, readyAwaiters, expiredRetries, expiredLeases)
  }

  function ProcessTimeoutBatch(s: CoordinationState, expiredPromises: seq<Id>, readyAwaiters: seq<Id>, expiredRetries: seq<Id>, expiredLeases: seq<Id>): CoordinationState {
    var settled := ApplyPromiseTimeouts(s, expiredPromises);
    var resumed := ResumeReadyAwaiters(settled, readyAwaiters);
    var retried := ApplyRetryTimeouts(resumed, expiredRetries);
    ApplyLeaseTimeouts(retried, expiredLeases)
  }

  function ScheduleCreate(s: CoordinationState, id: Id, firstRunAt: nat, promiseTimeout: nat): CoordinationState {
    if id in s.schedules then s
    else
      State(
        s.core,
        s.callbacks,
        s.readyCallbacks,
        s.listeners,
        s.outgoingExec,
        s.outgoingUnblock,
        s.schedules[id := ScheduleRec(firstRunAt, 0, false, promiseTimeout)])
  }

  function InsertRunPromise(core: Core.ResonateState, promiseId: Id, timeoutAt: nat, createdAt: nat): Core.ResonateState {
    Core.CreatePromise(core, promiseId, timeoutAt, false, false, createdAt)
  }

  function ScheduleRun(s: CoordinationState, scheduleId: Id, promiseId: Id, createdAt: nat, timeoutAt: nat, nextRunAt: nat): CoordinationState {
    if scheduleId !in s.schedules then s
    else
      State(
        InsertRunPromise(s.core, promiseId, timeoutAt, createdAt),
        s.callbacks,
        s.readyCallbacks,
        s.listeners,
        s.outgoingExec,
        s.outgoingUnblock,
        s.schedules[scheduleId := ScheduleRec(nextRunAt, createdAt, true, s.schedules[scheduleId].promiseTimeout)])
  }

  predicate ScheduleDueAt(s: CoordinationState, scheduleId: Id, now: nat) {
    scheduleId in s.schedules && s.schedules[scheduleId].nextRunAt <= now
  }

  function DueSchedulesAt(s: CoordinationState, now: nat): set<Id> {
    set scheduleId: Id | scheduleId in s.schedules && ScheduleDueAt(s, scheduleId, now)
  }

  predicate ExhaustedRunPrefix(schedule: Schedule, now: nat, runs: seq<ScheduleRunRequest>, finalNextRunAt: nat) {
    |runs| > 0 &&
    runs[0].createdAt == schedule.nextRunAt &&
    (forall i: nat :: i < |runs| ==> runs[i].createdAt <= now) &&
    (forall i: nat :: i + 1 < |runs| ==> runs[i].createdAt < runs[i + 1].createdAt) &&
    finalNextRunAt > now
  }

  function ApplyScheduleRunPromises(core: Core.ResonateState, runs: seq<ScheduleRunRequest>): Core.ResonateState
    decreases |runs|
  {
    if |runs| == 0 then core
    else ApplyScheduleRunPromises(InsertRunPromise(core, runs[0].promiseId, runs[0].timeoutAt, runs[0].createdAt), runs[1..])
  }

  function ScheduleRunBatch(s: CoordinationState, scheduleId: Id, runs: seq<ScheduleRunRequest>, finalNextRunAt: nat): CoordinationState {
    if scheduleId !in s.schedules || |runs| == 0 then s
    else
      State(
        ApplyScheduleRunPromises(s.core, runs),
        s.callbacks,
        s.readyCallbacks,
        s.listeners,
        s.outgoingExec,
        s.outgoingUnblock,
        s.schedules[scheduleId := ScheduleRec(finalNextRunAt, runs[|runs| - 1].createdAt, true, s.schedules[scheduleId].promiseTimeout)])
  }
}
