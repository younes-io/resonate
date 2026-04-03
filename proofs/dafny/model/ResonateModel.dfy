module ResonateModel {
  type Id = nat

  datatype PromiseState = Pending | Resolved | Rejected | RejectedCanceled | RejectedTimedout
  datatype TaskState = TaskPending | Acquired | Suspended | Halted | Fulfilled

  datatype Promise = PromiseRec(state: PromiseState, timeoutAt: nat, timer: bool)
  datatype Task = TaskRec(state: TaskState, version: nat)

  datatype ResonateState = State(
    promises: map<Id, Promise>,
    tasks: map<Id, Task>,
    promiseTimeouts: set<Id>,
    retryTimeouts: set<Id>,
    leaseTimeouts: set<Id>
  )

  function EmptyState(): ResonateState {
    State(map[], map[], {}, {}, {})
  }

  predicate PromiseTerminal(ps: PromiseState) {
    ps != Pending
  }

  predicate AllAwaitedPending(s: ResonateState, awaited: set<Id>) {
    forall aid :: aid in awaited ==> aid in s.promises && s.promises[aid].state == Pending
  }

  predicate Valid(s: ResonateState) {
    (forall id :: id in s.tasks ==> id in s.promises) &&
    (forall id :: id in s.promiseTimeouts ==> id in s.promises && s.promises[id].state == Pending) &&
    (forall id :: id in s.retryTimeouts ==> id in s.tasks && s.tasks[id].state == TaskPending && id !in s.leaseTimeouts) &&
    (forall id :: id in s.leaseTimeouts ==> id in s.tasks && s.tasks[id].state == Acquired && id !in s.retryTimeouts) &&
    (forall id :: id in s.tasks && s.tasks[id].state == Suspended ==> id !in s.retryTimeouts && id !in s.leaseTimeouts && s.promises[id].state == Pending) &&
    (forall id :: id in s.tasks && s.tasks[id].state == Halted ==> id !in s.retryTimeouts && id !in s.leaseTimeouts && s.promises[id].state == Pending) &&
    (forall id :: id in s.tasks && s.tasks[id].state == Fulfilled ==> id !in s.retryTimeouts && id !in s.leaseTimeouts && PromiseTerminal(s.promises[id].state)) &&
    (forall id :: id in s.tasks && (s.tasks[id].state == TaskPending || s.tasks[id].state == Acquired) ==> s.promises[id].state == Pending)
  }

  function CreatePromise(s: ResonateState, id: Id, timeoutAt: nat, timer: bool, hasTarget: bool, now: nat): ResonateState {
    if id in s.promises then s
    else if now >= timeoutAt then
      State(
        s.promises[id := PromiseRec(if timer then Resolved else RejectedTimedout, timeoutAt, timer)],
        if hasTarget then s.tasks[id := TaskRec(Fulfilled, 0)] else s.tasks,
        s.promiseTimeouts,
        s.retryTimeouts,
        s.leaseTimeouts)
    else
      State(
        s.promises[id := PromiseRec(Pending, timeoutAt, timer)],
        if hasTarget then s.tasks[id := TaskRec(TaskPending, 0)] else s.tasks,
        s.promiseTimeouts + {id},
        if hasTarget then s.retryTimeouts + {id} else s.retryTimeouts,
        s.leaseTimeouts)
  }

  function SettlePromise(s: ResonateState, id: Id, newState: PromiseState): ResonateState {
    if id !in s.promises || s.promises[id].state != Pending || newState == Pending then s
    else
      State(
        s.promises[id := PromiseRec(newState, s.promises[id].timeoutAt, s.promises[id].timer)],
        if id in s.tasks then s.tasks[id := TaskRec(Fulfilled, s.tasks[id].version)] else s.tasks,
        s.promiseTimeouts - {id},
        s.retryTimeouts - {id},
        s.leaseTimeouts - {id})
  }

  function AcquireTask(s: ResonateState, id: Id, version: nat): ResonateState {
    if id !in s.tasks || s.tasks[id].state != TaskPending || s.tasks[id].version != version then s
    else
      State(
        s.promises,
        s.tasks[id := TaskRec(Acquired, version)],
        s.promiseTimeouts,
        s.retryTimeouts - {id},
        s.leaseTimeouts + {id})
  }

  function ReleaseTask(s: ResonateState, id: Id, version: nat): ResonateState {
    if id !in s.tasks || s.tasks[id].state != Acquired || s.tasks[id].version != version then s
    else
      State(
        s.promises,
        s.tasks[id := TaskRec(TaskPending, version + 1)],
        s.promiseTimeouts,
        s.retryTimeouts + {id},
        s.leaseTimeouts - {id})
  }

  function SuspendTask(s: ResonateState, id: Id, version: nat, awaited: set<Id>): ResonateState {
    if id !in s.tasks || s.tasks[id].state != Acquired || s.tasks[id].version != version || !AllAwaitedPending(s, awaited) then s
    else
      State(
        s.promises,
        s.tasks[id := TaskRec(Suspended, version)],
        s.promiseTimeouts,
        s.retryTimeouts,
        s.leaseTimeouts - {id})
  }

  function FulfillTask(s: ResonateState, id: Id, version: nat, newState: PromiseState): ResonateState {
    if id !in s.tasks || id !in s.promises || s.tasks[id].state != Acquired || s.tasks[id].version != version || s.promises[id].state != Pending || newState == Pending then s
    else
      State(
        s.promises[id := PromiseRec(newState, s.promises[id].timeoutAt, s.promises[id].timer)],
        s.tasks[id := TaskRec(Fulfilled, version)],
        s.promiseTimeouts - {id},
        s.retryTimeouts - {id},
        s.leaseTimeouts - {id})
  }

  function HaltTask(s: ResonateState, id: Id): ResonateState {
    if id !in s.tasks || s.tasks[id].state == Fulfilled || s.tasks[id].state == Halted then s
    else
      State(
        s.promises,
        s.tasks[id := TaskRec(Halted, s.tasks[id].version)],
        s.promiseTimeouts,
        s.retryTimeouts - {id},
        s.leaseTimeouts - {id})
  }

  function ContinueTask(s: ResonateState, id: Id): ResonateState {
    if id !in s.tasks || s.tasks[id].state != Halted then s
    else
      State(
        s.promises,
        s.tasks[id := TaskRec(TaskPending, s.tasks[id].version + 1)],
        s.promiseTimeouts,
        s.retryTimeouts + {id},
        s.leaseTimeouts - {id})
  }

  function ExpirePromise(s: ResonateState, id: Id, now: nat): ResonateState {
    if id !in s.promises || s.promises[id].state != Pending || now < s.promises[id].timeoutAt then s
    else
      SettlePromise(s, id, if s.promises[id].timer then Resolved else RejectedTimedout)
  }

  function ExpireLease(s: ResonateState, id: Id): ResonateState {
    if id !in s.tasks || s.tasks[id].state != Acquired || id !in s.leaseTimeouts then s
    else
      State(
        s.promises,
        s.tasks[id := TaskRec(TaskPending, s.tasks[id].version + 1)],
        s.promiseTimeouts,
        s.retryTimeouts + {id},
        s.leaseTimeouts - {id})
  }
}
