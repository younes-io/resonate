include "../model/ResonateModel.dfy"

module ResonatePromiseStateMachineProofs {
  import M = ResonateModel

  lemma EmptyStateIsValid()
    ensures M.Valid(M.EmptyState())
  {
    assert M.EmptyState().promises == map[];
    assert M.EmptyState().tasks == map[];
  }

  lemma CreatePromisePreservesValidity(s: M.ResonateState, id: M.Id, timeoutAt: nat, timer: bool, hasTarget: bool, now: nat)
    requires M.Valid(s)
    requires id !in s.promises
    ensures M.Valid(M.CreatePromise(s, id, timeoutAt, timer, hasTarget, now))
  {
    assert M.CreatePromise(s, id, timeoutAt, timer, hasTarget, now) ==
      if now >= timeoutAt then
        M.State(
          s.promises[id := M.PromiseRec(if timer then M.Resolved else M.RejectedTimedout, timeoutAt, timer)],
          if hasTarget then s.tasks[id := M.TaskRec(M.Fulfilled, 0)] else s.tasks,
          s.promiseTimeouts,
          s.retryTimeouts,
          s.leaseTimeouts)
      else
        M.State(
          s.promises[id := M.PromiseRec(M.Pending, timeoutAt, timer)],
          if hasTarget then s.tasks[id := M.TaskRec(M.TaskPending, 0)] else s.tasks,
          s.promiseTimeouts + {id},
          if hasTarget then s.retryTimeouts + {id} else s.retryTimeouts,
          s.leaseTimeouts);
  }

  lemma SettlePromisePreservesValidity(s: M.ResonateState, id: M.Id, newState: M.PromiseState)
    requires M.Valid(s)
    ensures M.Valid(M.SettlePromise(s, id, newState))
  {
    if id in s.promises && s.promises[id].state == M.Pending && newState != M.Pending {
      assert M.SettlePromise(s, id, newState) ==
        M.State(
          s.promises[id := M.PromiseRec(newState, s.promises[id].timeoutAt, s.promises[id].timer)],
          if id in s.tasks then s.tasks[id := M.TaskRec(M.Fulfilled, s.tasks[id].version)] else s.tasks,
          s.promiseTimeouts - {id},
          s.retryTimeouts - {id},
          s.leaseTimeouts - {id});
    }
  }

  lemma AcquireTaskPreservesValidity(s: M.ResonateState, id: M.Id, version: nat)
    requires M.Valid(s)
    ensures M.Valid(M.AcquireTask(s, id, version))
  {
    if id in s.tasks && s.tasks[id].state == M.TaskPending && s.tasks[id].version == version {
      assert M.AcquireTask(s, id, version) ==
        M.State(s.promises, s.tasks[id := M.TaskRec(M.Acquired, version)], s.promiseTimeouts, s.retryTimeouts - {id}, s.leaseTimeouts + {id});
    }
  }

  lemma ReleaseTaskPreservesValidity(s: M.ResonateState, id: M.Id, version: nat)
    requires M.Valid(s)
    ensures M.Valid(M.ReleaseTask(s, id, version))
  {
    if id in s.tasks && s.tasks[id].state == M.Acquired && s.tasks[id].version == version {
      assert M.ReleaseTask(s, id, version) ==
        M.State(s.promises, s.tasks[id := M.TaskRec(M.TaskPending, version + 1)], s.promiseTimeouts, s.retryTimeouts + {id}, s.leaseTimeouts - {id});
    }
  }

  lemma SuspendTaskPreservesValidity(s: M.ResonateState, id: M.Id, version: nat, awaited: set<M.Id>)
    requires M.Valid(s)
    ensures M.Valid(M.SuspendTask(s, id, version, awaited))
  {
    if id in s.tasks && s.tasks[id].state == M.Acquired && s.tasks[id].version == version && M.AllAwaitedPending(s, awaited) {
      assert M.SuspendTask(s, id, version, awaited) ==
        M.State(s.promises, s.tasks[id := M.TaskRec(M.Suspended, version)], s.promiseTimeouts, s.retryTimeouts, s.leaseTimeouts - {id});
    }
  }

  lemma FulfillTaskPreservesValidity(s: M.ResonateState, id: M.Id, version: nat, newState: M.PromiseState)
    requires M.Valid(s)
    ensures M.Valid(M.FulfillTask(s, id, version, newState))
  {
    if id in s.tasks && id in s.promises && s.tasks[id].state == M.Acquired && s.tasks[id].version == version && s.promises[id].state == M.Pending && newState != M.Pending {
      assert M.FulfillTask(s, id, version, newState) ==
        M.State(
          s.promises[id := M.PromiseRec(newState, s.promises[id].timeoutAt, s.promises[id].timer)],
          s.tasks[id := M.TaskRec(M.Fulfilled, version)],
          s.promiseTimeouts - {id},
          s.retryTimeouts - {id},
          s.leaseTimeouts - {id});
    }
  }

  lemma HaltAndContinuePreserveValidity(s: M.ResonateState, id: M.Id)
    requires M.Valid(s)
    ensures M.Valid(M.HaltTask(s, id))
    ensures M.Valid(M.ContinueTask(M.HaltTask(s, id), id))
  {
    if id in s.tasks && s.tasks[id].state != M.Fulfilled && s.tasks[id].state != M.Halted {
      assert M.HaltTask(s, id) ==
        M.State(s.promises, s.tasks[id := M.TaskRec(M.Halted, s.tasks[id].version)], s.promiseTimeouts, s.retryTimeouts - {id}, s.leaseTimeouts - {id});
      assert M.ContinueTask(M.HaltTask(s, id), id) ==
        M.State(s.promises, M.HaltTask(s, id).tasks[id := M.TaskRec(M.TaskPending, M.HaltTask(s, id).tasks[id].version + 1)], s.promiseTimeouts, M.HaltTask(s, id).retryTimeouts + {id}, M.HaltTask(s, id).leaseTimeouts - {id});
    }
  }

  lemma FulfilledTaskImpliesTerminalPromise(s: M.ResonateState, id: M.Id)
    requires M.Valid(s)
    requires id in s.tasks
    requires s.tasks[id].state == M.Fulfilled
    ensures M.PromiseTerminal(s.promises[id].state)
  {
    assert id in s.promises;
  }
}
