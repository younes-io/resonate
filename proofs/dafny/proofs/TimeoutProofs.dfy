include "../model/ResonateModel.dfy"

module ResonateTimeoutProofs {
  import M = ResonateModel

  lemma ExpirePromisePreservesValidity(s: M.ResonateState, id: M.Id, now: nat)
    requires M.Valid(s)
    ensures M.Valid(M.ExpirePromise(s, id, now))
  {
    if id in s.promises && s.promises[id].state == M.Pending && now >= s.promises[id].timeoutAt {
      assert M.ExpirePromise(s, id, now) == M.SettlePromise(s, id, if s.promises[id].timer then M.Resolved else M.RejectedTimedout);
    }
  }

  lemma ExpireLeasePreservesValidity(s: M.ResonateState, id: M.Id)
    requires M.Valid(s)
    ensures M.Valid(M.ExpireLease(s, id))
  {
    if id in s.tasks && s.tasks[id].state == M.Acquired && id in s.leaseTimeouts {
      assert M.ExpireLease(s, id) ==
        M.State(s.promises, s.tasks[id := M.TaskRec(M.TaskPending, s.tasks[id].version + 1)], s.promiseTimeouts, s.retryTimeouts + {id}, s.leaseTimeouts - {id});
    }
  }

  lemma ExpirePromiseFulfillsBoundTask(s: M.ResonateState, id: M.Id, now: nat)
    requires M.Valid(s)
    requires id in s.promises
    requires id in s.tasks
    requires s.promises[id].state == M.Pending
    requires now >= s.promises[id].timeoutAt
    ensures M.ExpirePromise(s, id, now).tasks[id].state == M.Fulfilled
  {
    assert M.ExpirePromise(s, id, now) == M.SettlePromise(s, id, if s.promises[id].timer then M.Resolved else M.RejectedTimedout);
  }

  lemma ExpireLeaseReturnsTaskToPending(s: M.ResonateState, id: M.Id)
    requires M.Valid(s)
    requires id in s.tasks
    requires s.tasks[id].state == M.Acquired
    requires id in s.leaseTimeouts
    ensures M.ExpireLease(s, id).tasks[id].state == M.TaskPending
  {
    assert M.ExpireLease(s, id) ==
      M.State(s.promises, s.tasks[id := M.TaskRec(M.TaskPending, s.tasks[id].version + 1)], s.promiseTimeouts, s.retryTimeouts + {id}, s.leaseTimeouts - {id});
  }

  lemma ExpireLeaseBumpsVersion(s: M.ResonateState, id: M.Id)
    requires M.Valid(s)
    requires id in s.tasks
    requires s.tasks[id].state == M.Acquired
    requires id in s.leaseTimeouts
    ensures M.ExpireLease(s, id).tasks[id].version == s.tasks[id].version + 1
  {
    assert M.ExpireLease(s, id) ==
      M.State(s.promises, s.tasks[id := M.TaskRec(M.TaskPending, s.tasks[id].version + 1)], s.promiseTimeouts, s.retryTimeouts + {id}, s.leaseTimeouts - {id});
  }
}
