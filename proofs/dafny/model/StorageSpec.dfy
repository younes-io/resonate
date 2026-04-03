include "ResonateModel.dfy"

module ResonateStorageSpec {
  import M = ResonateModel

  predicate PromiseCreateContract(before: M.ResonateState, after: M.ResonateState, id: M.Id, timeoutAt: nat, timer: bool, hasTarget: bool, now: nat) {
    after == M.CreatePromise(before, id, timeoutAt, timer, hasTarget, now)
  }

  predicate PromiseSettleContract(before: M.ResonateState, after: M.ResonateState, id: M.Id, newState: M.PromiseState) {
    after == M.SettlePromise(before, id, newState)
  }

  predicate TaskAcquireContract(before: M.ResonateState, after: M.ResonateState, id: M.Id, version: nat) {
    after == M.AcquireTask(before, id, version)
  }

  predicate TaskReleaseContract(before: M.ResonateState, after: M.ResonateState, id: M.Id, version: nat) {
    after == M.ReleaseTask(before, id, version)
  }

  predicate TaskFulfillContract(before: M.ResonateState, after: M.ResonateState, id: M.Id, version: nat, newState: M.PromiseState) {
    after == M.FulfillTask(before, id, version, newState)
  }

  predicate PromiseTimeoutContract(before: M.ResonateState, after: M.ResonateState, id: M.Id, now: nat) {
    after == M.ExpirePromise(before, id, now)
  }

  predicate LeaseTimeoutContract(before: M.ResonateState, after: M.ResonateState, id: M.Id) {
    after == M.ExpireLease(before, id)
  }

  lemma ContractsPreserveValidityAfterPromiseCreate(before: M.ResonateState, after: M.ResonateState, id: M.Id, timeoutAt: nat, timer: bool, hasTarget: bool, now: nat)
    requires M.Valid(before)
    requires id !in before.promises
    requires PromiseCreateContract(before, after, id, timeoutAt, timer, hasTarget, now)
    ensures M.Valid(after)
  {
    assert after == M.CreatePromise(before, id, timeoutAt, timer, hasTarget, now);
  }
}
