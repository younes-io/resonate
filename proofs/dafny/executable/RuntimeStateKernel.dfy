module RuntimeStateKernel {
  datatype PromiseState = Pending | Resolved | Rejected | RejectedCanceled | RejectedTimedout
  datatype TaskState = TaskPending | Acquired | Suspended | Halted | Fulfilled
  datatype Schedule = ScheduleRec(nextRunAt: nat, lastRunAt: nat, hasRun: bool, promiseTimeout: nat)

  function StrictlyIncreasing(xs: seq<nat>): bool {
    forall i: nat :: i + 1 < |xs| ==> xs[i] < xs[i + 1]
  }

  function CreatePromiseState(now: nat, timeoutAt: nat, timer: bool): PromiseState {
    if now >= timeoutAt then if timer then Resolved else RejectedTimedout else Pending
  }

  function CreatePromiseCreatedAt(now: nat, timeoutAt: nat): nat {
    if now >= timeoutAt then timeoutAt else now
  }

  function CreatePromiseHasSettled(now: nat, timeoutAt: nat): bool {
    now >= timeoutAt
  }

  function CreatePromiseSettledAt(now: nat, timeoutAt: nat): nat {
    if now >= timeoutAt then timeoutAt else 0
  }

  function CreatePromiseHasTask(hasTarget: bool): bool {
    hasTarget
  }

  function CreatePromiseTaskState(now: nat, timeoutAt: nat): TaskState {
    if now >= timeoutAt then Fulfilled else TaskPending
  }

  function SettlePromiseState(current: PromiseState, newState: PromiseState): PromiseState {
    if current != Pending || newState == Pending then current else newState
  }

  function SettlePromiseTaskState(currentPromise: PromiseState, newState: PromiseState, hasTask: bool, currentTask: TaskState): TaskState {
    if !hasTask || currentPromise != Pending || newState == Pending then currentTask else Fulfilled
  }

  function AcquireTaskState(current: TaskState, currentVersion: nat, requestedVersion: nat): TaskState {
    if current == TaskPending && currentVersion == requestedVersion then Acquired else current
  }

  function AcquireTaskVersion(current: TaskState, currentVersion: nat, requestedVersion: nat): nat {
    currentVersion
  }

  function ReleaseTaskState(current: TaskState, currentVersion: nat, requestedVersion: nat): TaskState {
    if current == Acquired && currentVersion == requestedVersion then TaskPending else current
  }

  function ReleaseTaskVersion(current: TaskState, currentVersion: nat, requestedVersion: nat): nat {
    if current == Acquired && currentVersion == requestedVersion then currentVersion + 1 else currentVersion
  }

  function FulfillTaskState(currentTask: TaskState, currentVersion: nat, requestedVersion: nat, currentPromise: PromiseState, newPromise: PromiseState): TaskState {
    if currentTask == Acquired && currentVersion == requestedVersion && currentPromise == Pending && newPromise != Pending then Fulfilled else currentTask
  }

  function FulfillPromiseState(currentTask: TaskState, currentVersion: nat, requestedVersion: nat, currentPromise: PromiseState, newPromise: PromiseState): PromiseState {
    if currentTask == Acquired && currentVersion == requestedVersion && currentPromise == Pending && newPromise != Pending then newPromise else currentPromise
  }

  function HaltTaskState(current: TaskState): TaskState {
    if current == Fulfilled || current == Halted then current else Halted
  }

  function ContinueTaskState(current: TaskState): TaskState {
    if current == Halted then TaskPending else current
  }

  function ContinueTaskVersion(current: TaskState, currentVersion: nat): nat {
    if current == Halted then currentVersion + 1 else currentVersion
  }

  function ScheduleCreate(firstRunAt: nat, promiseTimeout: nat): Schedule {
    ScheduleRec(firstRunAt, 0, false, promiseTimeout)
  }

  predicate ValidScheduleAdvanceInput(schedule: Schedule, runTimes: seq<nat>, finalNextRunAt: nat) {
    |runTimes| > 0 &&
    runTimes[0] == schedule.nextRunAt &&
    StrictlyIncreasing(runTimes) &&
    runTimes[|runTimes| - 1] < finalNextRunAt
  }

  function ScheduleAdvance(schedule: Schedule, runTimes: seq<nat>, finalNextRunAt: nat): Schedule {
    if ValidScheduleAdvanceInput(schedule, runTimes, finalNextRunAt) then
      ScheduleRec(finalNextRunAt, runTimes[|runTimes| - 1], true, schedule.promiseTimeout)
    else
      schedule
  }

  lemma ScheduleAdvanceIsIdempotentOnPostState(schedule: Schedule, runTimes: seq<nat>, finalNextRunAt: nat)
    requires ValidScheduleAdvanceInput(schedule, runTimes, finalNextRunAt)
    ensures ScheduleAdvance(ScheduleAdvance(schedule, runTimes, finalNextRunAt), runTimes, finalNextRunAt) ==
            ScheduleAdvance(schedule, runTimes, finalNextRunAt)
  {
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

  method Main(args: seq<string>)
  {
    if |args| == 0 {
      print "ERR\n";
      return;
    }

    var start := 0;
    var command := args[0];
    if command != "promise-create" && command != "promise-settle" && command != "task-acquire" && command != "task-release" && command != "task-fulfill" && command != "task-halt" && command != "task-continue" && command != "schedule-create" && command != "schedule-advance" && |args| > 1 {
      start := 1;
      command := args[1];
    }

    if command == "promise-create" {
      if |args| != start + 5 {
        print "ERR\n";
        return;
      }
      var okNow, now := ParseNat(args[start + 1]);
      var okTimeoutAt, timeoutAt := ParseNat(args[start + 2]);
      var okTimer, timer := ParseBoolCode(args[start + 3]);
      var okHasTarget, hasTarget := ParseBoolCode(args[start + 4]);
      if !(okNow && okTimeoutAt && okTimer && okHasTarget) {
        print "ERR\n";
        return;
      }
      print PromiseStateCode(CreatePromiseState(now, timeoutAt, timer)), "\n";
      print CreatePromiseCreatedAt(now, timeoutAt), "\n";
      PrintBoolCode(CreatePromiseHasSettled(now, timeoutAt));
      print CreatePromiseSettledAt(now, timeoutAt), "\n";
      PrintBoolCode(CreatePromiseHasTask(hasTarget));
      print TaskStateCode(CreatePromiseTaskState(now, timeoutAt)), "\n";
    } else if command == "promise-settle" {
      if |args| != start + 6 {
        print "ERR\n";
        return;
      }
      var okCurrentPromise, currentPromiseCode := ParseNat(args[start + 1]);
      var okNewPromise, newPromiseCode := ParseNat(args[start + 2]);
      var okHasTask, hasTask := ParseBoolCode(args[start + 3]);
      var okCurrentTask, currentTaskCode := ParseNat(args[start + 4]);
      var okTaskVersion, taskVersion := ParseNat(args[start + 5]);
      if !(okCurrentPromise && okNewPromise && okHasTask && okCurrentTask && okTaskVersion) {
        print "ERR\n";
        return;
      }
      var currentPromise := ParsePromiseStateCode(currentPromiseCode);
      var newPromise := ParsePromiseStateCode(newPromiseCode);
      var currentTask := ParseTaskStateCode(currentTaskCode);
      var nextPromise := SettlePromiseState(currentPromise, newPromise);
      var nextTask := SettlePromiseTaskState(currentPromise, newPromise, hasTask, currentTask);
      PrintBoolCode(nextPromise != currentPromise);
      print PromiseStateCode(nextPromise), "\n";
      PrintBoolCode(hasTask);
      print TaskStateCode(nextTask), "\n";
      print taskVersion, "\n";
    } else if command == "task-acquire" {
      if |args| != start + 4 {
        print "ERR\n";
        return;
      }
      var okCurrentState, currentStateCode := ParseNat(args[start + 1]);
      var okCurrentVersion, currentVersion := ParseNat(args[start + 2]);
      var okRequestedVersion, requestedVersion := ParseNat(args[start + 3]);
      if !(okCurrentState && okCurrentVersion && okRequestedVersion) {
        print "ERR\n";
        return;
      }
      var currentState := ParseTaskStateCode(currentStateCode);
      var nextState := AcquireTaskState(currentState, currentVersion, requestedVersion);
      PrintBoolCode(nextState != currentState);
      print TaskStateCode(nextState), "\n";
      print AcquireTaskVersion(currentState, currentVersion, requestedVersion), "\n";
    } else if command == "task-release" {
      if |args| != start + 4 {
        print "ERR\n";
        return;
      }
      var okCurrentState, currentStateCode := ParseNat(args[start + 1]);
      var okCurrentVersion, currentVersion := ParseNat(args[start + 2]);
      var okRequestedVersion, requestedVersion := ParseNat(args[start + 3]);
      if !(okCurrentState && okCurrentVersion && okRequestedVersion) {
        print "ERR\n";
        return;
      }
      var currentState := ParseTaskStateCode(currentStateCode);
      var nextState := ReleaseTaskState(currentState, currentVersion, requestedVersion);
      PrintBoolCode(nextState != currentState || ReleaseTaskVersion(currentState, currentVersion, requestedVersion) != currentVersion);
      print TaskStateCode(nextState), "\n";
      print ReleaseTaskVersion(currentState, currentVersion, requestedVersion), "\n";
    } else if command == "task-fulfill" {
      if |args| != start + 6 {
        print "ERR\n";
        return;
      }
      var okCurrentTask, currentTaskCode := ParseNat(args[start + 1]);
      var okCurrentVersion, currentVersion := ParseNat(args[start + 2]);
      var okRequestedVersion, requestedVersion := ParseNat(args[start + 3]);
      var okCurrentPromise, currentPromiseCode := ParseNat(args[start + 4]);
      var okNewPromise, newPromiseCode := ParseNat(args[start + 5]);
      if !(okCurrentTask && okCurrentVersion && okRequestedVersion && okCurrentPromise && okNewPromise) {
        print "ERR\n";
        return;
      }
      var currentTask := ParseTaskStateCode(currentTaskCode);
      var currentPromise := ParsePromiseStateCode(currentPromiseCode);
      var newPromise := ParsePromiseStateCode(newPromiseCode);
      var nextTask := FulfillTaskState(currentTask, currentVersion, requestedVersion, currentPromise, newPromise);
      var nextPromise := FulfillPromiseState(currentTask, currentVersion, requestedVersion, currentPromise, newPromise);
      PrintBoolCode(nextTask != currentTask || nextPromise != currentPromise);
      print TaskStateCode(nextTask), "\n";
      print currentVersion, "\n";
      print PromiseStateCode(nextPromise), "\n";
    } else if command == "task-halt" {
      if |args| != start + 3 {
        print "ERR\n";
        return;
      }
      var okCurrentState, currentStateCode := ParseNat(args[start + 1]);
      var okCurrentVersion, currentVersion := ParseNat(args[start + 2]);
      if !(okCurrentState && okCurrentVersion) {
        print "ERR\n";
        return;
      }
      var currentState := ParseTaskStateCode(currentStateCode);
      var nextState := HaltTaskState(currentState);
      PrintBoolCode(nextState != currentState);
      print TaskStateCode(nextState), "\n";
      print currentVersion, "\n";
    } else if command == "task-continue" {
      if |args| != start + 3 {
        print "ERR\n";
        return;
      }
      var okCurrentState, currentStateCode := ParseNat(args[start + 1]);
      var okCurrentVersion, currentVersion := ParseNat(args[start + 2]);
      if !(okCurrentState && okCurrentVersion) {
        print "ERR\n";
        return;
      }
      var currentState := ParseTaskStateCode(currentStateCode);
      var nextState := ContinueTaskState(currentState);
      var nextVersion := ContinueTaskVersion(currentState, currentVersion);
      PrintBoolCode(nextState != currentState || nextVersion != currentVersion);
      print TaskStateCode(nextState), "\n";
      print nextVersion, "\n";
    } else if command == "schedule-create" {
      if |args| != start + 3 {
        print "ERR\n";
        return;
      }
      var okFirstRunAt, firstRunAt := ParseNat(args[start + 1]);
      var okPromiseTimeout, promiseTimeout := ParseNat(args[start + 2]);
      if !(okFirstRunAt && okPromiseTimeout) {
        print "ERR\n";
        return;
      }
      var schedule := ScheduleCreate(firstRunAt, promiseTimeout);
      PrintBoolCode(schedule.hasRun);
      print schedule.lastRunAt, "\n";
      print schedule.nextRunAt, "\n";
      print schedule.promiseTimeout, "\n";
    } else if command == "schedule-advance" {
      if |args| < start + 7 {
        print "ERR\n";
        return;
      }
      var okNextRunAt, nextRunAt := ParseNat(args[start + 1]);
      var okHasRun, hasRun := ParseBoolCode(args[start + 2]);
      var okLastRunAt, lastRunAt := ParseNat(args[start + 3]);
      var okPromiseTimeout, promiseTimeout := ParseNat(args[start + 4]);
      var okRunCount, runCount := ParseNat(args[start + 5]);
      if !(okNextRunAt && okHasRun && okLastRunAt && okPromiseTimeout && okRunCount) {
        print "ERR\n";
        return;
      }
      if |args| != start + 7 + runCount {
        print "ERR\n";
        return;
      }
      var runTimes: seq<nat> := [];
      var i := 0;
      while i < runCount
        invariant 0 <= i <= runCount
        invariant |runTimes| == i
      {
        var okRunTime, runTime := ParseNat(args[start + 6 + i]);
        if !okRunTime {
          print "ERR\n";
          return;
        }
        runTimes := runTimes + [runTime];
        i := i + 1;
      }
      var okFinalNextRunAt, finalNextRunAt := ParseNat(args[start + 6 + runCount]);
      if !okFinalNextRunAt {
        print "ERR\n";
        return;
      }
      var schedule := ScheduleRec(nextRunAt, lastRunAt, hasRun, promiseTimeout);
      var nextSchedule := ScheduleAdvance(schedule, runTimes, finalNextRunAt);
      PrintBoolCode(ValidScheduleAdvanceInput(schedule, runTimes, finalNextRunAt));
      PrintBoolCode(nextSchedule.hasRun);
      print nextSchedule.lastRunAt, "\n";
      print nextSchedule.nextRunAt, "\n";
      print nextSchedule.promiseTimeout, "\n";
    } else {
      print "ERR\n";
    }
  }
}
