module SchedulePlannerKernel {
  function StrictlyIncreasing(xs: seq<nat>): bool {
    forall i: nat :: i + 1 < |xs| ==> xs[i] < xs[i + 1]
  }

  function HasFutureCandidate(now: nat, xs: seq<nat>): bool {
    exists i: nat :: i < |xs| && xs[i] > now
  }

  predicate ValidScheduleCandidateStream(now: nat, candidates: seq<nat>) {
    |candidates| > 0 &&
    StrictlyIncreasing(candidates) &&
    candidates[0] <= now &&
    HasFutureCandidate(now, candidates)
  }

  predicate TrustedCronCandidateStream(firstCandidate: nat, now: nat, candidates: seq<nat>) {
    ValidScheduleCandidateStream(now, candidates) &&
    candidates[0] == firstCandidate
  }

  lemma TrustedCronCandidateStreamIsValid(now: nat, firstCandidate: nat, candidates: seq<nat>)
    requires TrustedCronCandidateStream(firstCandidate, now, candidates)
    ensures ValidScheduleCandidateStream(now, candidates)
    ensures candidates[0] == firstCandidate
  {
  }

  predicate ExhaustedDuePrefixBoundary(now: nat, candidates: seq<nat>, runTimes: seq<nat>, finalNextRunAt: nat) {
    |runTimes| > 0 &&
    |runTimes| < |candidates| &&
    runTimes == candidates[..|runTimes|] &&
    (forall i: nat :: i < |runTimes| ==> runTimes[i] <= now) &&
    finalNextRunAt == candidates[|runTimes|] &&
    finalNextRunAt > now
  }

  function DuePrefixLength(now: nat, candidates: seq<nat>): nat
    decreases |candidates|
  {
    if |candidates| == 0 || candidates[0] > now then 0
    else 1 + DuePrefixLength(now, candidates[1..])
  }

  function PlannedRunTimes(now: nat, candidates: seq<nat>): seq<nat>
    requires ValidScheduleCandidateStream(now, candidates)
  {
    if DuePrefixLength(now, candidates) < |candidates| then candidates[..DuePrefixLength(now, candidates)] else []
  }

  function PlannedFinalNextRunAt(now: nat, candidates: seq<nat>): nat
    requires ValidScheduleCandidateStream(now, candidates)
  {
    if DuePrefixLength(now, candidates) < |candidates| then candidates[DuePrefixLength(now, candidates)] else 0
  }

  lemma FirstFutureBoundaryExists(now: nat, candidates: seq<nat>) returns (boundary: nat)
    requires ValidScheduleCandidateStream(now, candidates)
    ensures 0 < boundary < |candidates|
    ensures forall i: nat :: i < boundary ==> candidates[i] <= now
    ensures candidates[boundary] > now
    decreases |candidates|
  {
    if candidates[1] > now {
      boundary := 1;
    } else {
      var tailBoundary := FirstFutureBoundaryExists(now, candidates[1..]);
      boundary := tailBoundary + 1;
    }
  }

  lemma DuePrefixLengthMatchesBoundary(now: nat, candidates: seq<nat>, boundary: nat)
    requires boundary < |candidates|
    requires forall i: nat :: i < boundary ==> candidates[i] <= now
    requires candidates[boundary] > now
    ensures DuePrefixLength(now, candidates) == boundary
    decreases |candidates|
  {
    if boundary != 0 {
      DuePrefixLengthMatchesBoundary(now, candidates[1..], boundary - 1);
    }
  }

  lemma ValidStreamPlannedBoundary(now: nat, candidates: seq<nat>)
    requires ValidScheduleCandidateStream(now, candidates)
    ensures ExhaustedDuePrefixBoundary(now, candidates, PlannedRunTimes(now, candidates), PlannedFinalNextRunAt(now, candidates))
  {
    var boundary := FirstFutureBoundaryExists(now, candidates);
    DuePrefixLengthMatchesBoundary(now, candidates, boundary);
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

  method PlanScheduleBatch(now: nat, candidates: seq<nat>) returns (runTimes: seq<nat>, finalNextRunAt: nat)
    ensures |runTimes| == 0 || |runTimes| < |candidates|
    ensures |runTimes| == 0 || runTimes == candidates[..(|runTimes|)]
    ensures |runTimes| == 0 || forall i: nat :: i < |runTimes| ==> runTimes[i] <= now
    ensures |runTimes| == 0 || finalNextRunAt > now
    ensures |runTimes| == 0 || finalNextRunAt == candidates[(|runTimes|)]
    ensures ValidScheduleCandidateStream(now, candidates) ==> runTimes == PlannedRunTimes(now, candidates)
    ensures ValidScheduleCandidateStream(now, candidates) ==> finalNextRunAt == PlannedFinalNextRunAt(now, candidates)
    ensures ValidScheduleCandidateStream(now, candidates) ==> ExhaustedDuePrefixBoundary(now, candidates, runTimes, finalNextRunAt)
  {
    var i := 0;
    while i < |candidates| && candidates[i] <= now
      invariant 0 <= i <= |candidates|
      invariant forall j: nat :: j < i ==> candidates[j] <= now
    {
      i := i + 1;
    }

    if i == 0 || i == |candidates| {
      runTimes := [];
      finalNextRunAt := 0;
    } else {
      runTimes := candidates[..i];
      finalNextRunAt := candidates[i];
      if ValidScheduleCandidateStream(now, candidates) {
        DuePrefixLengthMatchesBoundary(now, candidates, i);
        assert runTimes == PlannedRunTimes(now, candidates);
        assert finalNextRunAt == PlannedFinalNextRunAt(now, candidates);
        ValidStreamPlannedBoundary(now, candidates);
      }
    }
  }

  method Main(args: seq<string>)
  {
    if |args| < 3 {
      print "ERR\n";
      return;
    }

    var start := 0;
    var okNow, now := ParseNat(args[0]);
    if !okNow && |args| > 1 {
      var shiftedOkNow, shiftedNow := ParseNat(args[1]);
      if shiftedOkNow {
        start := 1;
        okNow := true;
        now := shiftedNow;
      }
    }

    if !okNow {
      print "ERR\n";
      return;
    }

    var candidates: seq<nat> := [];
    var i := start + 1;
    while i < |args|
      invariant start + 1 <= i <= |args|
    {
      var okCandidate, candidate := ParseNat(args[i]);
      if !okCandidate {
        print "ERR\n";
        return;
      }
      candidates := candidates + [candidate];
      i := i + 1;
    }

    var runTimes, finalNextRunAt := PlanScheduleBatch(now, candidates);
    if |runTimes| == 0 {
      print "ERR\n";
      return;
    }

    print finalNextRunAt, "\n";
    print |runTimes|, "\n";

    i := 0;
    while i < |runTimes|
      invariant 0 <= i <= |runTimes|
    {
      print runTimes[i], "\n";
      i := i + 1;
    }
  }
}
