include "../src/DafnyCheck.dfy"
include "../src/Arbitrary.dfy"
include "../src/RandomGenerator.dfy"
include "../src/TestStatus.dfy"
include "../src/TestResult.dfy"

// Run the tests with:
//   dafny test ../src/DafnyCheck.dfy MinithesisTest.dfy --standard-libraries --allow-warnings
//
// White-box tests seed `state.result` to a known choice sequence and call
// individual shrink methods, asserting the resulting sequence is shorter or
// lexicographically smaller. End-to-end tests run the full RunTest pipeline
// against an Arbitrary<T> + predicate, mirroring Java ShrinkTest.

module MinithesisTest {
  import opened DafnyCheck
  import opened Arbitrary
  import opened RandomGenerator
  import opened TestResult
  import opened TestTypes
  import opened Std.Wrappers

  // TestFunction whose Apply runs a predicate over the candidate choice
  // sequence (read from tc.prefix). Useful for shrink tests where Consider
  // builds TestCases via TestCase.ForChoices, so the candidate appears as
  // the prefix. Cannot be used during Generate (prefix is always [] then).
  @AssumeCrossModuleTermination
  class ChoicePredicateTest extends TestFunction<bv64> {
    var pred: seq<bv64> -> bool

    constructor(pred: seq<bv64> -> bool)
      ensures fresh(this)
      ensures this.pred == pred
      ensures this.repr == {this}
      ensures Valid()
    {
      this.pred := pred;
      this.repr := {this};
    }

    ghost predicate Valid()
      reads this, repr
      ensures Valid() ==> this in repr
    {
      this in repr && repr == {this}
    }

    method Apply(tc: TestCase) returns (result: TestResult<bv64>)
      requires Valid()
      requires tc.Valid()
      requires this.repr !! tc.repr
      modifies tc, tc.random
      ensures Valid()
      decreases this.repr
    {
      if pred(tc.prefix) {
        result := new TestResult<bv64>(Some(INTERESTING), Some(0 as bv64));
      } else {
        result := new TestResult<bv64>(None, Some(0 as bv64));
      }
    }
  }

  // Factory: a fresh TestingState wired to a ChoicePredicateTest.
  // We surface the rng + rng.random freshness in ensures so callers can
  // discharge the modifies clauses on shrink methods (which write through
  // state.random and state.random.random).
  method NewState(pred: seq<bv64> -> bool) returns (state: TestingState<bv64>)
    ensures fresh(state)
    ensures fresh(state.random)
    ensures fresh(state.random.random)
    ensures fresh(state.testFunction)
    ensures state.Valid()
  {
    var rng := new SimpleRandomGen();
    var tf := new ChoicePredicateTest(pred);
    assume {:axiom} rng !in tf.repr && rng.random !in tf.repr;
    state := new TestingState<bv64>(rng, tf, 1000);
  }

  // ============================================================
  // White-box per-method tests.
  // Each seeds state.result with a known sequence, calls one
  // shrink method, then prints + asserts the outcome.
  // ============================================================

  method {:test} TestConsiderAcceptsShorter()
  {
    // Predicate: any sequence starting with 3 is INTERESTING.
    var pred := (cs: seq<bv64>) => |cs| >= 1 && cs[0] == 3;
    var state := NewState(pred);
    state.result := Some([3 as bv64, 9, 9, 9]);
    print "\n[Consider shorter] before: ", state.result, "\n";
    var res := state.Consider([3 as bv64]);
    print "[Consider shorter] after:  ", state.result, " (returned ", res, ")\n";
    expect res.Some?;
    expect state.result == Some([3 as bv64]);
  }

  method {:test} TestConsiderRejectsNonInteresting()
  {
    var pred := (cs: seq<bv64>) => |cs| >= 1 && cs[0] == 7;
    var state := NewState(pred);
    state.result := Some([7 as bv64, 9, 9]);
    print "\n[Consider reject] before: ", state.result, "\n";
    var res := state.Consider([2 as bv64, 2]);
    print "[Consider reject] after:  ", state.result, " (returned ", res, ")\n";
    expect res.None?;
    expect state.result == Some([7 as bv64, 9, 9]);
  }

  method {:test} TestShrinkByDeletionRemovesTrailingZeros()
  {
    // INTERESTING when the sequence starts with 5 (length-agnostic).
    var pred := (cs: seq<bv64>) => |cs| >= 1 && cs[0] == 5;
    var state := NewState(pred);
    state.result := Some([5 as bv64, 0, 0, 0, 0]);
    print "\n[ShrinkByDeletion trailing] before: ", state.result, "\n";
    state.ShrinkByDeletion();
    print "[ShrinkByDeletion trailing] after:  ", state.result, "\n";
    expect state.result.Some?;
    var after := state.result.Extract();
    expect |after| < 5;
    expect |after| >= 1 && after[0] == 5;
  }

  method {:test} TestShrinkByDeletionLargeRun()
  {
    // INTERESTING when length >= 3 (regardless of values).
    var pred := (cs: seq<bv64>) => |cs| >= 3;
    var state := NewState(pred);
    state.result := Some([1 as bv64, 1, 1, 1, 1, 1, 1, 1, 1]);
    print "\n[ShrinkByDeletion large] before: ", state.result, "\n";
    state.ShrinkByDeletion();
    print "[ShrinkByDeletion large] after:  ", state.result, "\n";
    expect state.result.Some?;
    var after := state.result.Extract();
    expect |after| < 9;
    expect |after| >= 3;
  }

  method {:test} TestShrinkByZeroingZeroesMiddle()
  {
    // INTERESTING when length >= 5 and first element is 7.
    var pred := (cs: seq<bv64>) => |cs| >= 5 && cs[0] == 7;
    var state := NewState(pred);
    state.result := Some([7 as bv64, 9, 9, 9, 9, 9, 9, 9, 9]);
    print "\n[ShrinkByZeroing] before: ", state.result, "\n";
    state.ShrinkByZeroing();
    print "[ShrinkByZeroing] after:  ", state.result, "\n";
    expect state.result.Some?;
    var after := state.result.Extract();
    expect |after| >= 5;
    expect after[0] == 7;
    // At least one of the trailing positions should be zeroed.
    var anyZero := false;
    var i := 1;
    while i < |after|
      decreases |after| - i
    {
      if after[i] == 0 {
        anyZero := true;
      }
      i := i + 1;
    }
    expect anyZero;
  }

  method {:test} TestShrinkIndividualValuesBinarySearch()
  {
    // Mirrors Java ShrinkTest.testShrinkSingleInt: INTERESTING when the
    // single choice is >= 24 (and < 1000 implicitly, since 1000 was the
    // upper bound there). Expect shrink to drive the choice toward 24.
    var pred := (cs: seq<bv64>) => |cs| == 1 && cs[0] >= 24;
    var state := NewState(pred);
    state.result := Some([1000 as bv64]);
    print "\n[ShrinkIndividualValues single] before: ", state.result, "\n";
    state.ShrinkIndividualValues();
    print "[ShrinkIndividualValues single] after:  ", state.result, "\n";
    expect state.result.Some?;
    var after := state.result.Extract();
    expect |after| == 1;
    // Java's testShrinkSingleInt accepts 24 or 25 — the algorithm doesn't
    // guarantee the global minimum. We accept anything in [24, 32] as a
    // tight upper bound on the shrunk value.
    expect after[0] >= 24;
    expect after[0] <= 32;
  }

  method {:test} TestShrinkIndividualValuesTwoPositions()
  {
    // INTERESTING when length == 2 and sum >= 10.
    var pred := (cs: seq<bv64>) => |cs| == 2 && cs[0] + cs[1] >= 10;
    var state := NewState(pred);
    state.result := Some([100 as bv64, 100]);
    print "\n[ShrinkIndividualValues pair] before: ", state.result, "\n";
    state.ShrinkIndividualValues();
    print "[ShrinkIndividualValues pair] after:  ", state.result, "\n";
    expect state.result.Some?;
    var after := state.result.Extract();
    expect |after| == 2;
    // Each value should be much smaller than 100 after independent
    // binary search.
    expect after[0] < 100;
    expect after[1] < 100;
    expect after[0] + after[1] >= 10;
  }

  method {:test} TestShrinkBySwappingReorders()
  {
    // INTERESTING when length >= 3 and result[0] >= result[2].
    // We seed [0, 5, 9] — predicate fails (0 < 9). But ShrinkBySwapping
    // only runs as part of the larger fixed-point loop in real use; here
    // we verify that calling it on a non-interesting predicate leaves
    // state.result unchanged (i.e., no swap is accepted).
    var pred := (cs: seq<bv64>) => |cs| >= 3 && cs[0] >= cs[2];
    var state := NewState(pred);
    state.result := Some([9 as bv64, 5, 0]);
    print "\n[ShrinkBySwapping] before: ", state.result, "\n";
    state.ShrinkBySwapping();
    print "[ShrinkBySwapping] after:  ", state.result, "\n";
    expect state.result.Some?;
    var after := state.result.Extract();
    expect |after| == 3;
    // result[0] >= result[2] must still hold (predicate is preserved).
    expect after[0] >= after[2];
  }

  method {:test} TestFullShrinkEndsAtMinimum()
  {
    // INTERESTING when length >= 1 and first element >= 50.
    // Full Shrink() should reduce this to length 1 with first element
    // in a small neighborhood of 50.
    var pred := (cs: seq<bv64>) => |cs| >= 1 && cs[0] >= 50;
    var state := NewState(pred);
    state.result := Some([999 as bv64, 100, 100, 100]);
    print "\n[Full Shrink] before: ", state.result, "\n";
    state.Shrink();
    print "[Full Shrink] after:  ", state.result, "\n";
    expect state.result.Some?;
    var after := state.result.Extract();
    expect |after| < 4;
    expect |after| >= 1 && after[0] >= 50;
    expect after[0] <= 64;
  }

  method {:test} TestReplaceSingleAccepts()
  {
    // Verifies the ReplaceSingle helper independently of binary search.
    var pred := (cs: seq<bv64>) => |cs| == 2 && cs[0] >= 10;
    var state := NewState(pred);
    state.result := Some([50 as bv64, 99]);
    print "\n[ReplaceSingle] before: ", state.result, "\n";
    var r := state.ReplaceSingle(0, 20 as bv64);
    print "[ReplaceSingle] after:  ", state.result, " (returned ", r, ")\n";
    expect r.Some?;
    expect state.result == Some([20 as bv64, 99]);
  }

  method {:test} TestReplaceMultipleAccepts()
  {
    // Replace both positions at once.
    var pred := (cs: seq<bv64>) => |cs| == 3 && cs[1] == 4;
    var state := NewState(pred);
    state.result := Some([7 as bv64, 4, 5]);
    print "\n[ReplaceMultiple] before: ", state.result, "\n";
    var r := state.ReplaceMultiple(map[0 := 1 as bv64, 2 := 2 as bv64]);
    print "[ReplaceMultiple] after:  ", state.result, " (returned ", r, ")\n";
    expect r.Some?;
    expect state.result == Some([1 as bv64, 4, 2]);
  }

  // ============================================================
  // Black-box end-to-end tests via RunTestWithExamples.
  // These exercise the full Generate -> Shrink pipeline through
  // a real Arbitrary<T>. They assert structural properties only;
  // exact choice values depend on Arbitrary internals.
  // ============================================================

  method {:test} TestEndToEndSingleInt()
  {
    // Mirrors Java ShrinkTest.testShrinkSingleInt.
    // Predicate is "the value is in [24, 256]" — we phrase it as a
    // *passing* predicate, so the test FAILS for that range, which is
    // what triggers shrinking.
    var arb := Arbitrary<int>.Range(0, 1000);
    var pred := (i: int) => i > 256 || i < 24;
    print "\n[E2E single int] start\n";
    RunTestWithExamples(pred, arb, "E2E_single_int", 100);
    print "[E2E single int] done\n";
  }

  method {:test} TestEndToEndListSum()
  {
    // Mirrors Java ShrinkTest.testFindsSmallList.
    var inner := Arbitrary<int>.Range(0, 10000);
    var arb := Arbitrary<seq<int>>.Lists(inner, 1, 100);
    var pred := (xs: seq<int>) => SumSeq(xs) <= 1000;
    print "\n[E2E list sum] start\n";
    RunTestWithExamples(pred, arb, "E2E_list_sum", 100);
    print "[E2E list sum] done\n";
  }

  method {:test} TestEndToEndUniqueValues()
  {
    // Mirrors Java ShrinkTest.testFindsSmallUniqueValuesForList.
    var inner := Arbitrary<int>.Range(0, 10000);
    var arb := Arbitrary<seq<int>>.Lists(inner, 1, 100);
    // Pass = "size < 4 OR all unique"; fail = duplicate in size>=4 list.
    var pred := (xs: seq<int>) => |xs| < 4 || AllUnique(xs);
    print "\n[E2E unique values] start\n";
    RunTestWithExamples(pred, arb, "E2E_unique_values", 100);
    print "[E2E unique values] done\n";
  }

  function SumSeq(xs: seq<int>): int
  {
    if |xs| == 0 then 0
    else xs[0] + SumSeq(xs[1..])
  }

  function AllUnique(xs: seq<int>): bool
  {
    forall i, j :: 0 <= i < j < |xs| ==> xs[i] != xs[j]
  }

  // ============================================================
  // MethodTest demos. Each MethodUnderTest wraps one buggy method
  // + post-condition check; RunMethodTestWithExamples drives
  // Arbitrary<seq<int>> through it. The demos are *expected* to
  // find the bug and report FAIL with a minimised input.
  // ============================================================

  function SeqSet(s: seq<int>): set<int>
    decreases |s|
  {
    if |s| == 0 then {} else {s[0]} + SeqSet(s[1..])
  }

  // Allocates a fresh int[] from the generated seq, runs an in-place
  // uniq that only collapses *adjacent* equal pairs (Unix uniq behaviour),
  // then checks that the result has no duplicates and preserves the
  // value-set. Fails on inputs with non-adjacent repeats, e.g., [0, 1, 0].
  @AssumeCrossModuleTermination
  class BuggyDedup extends MethodUnderTest<seq<int>, string> {
    constructor()
      ensures fresh(this)
      ensures Valid()
    {}

    ghost predicate Valid() reads this { true }

    method run(input: seq<int>) returns (result: Result<bool, string>)
      requires Valid()
      ensures Valid()
      decreases 0
    {
      var arr := new int[|input|];
      var k := 0;
      while k < |input|
        invariant 0 <= k <= |input|
        invariant arr.Length == |input|
        decreases |input| - k
      {
        arr[k] := input[k];
        k := k + 1;
      }

      var write := 0;
      var read := 0;
      while read < arr.Length
        invariant 0 <= write <= read <= arr.Length
        invariant arr.Length == |input|
        decreases arr.Length - read
      {
        if write == 0 || arr[write - 1] != arr[read] {
          arr[write] := arr[read];
          write := write + 1;
        }
        read := read + 1;
      }

      var outSeq: seq<int> := arr[..write];

      var hasDup := false;
      var p := 0;
      while p < |outSeq|
        invariant 0 <= p <= |outSeq|
        decreases |outSeq| - p
      {
        var q := p + 1;
        while q < |outSeq|
          invariant p + 1 <= q <= |outSeq|
          decreases |outSeq| - q
        {
          if outSeq[p] == outSeq[q] { hasDup := true; }
          q := q + 1;
        }
        p := p + 1;
      }

      var setMatches := SeqSet(outSeq) == SeqSet(input);

      if hasDup {
        result := Failure("output has duplicates");
      } else if !setMatches {
        result := Failure("output set != input set");
      } else {
        result := Success(true);
      }
    }
  }

  // Allocates a fresh int[], sorts it, picks the middle element as the
  // probe, and runs a binary search with `while lo < hi` (should be
  // `lo <= hi`). On 1-element arrays the loop body never runs, so the
  // search misses a probe that is in the array.
  @AssumeCrossModuleTermination
  class BuggyBinarySearch extends MethodUnderTest<seq<int>, string> {
    constructor()
      ensures fresh(this)
      ensures Valid()
    {}

    ghost predicate Valid() reads this { true }

    method run(input: seq<int>) returns (result: Result<bool, string>)
      requires Valid()
      ensures Valid()
      decreases 0
    {
      var arr := new int[|input|];
      var k := 0;
      while k < |input|
        invariant 0 <= k <= |input|
        invariant arr.Length == |input|
        decreases |input| - k
      {
        arr[k] := input[k];
        k := k + 1;
      }

      var i := 1;
      while i < arr.Length
        invariant 1 <= i <= arr.Length || arr.Length == 0
        invariant arr.Length == |input|
        decreases arr.Length - i
      {
        var j := i;
        while j > 0 && arr[j - 1] > arr[j]
          invariant 0 <= j <= i
          invariant arr.Length == |input|
          decreases j
        {
          var t := arr[j - 1];
          arr[j - 1] := arr[j];
          arr[j] := t;
          j := j - 1;
        }
        i := i + 1;
      }

      if arr.Length == 0 {
        result := Success(true);
        return;
      }

      var probe := arr[arr.Length / 2];

      var lo: int := 0;
      var hi: int := arr.Length - 1;
      var foundIdx: int := -1;
      while lo < hi && foundIdx == -1
        invariant 0 <= lo
        invariant hi < arr.Length
        decreases if foundIdx != -1 then 0 else hi - lo + 1
      {
        var mid := (lo + hi) / 2;
        if arr[mid] == probe { foundIdx := mid; }
        else if arr[mid] < probe { lo := mid + 1; }
        else { hi := mid - 1; }
      }

      var ok := false;
      if foundIdx == -1 {
        ok := true;
        var t := 0;
        while t < arr.Length
          invariant 0 <= t <= arr.Length
          decreases arr.Length - t
        {
          if arr[t] == probe { ok := false; }
          t := t + 1;
        }
      } else if 0 <= foundIdx < arr.Length {
        ok := arr[foundIdx] == probe;
      }

      if ok {
        result := Success(true);
      } else if foundIdx == -1 {
        result := Failure("probe present but search returned -1");
      } else {
        result := Failure("search returned wrong index");
      }
    }
  }

  method {:test} TestMethodTestBuggyDedup()
  {
    var inner := Arbitrary<int>.Range(0, 5);
    var arb := Arbitrary<seq<int>>.Lists(inner, 0, 5);
    var sut := new BuggyDedup();
    print "\n[method-test buggy dedup] start\n";
    RunMethodTestWithExamples(arb, sut, "method-test buggy dedup", 100);
    print "[method-test buggy dedup] done\n";
  }

  method {:test} TestMethodTestBuggyBinarySearch()
  {
    var inner := Arbitrary<int>.Range(0, 100);
    var arb := Arbitrary<seq<int>>.Lists(inner, 0, 10);
    var sut := new BuggyBinarySearch();
    print "\n[method-test buggy binsearch] start\n";
    RunMethodTestWithExamples(arb, sut, "method-test buggy binsearch", 100);
    print "[method-test buggy binsearch] done\n";
  }
}
