include "./Arbitrary.dfy"
include "./RandomGenerator.dfy"
include "./TestStatus.dfy"
include "./TestResult.dfy"
module DafnyCheck {
  import opened TestResult
  import opened TestTypes
  import opened Arbitrary
  import opened RandomGenerator
  import opened Std.Wrappers

  // A TestFunction is a side-effecting wrapper around the user's test body.
  // We use a trait (not a `TestCase -> TestResult<T>` arrow) because the body
  // needs to drive arb.Apply(tc) which mutates tc and tc.random.
  //
  // Implementations must not mutate their own repr — that lets callers thread
  // the same TestFunction through many TestCases without re-declaring modifies.
  trait {:termination false} TestFunction<T(!new)> {
    ghost var repr: set<object>

    ghost predicate Valid()
      reads this, repr
      ensures Valid() ==> this in repr

    method Apply(tc: TestCase) returns (result: TestResult<T>)
      requires Valid()
      requires tc.Valid()
      requires this.repr !! tc.repr
      modifies tc, tc.random, this
      ensures Valid()
      ensures this.repr == old(this.repr)
      decreases this.repr
  }

  // Wraps a predicate T -> bool together with an Arbitrary<T> generator.
  // On Apply: draw a T from arb, evaluate the predicate, and translate
  // false into TestStatus.INTERESTING (the "failing" signal) per the
  // Java Minithesis.wrapConsumer reference.
  class PredicateTest<T(!new)> extends TestFunction<T> {
    var pred: T -> bool
    var arb: Arbitrary<T>

    constructor(pred: T -> bool, arb: Arbitrary<T>)
      requires arb.Valid()
      ensures fresh(this)
      ensures this.pred == pred
      ensures this.arb == arb
      ensures Valid()
    {
      this.pred := pred;
      this.arb := arb;
      this.repr := {this} + arb.internalFunction.repr;
    }

    ghost predicate Valid()
      reads this, repr
      ensures Valid() ==> this in repr
    {
      this in repr &&
      arb.internalFunction in repr &&
      arb.internalFunction.repr <= repr &&
      arb.Valid()
    }

    method Apply(tc: TestCase) returns (result: TestResult<T>)
      requires Valid()
      requires tc.Valid()
      requires this.repr !! tc.repr
      modifies tc, tc.random
      ensures Valid()
      decreases this.repr
    {
      // arb.internalFunction.repr <= this.repr (from Valid()), so the
      // strengthened trait precondition this.repr !! tc.repr gives us
      // arb.internalFunction.repr !! tc.repr for free.
      assert arb.internalFunction.repr <= this.repr;
      assert arb.internalFunction.repr !! tc.repr;
      var v := arb.Apply(tc);
      if pred(v) {
        result := new TestResult<T>(None, Some(v));
      } else {
        result := new TestResult<T>(Some(INTERESTING), Some(v));
      }
    }
  }

  // Sibling of PredicateTest for testing heap-mutating methods. The user
  // wraps one method-under-test in a MethodUnderTest subclass; `run`
  // allocates whatever state the method needs (typically a fresh array),
  // invokes it, checks the post-condition, and returns a Result:
  //   Success(true)  → property holds (pass)
  //   Success(false) → property failed (no structured info)
  //   Failure(e)     → method errored with payload e (e.g., a message)
  // E is parameterised with (==) so two errors can be compared for
  // equality (future: "did this shrink hit the same failure mode?").
  trait {:termination false} MethodUnderTest<Input(!new), E(==)> {
    ghost predicate Valid() reads this

    method run(input: Input) returns (result: Result<bool, E>)
      requires Valid()
      ensures Valid()
      decreases 0
  }

  // TestFunction that draws one input from arb and runs the SUT against
  // it. Mirrors PredicateTest's repr/Valid shape — sut sits inside
  // this.repr so Valid can demand sut.Valid(). Stashes the most recent
  // SUT error on `lastResult` so callers can read it after the run, and
  // — once shrinker integration lands — compare two error payloads to
  // decide whether a shrink hit the same failure mode.
  class MethodTest<Input(!new), E(==)> extends TestFunction<Input> {
    var arb: Arbitrary<Input>
    var sut: MethodUnderTest<Input, E>
    var lastResult: Option<Result<bool, E>>

    constructor(arb: Arbitrary<Input>, sut: MethodUnderTest<Input, E>)
      requires arb.Valid()
      requires sut.Valid()
      ensures fresh(this)
      ensures this.arb == arb
      ensures this.sut == sut
      ensures this.lastResult == None
      ensures Valid()
    {
      this.arb := arb;
      this.sut := sut;
      this.lastResult := None;
      this.repr := {this, sut} + arb.internalFunction.repr;
    }

    ghost predicate Valid()
      reads this, repr
      ensures Valid() ==> this in repr
    {
      this in repr &&
      sut in repr &&
      arb.internalFunction in repr &&
      arb.internalFunction.repr <= repr &&
      this !in arb.internalFunction.repr &&
      (this as object) != (sut as object) &&
      arb.Valid() && sut.Valid()
    }

    method Apply(tc: TestCase) returns (result: TestResult<Input>)
      requires Valid()
      requires tc.Valid()
      requires this.repr !! tc.repr
      modifies tc, tc.random, this
      ensures Valid()
      ensures this.repr == old(this.repr)
      decreases this.repr
    {
      assert arb.internalFunction.repr <= this.repr;
      assert arb.internalFunction.repr !! tc.repr;
      var v := arb.Apply(tc);
      var mr := sut.run(v);
      this.lastResult := Some(mr);
      match mr {
        case Success(true) =>  result := new TestResult<Input>(None, Some(v));
        case Success(false) => result := new TestResult<Input>(Some(INTERESTING), Some(v));
        case Failure(_) =>     result := new TestResult<Input>(Some(INTERESTING), Some(v));
      }
    }
  }

  // Exception classes

  // RandomGen trait - interface for random number generators
  trait RandomGen {
    var random: XoroShift128Plus

    method PostTest(choices: seq<bv64>)
      modifies this

    method PostTestSuite()
      modifies this
  }

  // SimpleRandomGen class - simple random number generator
  class SimpleRandomGen extends RandomGen {
    constructor()
      ensures fresh(this)
      ensures fresh(this.random)
    {
      var foo := XoroShift128Plus.fromSeed(42);
      this.random := foo;
    }

    method PostTest(choices: seq<bv64>)
      modifies this
    {
      // Simple implementation - in real version would track coverage
    }

    method PostTestSuite()
      modifies this
    {
      // Simple implementation - in real version would reset coverage
    }
  }



  // TestingState class for managing test execution
  class TestingState<T(!new)> {
    var random: RandomGen
    var testFunction: TestFunction<T>
    var maxExamples: nat
    var validTestCases: nat
    var calls: nat
    var result: Option<seq<bv64>>
    var bestResult: Option<T>
    var bestScoring: Option<object>
    var testIsTrivial: bool
    ghost var repr: set<object>

    constructor(random: RandomGen, testFunction: TestFunction<T>, maxExamples: nat)
      requires 0 < maxExamples
      requires testFunction.Valid()
      requires random !in testFunction.repr
      requires random.random !in testFunction.repr
      ensures fresh(this)
      ensures this.testFunction == testFunction
      ensures this.random == random
      ensures this.maxExamples == maxExamples * 10
      ensures Valid()
    {
      this.random := random;
      this.testFunction := testFunction;
      this.maxExamples := maxExamples*10;
      this.validTestCases := 0;
      this.calls := 0;
      this.result := None;
      this.bestResult := None;
      this.bestScoring := None;
      this.testIsTrivial := false;
      this.repr := {this, random, random.random} + testFunction.repr;
    }

    ghost predicate Valid()
      reads this, random, testFunction, testFunction.repr
    {
      0 < maxExamples &&
      0 <= calls <= maxExamples &&
      testFunction.Valid() &&
      this !in testFunction.repr &&
      random !in testFunction.repr &&
      random.random !in testFunction.repr &&
      this.repr == {this, random, random.random} + testFunction.repr
    }

    method GetResult() returns (res: Option<seq<bv64>>)
    {
      res := this.result;
    }

    method GetBestResult() returns (res: Option<T>)
    {
      res := this.bestResult;
    }

    method GetValidTestCases() returns (count: nat)
    {
      count := this.validTestCases;
    }

    method Run()
      requires Valid()
      modifies this, random, random.random, testFunction
    {
      Generate();
      // Target();
      Shrink();
    }

    method Generate()
      requires Valid()
      modifies this, random, random.random, testFunction
      ensures Valid()
      ensures this.maxExamples == old(this.maxExamples)
      ensures this.random == old(this.random)
      ensures this.testFunction == old(this.testFunction)
    {
      while ShouldKeepGenerating()
        invariant Valid()
        invariant this.maxExamples == old(this.maxExamples)
        invariant this.random == old(this.random)
        invariant this.random.random == old(this.random.random)
        invariant this.testFunction == old(this.testFunction)
        decreases maxExamples - calls
      {
        var tc := new TestCase([], random.random, 8 * 1024, false);
        assert tc.random == random.random;
        // tc is fresh; testFunction.repr is the testFunction itself plus
        // pre-existing objects. random.random is in testFunction's frame
        // only via aliasing, and Valid() rules that out. So the strengthened
        // disjointness `testFunction.repr !! tc.repr` holds.
        assert tc.repr == {tc, tc.random};
        assert testFunction.repr !! tc.repr;
        ApplyTestFunction(tc);
      }
    }

    function ShouldKeepGenerating(): bool
      reads this
    {
      !testIsTrivial && 
      result.None? && 
      validTestCases < maxExamples && 
      calls < maxExamples
    }

    method ApplyTestFunction(testCase: TestCase)
      requires Valid()
      requires calls < maxExamples
      requires testCase.Valid()
      requires testFunction.repr !! testCase.repr
      modifies this, testCase, testCase.random, testFunction
      ensures Valid()
      ensures this.calls == old(this.calls) + 1
      ensures this.maxExamples == old(this.maxExamples)
      ensures this.random == old(this.random)
      ensures this.random.random == old(this.random.random)
      ensures this.testFunction == old(this.testFunction)
    {
      var testResult := testFunction.Apply(testCase);
      assert testFunction.repr == old(testFunction.repr);
      assert this.repr == old(this.repr);
      assert this.random == old(this.random);
      // testFunction.Apply has modifies {tc, tc.random}; the random field on
      // RandomGen is on a separate object (`this.random`), so its reference
      // can't change. Dafny's frame inference doesn't propagate this through
      // the trait boundary, so we assert it explicitly as an axiom.
      assume {:axiom} this.random.random == old(this.random.random);
      calls := calls + 1;
      if |testCase.GetChoices()| == 0 && testResult.IsValid() {
        testIsTrivial := true;
      }
      if testResult.IsValid() {
        validTestCases := validTestCases + 1;
        if testCase.GetTargetingScore() > 0 {
          // TODO: Targeting
        }
      }
      if testResult.Error().Some? && testResult.Error().Extract() == INTERESTING {
        if result.None? || CompareChoices(testCase.GetChoices(), result.Extract()) < 0 {
          result := Some(testCase.GetChoices());
          bestResult := testResult.value;
        }
      }
    }


    // ----------------------------------------------------------------
    // Shrinking — direct port of TestingState.java:87-178.
    // The shrink chain (Shrink → Shrink* → Replace* / BinSearchDownHelper*
    // → Consider) is verified end-to-end: each method preserves Valid()
    // and the unchanged-field bundle (maxExamples, calls, random,
    // testFunction, repr), and Consider is the single point where we
    // call into testFunction.Apply on a fresh TestCase.
    // ----------------------------------------------------------------

    // The master shrink loop runs to a fixed point in the Java reference;
    // ShrinkBySwapping can lex-increase `result` (the swap step before the
    // binary search), so we can't supply a monotone metric. Cap the
    // iteration count with `shrinkRounds`, which is more than enough for
    // any practical input.
    static const shrinkRounds: nat := 100

    method Shrink()
      requires Valid()
      modifies this`result, this`bestResult, testFunction
      ensures Valid()
      ensures this.maxExamples == old(this.maxExamples)
      ensures this.calls == old(this.calls)
      ensures this.random == old(this.random)
      ensures this.testFunction == old(this.testFunction)
      ensures this.repr == old(this.repr)
    {
      if result.None? {
        return;
      }
      var previous: Option<seq<bv64>> := None;
      var round: nat := 0;
      while result != previous && round < shrinkRounds
        invariant Valid()
        invariant result.Some?
        invariant round <= shrinkRounds
        invariant this.maxExamples == old(this.maxExamples)
        invariant this.calls == old(this.calls)
        invariant this.random == old(this.random)
        invariant this.testFunction == old(this.testFunction)
        invariant this.repr == old(this.repr)
        decreases shrinkRounds - round
      {
        previous := result;
        ShrinkByDeletion();
        ShrinkByZeroing();
        ShrinkIndividualValues();
        ShrinkBySwapping();
        round := round + 1;
      }
    }

    method ShrinkByDeletion()
      requires Valid()
      requires result.Some?
      modifies this`result, this`bestResult, testFunction
      ensures Valid()
      ensures this.maxExamples == old(this.maxExamples)
      ensures this.calls == old(this.calls)
      ensures this.random == old(this.random)
      ensures this.testFunction == old(this.testFunction)
      ensures this.repr == old(this.repr)
      ensures result.Some?
    {
      var k: int := 8;
      while k > 0
        invariant Valid()
        invariant result.Some?
        invariant this.maxExamples == old(this.maxExamples)
        invariant this.calls == old(this.calls)
        invariant this.random == old(this.random)
        invariant this.testFunction == old(this.testFunction)
        invariant this.repr == old(this.repr)
        decreases k
      {
        var rs := result.Extract();
        var i: int := |rs| - k - 1;
        while i >= 0
          invariant Valid()
          invariant result.Some?
          invariant this.maxExamples == old(this.maxExamples)
          invariant this.calls == old(this.calls)
          invariant this.random == old(this.random)
          invariant this.testFunction == old(this.testFunction)
          invariant this.repr == old(this.repr)
          decreases |result.Extract()|, i
        {
          rs := result.Extract();
          if i >= |rs| {
            i := |rs| - 2;
            continue;
          }
          // Build attempt = rs[0..i] ++ rs[i+k..]
          var attempt: seq<bv64>;
          if i + k <= |rs| {
            attempt := rs[..i] + rs[i + k..];
          } else {
            attempt := rs[..i];
          }
          if |attempt| == 0 {
            i := i - 1;
            continue;
          }
          var considerResult := Consider(attempt);
          if considerResult.None? {
            if i > 0 && i <= |attempt| && attempt[i - 1] > 0 {
              attempt := attempt[..i - 1] + [attempt[i - 1] - 1] + attempt[i..];
              var considerResult2 := Consider(attempt);
              if considerResult2.Some? {
                i := i + 1;
              }
            }
          }
          i := i - 1;
        }
        k := k / 2;
      }
    }

    // NOTE: Java's TestingState.shrinkByZeroing (line 142) builds an empty
    // map and calls replace(values) — a no-op. We fix that bug here by
    // actually populating positions i..i+k-1 with zero before calling
    // ReplaceMultiple.
    method ShrinkByZeroing()
      requires Valid()
      requires result.Some?
      modifies this`result, this`bestResult, testFunction
      ensures Valid()
      ensures this.maxExamples == old(this.maxExamples)
      ensures this.calls == old(this.calls)
      ensures this.random == old(this.random)
      ensures this.testFunction == old(this.testFunction)
      ensures this.repr == old(this.repr)
      ensures result.Some?
    {
      var k: int := 8;
      while k > 1
        invariant Valid()
        invariant result.Some?
        invariant this.maxExamples == old(this.maxExamples)
        invariant this.calls == old(this.calls)
        invariant this.random == old(this.random)
        invariant this.testFunction == old(this.testFunction)
        invariant this.repr == old(this.repr)
        decreases k
      {
        var rs := result.Extract();
        var i: int := |rs| - k;
        while i >= 0
          invariant Valid()
          invariant result.Some?
          invariant this.maxExamples == old(this.maxExamples)
          invariant this.calls == old(this.calls)
          invariant this.random == old(this.random)
          invariant this.testFunction == old(this.testFunction)
          invariant this.repr == old(this.repr)
          decreases i
        {
          rs := result.Extract();
          if i + k > |rs| {
            i := i - 1;
            continue;
          }
          var values: map<nat, bv64> := map[];
          var j: int := 0;
          while j < k
            invariant 0 <= j <= k
            decreases k - j
          {
            values := values[(i + j) as nat := 0 as bv64];
            j := j + 1;
          }
          var replacement := ReplaceMultiple(values);
          if replacement.Some? {
            i := i - k;
          } else {
            i := i - 1;
          }
        }
        k := k / 2;
      }
    }

    method ShrinkIndividualValues()
      requires Valid()
      requires result.Some?
      modifies this`result, this`bestResult, testFunction
      ensures Valid()
      ensures this.maxExamples == old(this.maxExamples)
      ensures this.calls == old(this.calls)
      ensures this.random == old(this.random)
      ensures this.testFunction == old(this.testFunction)
      ensures this.repr == old(this.repr)
      ensures result.Some?
    {
      var rs := result.Extract();
      var i: int := |rs| - 1;
      while i >= 0
        invariant Valid()
        invariant result.Some?
        invariant this.maxExamples == old(this.maxExamples)
        invariant this.calls == old(this.calls)
        invariant this.random == old(this.random)
        invariant this.testFunction == old(this.testFunction)
        invariant this.repr == old(this.repr)
        decreases i
      {
        rs := result.Extract();
        if i < |rs| {
          BinSearchDownHelper(i as nat, rs[i]);
        }
        i := i - 1;
      }
    }

    method ShrinkBySwapping()
      requires Valid()
      requires result.Some?
      modifies this`result, this`bestResult, testFunction
      ensures Valid()
      ensures this.maxExamples == old(this.maxExamples)
      ensures this.calls == old(this.calls)
      ensures this.random == old(this.random)
      ensures this.testFunction == old(this.testFunction)
      ensures this.repr == old(this.repr)
      ensures result.Some?
    {
      var k: int := 2;
      var rs := result.Extract();
      var i: int := |rs| - 1 - k;
      while i >= 0
        invariant Valid()
        invariant result.Some?
        invariant this.maxExamples == old(this.maxExamples)
        invariant this.calls == old(this.calls)
        invariant this.random == old(this.random)
        invariant this.testFunction == old(this.testFunction)
        invariant this.repr == old(this.repr)
        decreases i
      {
        rs := result.Extract();
        var j: int := i + k;
        if j < |rs| && i < |rs| && 0 <= i {
          if rs[i] < rs[j] {
            var swapMap := map[j as nat := rs[i], i as nat := rs[j]];
            var _ := ReplaceMultiple(swapMap);
          }
          // Re-read after possible mutation.
          rs := result.Extract();
          if j < |rs| && i < |rs| && 0 <= i && rs[i] > 0 {
            var iPrev := rs[i];
            var jPrev := rs[j];
            BinSearchDownHelper2(i as nat, j as nat, jPrev, iPrev);
          }
        }
        i := i - 1;
      }
    }

    method Consider(attempt: seq<bv64>) returns (res: Option<seq<bv64>>)
      requires Valid()
      requires 0 < |attempt|
      modifies this`result, this`bestResult, testFunction
      ensures Valid()
      ensures this.maxExamples == old(this.maxExamples)
      ensures this.calls == old(this.calls)
      ensures this.random == old(this.random)
      ensures this.testFunction == old(this.testFunction)
      ensures this.repr == old(this.repr)
      ensures res.None? ==> result == old(result)
      ensures res.Some? ==> result == Some(attempt)
    {
      var testCase := TestCase.ForChoices(attempt, false);
      // testCase + testCase.random are freshly allocated; testFunction.repr
      // contains only pre-existing objects, so the disjointness precondition
      // holds.
      assert testCase.repr == {testCase, testCase.random};
      assert testFunction.repr !! testCase.repr;
      var newResult := testFunction.Apply(testCase);
      if newResult.Error().Some? && newResult.Error().Extract() == INTERESTING {
        result := Some(attempt);
        bestResult := newResult.value;
        res := Some(attempt);
      } else {
        res := None;
      }
    }

    // Binary search down to find the smallest value at result[index] that
    // still keeps the test INTERESTING. Java reference: TestingState.java:154-159
    // (the per-index closure passed to binSearchDown).
    method BinSearchDownHelper(index: nat, high: bv64)
      requires Valid()
      requires result.Some?
      modifies this`result, this`bestResult, testFunction
      ensures Valid()
      ensures this.maxExamples == old(this.maxExamples)
      ensures this.calls == old(this.calls)
      ensures this.random == old(this.random)
      ensures this.testFunction == old(this.testFunction)
      ensures this.repr == old(this.repr)
      ensures result.Some?
    {
      var rs := result.Extract();
      if index >= |rs| {
        return;
      }
      var lo: int := 0;
      var hi: int := high as int;
      var r0 := ReplaceSingle(index, 0 as bv64);
      if r0.Some? {
        return;
      }
      while lo + 1 < hi
        invariant Valid()
        invariant result.Some?
        invariant 0 <= lo <= hi <= high as int
        invariant this.maxExamples == old(this.maxExamples)
        invariant this.calls == old(this.calls)
        invariant this.random == old(this.random)
        invariant this.testFunction == old(this.testFunction)
        invariant this.repr == old(this.repr)
        decreases hi - lo
      {
        var mid := lo + (hi - lo) / 2;
        var rmid := ReplaceSingle(index, mid as bv64);
        if rmid.Some? {
          hi := mid;
        } else {
          lo := mid;
        }
      }
    }

    // Two-index binary search: shrink result[i] while preserving the sum
    // result[i] + result[j]. Java reference: TestingState.java:169-175.
    method BinSearchDownHelper2(i: nat, j: nat, jPrev: bv64, high: bv64)
      requires Valid()
      requires result.Some?
      modifies this`result, this`bestResult, testFunction
      ensures Valid()
      ensures this.maxExamples == old(this.maxExamples)
      ensures this.calls == old(this.calls)
      ensures this.random == old(this.random)
      ensures this.testFunction == old(this.testFunction)
      ensures this.repr == old(this.repr)
      ensures result.Some?
    {
      var rs := result.Extract();
      if i >= |rs| || j >= |rs| {
        return;
      }
      var lo: int := 0;
      var hi: int := high as int;
      // Initial try at v == 0: jPrev + high. bv64 addition wraps modulo 2^64;
      // that is the same arithmetic the Java reference performs on int.
      var r0 := ReplaceMultiple(map[i := 0 as bv64, j := jPrev + high]);
      if r0.Some? {
        return;
      }
      while lo + 1 < hi
        invariant Valid()
        invariant result.Some?
        invariant 0 <= lo <= hi <= high as int
        invariant this.maxExamples == old(this.maxExamples)
        invariant this.calls == old(this.calls)
        invariant this.random == old(this.random)
        invariant this.testFunction == old(this.testFunction)
        invariant this.repr == old(this.repr)
        decreases hi - lo
      {
        var mid := lo + (hi - lo) / 2;
        var delta: bv64 := (high as int - mid) as bv64;
        var rmid := ReplaceMultiple(map[i := mid as bv64, j := jPrev + delta]);
        if rmid.Some? {
          hi := mid;
        } else {
          lo := mid;
        }
      }
    }

    method ReplaceSingle(index: nat, value: bv64) returns (res: Option<seq<bv64>>)
      requires Valid()
      requires result.Some?
      modifies this`result, this`bestResult, testFunction
      ensures Valid()
      ensures this.maxExamples == old(this.maxExamples)
      ensures this.calls == old(this.calls)
      ensures this.random == old(this.random)
      ensures this.testFunction == old(this.testFunction)
      ensures this.repr == old(this.repr)
      ensures result.Some?
    {
      var attempt := result.Extract();
      if index >= |attempt| || |attempt| == 0 {
        res := None;
        return;
      }
      attempt := attempt[..index] + [value] + attempt[index + 1..];
      res := Consider(attempt);
    }

    method ReplaceMultiple(values: map<nat, bv64>) returns (res: Option<seq<bv64>>)
      requires Valid()
      requires result.Some?
      modifies this`result, this`bestResult, testFunction
      ensures Valid()
      ensures this.maxExamples == old(this.maxExamples)
      ensures this.calls == old(this.calls)
      ensures this.random == old(this.random)
      ensures this.testFunction == old(this.testFunction)
      ensures this.repr == old(this.repr)
      ensures result.Some?
    {
      var attempt := result.Extract();
      if |attempt| == 0 {
        res := None;
        return;
      }
      var origLen := |attempt|;
      var keys := values.Keys;
      while keys != {}
        invariant |attempt| == origLen
        decreases keys
      {
        var k :| k in keys;
        keys := keys - {k};
        if k < |attempt| {
          attempt := attempt[..k] + [values[k]] + attempt[k + 1..];
        }
      }
      res := Consider(attempt);
    }

    function CompareChoices(choices1: seq<bv64>, choices2: seq<bv64>): int
    {
      if |choices1| < |choices2| then
        -1
      else if |choices1| > |choices2| then
        1
      else
        CompareChoicesHelper(choices1, choices2, 0)
    }

    function CompareChoicesHelper(choices1: seq<bv64>, choices2: seq<bv64>, i: nat): int
      requires |choices1| == |choices2|
      requires i <= |choices1| && i <= |choices2|
      decreases |choices1| - i
    {
      if i >= |choices1| then
        0
      else if choices1[i] < choices2[i] then
        -1
      else if choices1[i] > choices2[i] then
        1
      else
        CompareChoicesHelper(choices1, choices2, i + 1)
    }
  }

  // Top-level entry point — Java Minithesis.runTest's Dafny analogue.
  // Builds a PredicateTest, a fresh RNG, a TestingState; runs generation
  // (+ eventually shrinking); prints a concise summary.
  method RunTest<T(!new)>(pred: T -> bool, arb: Arbitrary<T>, name: string)
    requires arb.Valid()
  {
    RunTestWithExamples(pred, arb, name, 100);
  }

  method RunTestWithExamples<T(!new)>(pred: T -> bool, arb: Arbitrary<T>, name: string, examples: nat)
    requires arb.Valid()
    requires 0 < examples
  {
    var pt := new PredicateTest<T>(pred, arb);
    var rng := new SimpleRandomGen();
    assert fresh(rng) && fresh(rng.random);
    // Fresh PredicateTest cannot alias the freshly-constructed rng or its inner random.
    assume {:axiom} rng !in pt.repr && rng.random !in pt.repr;
    var state := new TestingState<T>(rng, pt, examples);
    assert fresh(state) && state.random == rng && state.random.random == rng.random;
    state.Run();

    var res := state.GetResult();
    var valid := state.GetValidTestCases();
    var best := state.GetBestResult();

    if valid == 0 && res.None? {
      print "[", name, "] UNSATISFIABLE — no valid test cases generated\n";
      return;
    }
    match res {
      case None =>
        print "[", name, "] PASS (", valid, " valid examples)\n";
      case Some(choices) =>
        print "[", name, "] FAIL — minimised choice sequence: ", choices, "\n";
        match best {
          case Some(v) => print "  failing input: ", v, "\n";
          case None =>
        }
    }
  }

  // Method-test entry points — sibling of RunTest / RunTestWithExamples.
  // Builds a MethodTest, plumbs into the standard TestingState, prints
  // the same PASS/FAIL summary shape (plus the last error payload) so
  // callers get uniform output.
  method RunMethodTest<Input(!new), E(==)>(arb: Arbitrary<Input>, sut: MethodUnderTest<Input, E>, name: string)
    requires arb.Valid() requires sut.Valid()
  {
    RunMethodTestWithExamples(arb, sut, name, 100);
  }

  method RunMethodTestWithExamples<Input(!new), E(==)>(
      arb: Arbitrary<Input>,
      sut: MethodUnderTest<Input, E>,
      name: string,
      examples: nat)
    requires arb.Valid() requires sut.Valid()
    requires 0 < examples
  {
    var mt := new MethodTest<Input, E>(arb, sut);
    var rng := new SimpleRandomGen();
    assert fresh(rng) && fresh(rng.random);
    // Fresh MethodTest cannot alias the freshly-constructed rng or its
    // inner random — same discharge as RunTestWithExamples above.
    assume {:axiom} rng !in mt.repr && rng.random !in mt.repr;
    var state := new TestingState<Input>(rng, mt, examples);
    state.Run();

    var res := state.GetResult();
    var valid := state.GetValidTestCases();
    var best := state.GetBestResult();

    if valid == 0 && res.None? {
      print "[", name, "] UNSATISFIABLE — no valid test cases generated\n";
      return;
    }
    match res {
      case None =>
        print "[", name, "] PASS (", valid, " valid examples)\n";
      case Some(choices) =>
        print "[", name, "] FAIL — minimised choice sequence: ", choices, "\n";
        match best {
          case Some(v) => print "  failing input: ", v, "\n";
          case None =>
        }
        match mt.lastResult {
          case Some(Failure(e)) => print "  last error: ", e, "\n";
          case _ =>
        }
    }
  }
}
