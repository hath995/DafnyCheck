include "./RandomGenerator.dfy"
include "./TestStatus.dfy"
include "./TestResult.dfy"
module Arbitraries {
  import opened TestResults
  import opened RandomGenerator
  import opened TestTypes
  import opened Std.Wrappers
  class TestCase {
    ghost var repr: set<object>
    var prefix: seq<Choice>
    var random: XoroShift128Plus
    var maxSize: nat
    var printResults: bool
    var depth: nat
    var targetingScore: nat
    var choices: seq<Choice>

    ghost predicate Valid()
      reads this
    {
      this.repr == {this, random} &&
      |choices| <= maxSize
    }

    constructor(prefix: seq<Choice>, random: XoroShift128Plus, maxSize: nat, printResults: bool)
      requires 0 < maxSize
      ensures this.random == random
      ensures this.prefix == prefix
      ensures this.maxSize == maxSize
      ensures this.printResults == printResults
      ensures this.Valid()
      ensures fresh(this)
    //   ensures fresh(repr)
    {
      this.prefix := prefix;
      this.random := random;
      this.maxSize := maxSize;
      this.printResults := printResults;
      this.depth := 0;
      this.targetingScore := 0; // Integer.MIN_VALUE equivalent
      this.choices := [];
      this.repr := {this, random};
    }

    // Static factory method for creating TestCase from choices
    static method ForChoices(choices: seq<Choice>, seed: bv64, printResults: bool) returns (tc: TestCase)
      requires 0 < |choices|
      ensures fresh(tc)
      ensures fresh(tc.random)
      ensures tc.Valid()
      ensures tc.prefix == choices
    {
      var random := XoroShift128Plus.fromSeed(seed);
      tc := new TestCase(choices, random, |choices|, printResults);
    }

    // Make a choice between 0 and n-1
    // method Choice(n: bv64) returns (result: bv64)
    //   requires 0 <= n
    //   modifies this
    // {
    //   var testResult := MakeChoice(n, () => this.random.unsafeNext() % n);
    //   if (ShouldPrint()) {
    //     print "choice(", n, "): ", testResult.Unwrap();
    //   }
    //   if (testResult.err.Some?) {
    //     // TODO: Handle unsatisfiable test case exception
    //     assert false; // Placeholder for exception
    //   }
    //   result := testResult.Unwrap();
    // }

    // // Force a specific choice
    method ForcedChoice(n: Choice) returns (result: TestResult<Choice>)
      requires 0 <= n
      ensures maxSize == old(maxSize)
      ensures |choices| >= old(|choices|)
      ensures result.value.Some? ==> |choices| == old(|choices|) + 1
      ensures result.value.None? ==> choices == old(choices)
      ensures old(this.Valid()) ==> this.Valid()
      ensures old(repr) == repr
      modifies this
    {
      if (n < 0) {
        // TODO: Handle IllegalArgumentException
        assert false;
      }
      // Buffer-exhaustion check: at |choices| == maxSize the buffer is full, so we
      // must OVERRUN rather than append (keeping |choices| <= maxSize, the well-
      // foundedness invariant for the Apply buffer metric maxSize - |choices|).
      if (|choices| >= maxSize) {
        result := new TestResult<Choice>(Some(OVERRUN), None);
        return;
      }
      choices := choices + [n];
      result := new TestResult<Choice>(None, Some(n));
    }

    // Boolean choice with 50% probability. Native: one Choice draw, compare against
    // MOD/2. No real, no bv64 â€” a boolean is not "an arbitrary for real".
    method BooleanChoice() returns (result: bool)
      ensures old(this.Valid()) ==> this.Valid()
      // ensures old(repr) == repr
      modifies this, random
    {
      var rnd := this.random.unsafeNextChoice();
      result := rnd < 1073741823;   // floor((2^31-1)/2); ~50%
    }

    // Weighted boolean choice
    method Weighted(p: real) returns (result: bool)
      requires 0.0 <= p <= 1.0
      ensures old(this.Valid()) ==> this.Valid()
      // ensures old(repr) == repr
      modifies this, random
    {
      var testResult := WeightedInternal(p);
      if (!testResult.value.Some?) {
        result := false;
      }else {
        result := testResult.Unwrap();
      }
    }

    // Internal weighted choice that returns TestResult
    method WeightedInternal(p: real) returns (result: TestResult<bool>)
      requires 0.0 <= p <= 1.0
      ensures maxSize == old(maxSize)
      ensures |choices| >= old(|choices|)
      ensures old(this.Valid()) ==> this.Valid()
      ensures old(repr) == repr
    //   ensures result.value.Some?
      modifies this, random
    {
      var intResult: TestResult<Choice>;
      if (p <= 0.0) {
        intResult := ForcedChoice(0);
      } else if (p >= 1.0) {
        intResult := ForcedChoice(1);
      } else {
        // Convert the real probability to a native threshold ONCE (the only real op,
        // at the boundary where the caller supplied a real `p`), then draw + compare
        // entirely in native Choice arithmetic. 0 < p < 1 => 0 <= thr < MOD < 2^32.
        var rnd := this.random.unsafeNextChoice();
        var thr: Choice := (p * 2147483647.0).Floor as Choice;
        var choice: Choice := if rnd < thr then 1 else 0;
        intResult := new TestResult<Choice>(None, Some(choice));
      }
      result := intResult.Map<bool>((i) => i == 1);
    }

    // Internal method to make a choice
    method MakeChoice(n: Choice) returns (result: TestResult<Choice>)
      requires 0 < n
      ensures |choices| >= old(|choices|)
      ensures result.value.Some? ==> |choices| == old(|choices|) + 1
      ensures result.value.None? ==> choices == old(choices)
      ensures old(this.Valid()) ==> this.Valid()
      ensures old(repr) == repr
      modifies this`choices, random
      // ensures result.value.Some? ==> result.value.Extract() < n
    {
      result := MakeChoice_(n, (rand) => rand % n);
    }

    // Internal method to make a choice with custom random function
    method MakeChoice_(n: Choice, randomFunc: Choice -> Choice) returns (result: TestResult<Choice>)
      requires 0 < n
      ensures |choices| >= old(|choices|)
      ensures result.value.Some? ==> |choices| == old(|choices|) + 1
      ensures result.value.None? ==> choices == old(choices)
      ensures old(this.Valid()) ==> this.Valid()
      ensures old(repr) == repr
      modifies this`choices, random
      // ensures result.value.Some? ==> exists x: Choice :: randomFunc(x) == result.value.Extract();
    {
      if (|choices| >= maxSize) {
        result := new TestResult<Choice>(Some(OVERRUN), None);
        return;
      }

      var choiceResult: Choice;
      if (|choices| < |prefix|) {
        choiceResult := prefix[|choices|];
      } else {
        var rand := this.random.unsafeNextChoice();
        choiceResult := randomFunc(rand);
      }
      // Valid choices index 0..n-1 (the random path uses rand % n, and callers
      // like OfTransformable index args[choice] with n == |args|). A replayed
      // prefix choice equal to n must therefore be rejected, not just one > n.
      if (choiceResult >= n) {
        result := new TestResult<Choice>(Some(INVALID), None);
        return;
      }
      choices := choices + [choiceResult];
      result := new TestResult<Choice>(None, Some(choiceResult));
    }

    // Check if should print debug information
    function ShouldPrint(): bool
      reads this
    {
      printResults && depth == 0
    }

    // Reject the current test case
    method Reject()
      modifies this
    {
      // TODO: Handle InvalidTestCaseException
    //   assert false;
    }

    // Assume a precondition
    method Assume(precondition: bool)
      modifies this
    {
      if (!precondition) {
        Reject();
      }
    }

    // Set targeting score
    method Target(n: nat)
      modifies this
    {
      this.targetingScore := n;
    }

    // Get targeting score
    function GetTargetingScore(): int
      reads this
    {
      targetingScore
    }

    // Get choices
    function GetChoices(): seq<Choice>
      reads this
    {
      choices
    }

    // Apply a possibility to generate a value
    method Any<T>(possibility: Arbitrary<T>) returns (result: Option<T>)
      requires possibility.Valid()
      requires Valid()
      // decreases parentRepr
      modifies this, random
      ensures Valid()
      ensures this.random == old(this.random)
      ensures this.repr == old(this.repr)
      ensures possibility.Valid()
    {
      this.depth := this.depth + 1;
      result := possibility.Apply(this);
    //   this.depth := this.depth - 1;
    }
  }

    // Choice bound for generator arguments. Was MaxLong (2^64-1, the old bv64 choice
    // base); now MaxChoice (2^32-1) since choices are uint32 â€” imported from
    // RandomGenerator. Generator args (|args|, max-min, |possibilities|, list bound)
    // are cast `as Choice` for MakeChoice, so they must fit a uint32.
    // Transformable is now a value trait (datatypes refine it, no `object`
    // parent). The old repr/childRepr dynamic-frames apparatus collapses to a
    // single stored ghost `Height()`: combinators that recurse into a child
    // WITHOUT first consuming a choice require `child.Height() < Height()`
    // (threaded through Valid), which is the well-founded order replacing
    // `childRepr < repr`. Apply still leads its `decreases` with the finite
    // buffer metric `maxSize - |choices|`; Height is only the tie-breaker.
    trait Transformable<T> {
        ghost function Height(): nat

        ghost predicate Valid()
            decreases Height(), 0

        method Apply(tc: TestCase) returns (result: Option<T>)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
    }

    datatype OfTransformable<T> extends Transformable<T> = OfT(args: seq<T>) {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        {
            0 < |args| <= MaxChoice
        }

        method Apply(tc: TestCase) returns (result: Option<T>)
            requires allocated(tc)
            requires this.Valid()
            requires tc.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            var choiceResult := tc.MakeChoice(|args| as Choice);
            if choiceResult.value.Some? {
                expect choiceResult.value.Extract() as int < |args|;
                return Some(args[choiceResult.Unwrap() as int]);
            }else{
                return None;
            }
        }
    }

    datatype JustTransformable<T> extends Transformable<T> = JustT(value: T) {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        {
            true
        }

        method Apply(tc: TestCase) returns (result: Option<T>)
            requires allocated(tc)
            requires this.Valid()
            requires tc.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            result := Some(this.value);
        }
    }

    datatype RangeTransformable extends Transformable<int> = RangeT(min: int, max: int) {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        {
            min <= max && (0 < max - min <= MaxChoice)
        }

        method Apply(tc: TestCase) returns (result: Option<int>)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            var choiceResult := tc.MakeChoice((max - min) as Choice);
            if choiceResult.value.Some? {
                result := Some(min + (choiceResult.Unwrap() as int));
            } else {
                result := None;
            }
        }
    }

    // class NothingTransformable<T> extends Transformable<T> {
    //     constructor()
    //         ensures fresh(this)
    //         ensures Valid()
    //     {
    //     }

    //     predicate Valid()
    //         reads this
    //     {
    //         true
    //     }

    //     method Apply(tc: TestCase) returns (result: T)
    //         requires allocated(tc)
    //         requires this.Valid()
    //         modifies tc, tc.random
    //     {
    //         tc.Reject();
    //         // This will never return due to Reject()
    //         result := *;
    //     }
    // }

    datatype MixTransformable<T> extends Transformable<T> = MixT(possibilities: seq<Arbitrary<T>>, ghost h: nat) {
        // Apply draws a choice BEFORE dispatching into the chosen child, so its
        // termination rests on the buffer metric, not Height. But Valid() still
        // recurses into each child's Valid(), so Height must dominate the
        // children for Valid()'s own well-foundedness. The old pairwise
        // disjointness precondition is gone: values cannot alias.
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
            0 < |possibilities| < MaxChoice &&
            (forall i :: 0 <= i < |possibilities| ==>
                possibilities[i].internalFunction.Height() < h && possibilities[i].Valid())
        }

        method Apply(tc: TestCase) returns (result: Option<T>)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            var choiceResult := tc.MakeChoice(|possibilities| as Choice);
            if choiceResult.value.Some? {
                var choice := choiceResult.Unwrap() as int;
                expect choice < |possibilities|;
                result := possibilities[choice].internalFunction.Apply(tc);
            } else {
                // OVERRUN/INVALID: abort the draw (Hypothesis discards the example).
                result := None;
            }
        }
    }

    datatype BoolsTransformable extends Transformable<bool> = BoolsT {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        {
            true
        }

        method Apply(tc: TestCase) returns (result: Option<bool>)
            requires allocated(tc)
            requires this.Valid()
            requires tc.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            var choiceResult := tc.MakeChoice(2);
            if choiceResult.value.Some? {
                result := Some(choiceResult.Unwrap() == 1);
            } else {
                result := None;
            }
        }
    }

    datatype ListsTransformable<S> extends Transformable<seq<S>> = ListsT(elementGenerator: Arbitrary<S>, minSize: int, maxSize: int, ghost h: nat) {
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
            elementGenerator.internalFunction.Height() < h &&
            0 <= minSize <= maxSize && elementGenerator.Valid()
        }

        method Apply(tc: TestCase) returns (result: Option<seq<S>>)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            var xs: seq<S> := [];
            while true
                invariant |xs| <= maxSize
                invariant tc.Valid()
                invariant tc.repr == old(tc.repr)
                invariant |tc.choices| >= old(|tc.choices|)
                invariant tc.maxSize == old(tc.maxSize)
                modifies tc, tc.random
                decreases maxSize-|xs|
            {
                if |xs| < minSize {
                    // Force continue
                    var forceResult := tc.ForcedChoice(1);
                    if forceResult.err.Some? {
                        break;
                    }
                } else if |xs| >= maxSize {
                    // Force stop
                    var forceResult := tc.ForcedChoice(0);
                    if forceResult.err.Some? {
                        break;
                    }
                    break;
                } else {
                    // Weighted choice
                    var weightedResult := tc.WeightedInternal(0.9);
                    if !weightedResult.value.Some? || !weightedResult.Unwrap() {
                        break;
                    }
                }
                var element := elementGenerator.internalFunction.Apply(tc);
                if element.None? { return None; }  // element draw overran: abort
                xs := xs + [element.value];
            }
            result := Some(xs);
        }
    }

    datatype StringsTransformable extends Transformable<string> = StringsT(minLength: int, maxLength: int, ascii: bool) {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        {
          0 <= minLength <= maxLength
        }

        method Apply(tc: TestCase) returns (result: Option<string>)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            var chars: seq<nat> := [];
            while true
                invariant |chars| <= maxLength
                invariant tc.Valid()
                invariant tc.repr == old(tc.repr)
                invariant |tc.choices| >= old(|tc.choices|)
                invariant tc.maxSize == old(tc.maxSize)
                invariant forall x :: x in chars ==> x < 0x0000D800
                modifies tc, tc.random
                decreases maxLength-|chars|
            {
                if |chars| < minLength {
                    // Force continue
                    var forceResult := tc.ForcedChoice(1);
                    if forceResult.err.Some? {
                        break;
                    }
                } else if |chars| >= maxLength {
                    // Force stop
                    var forceResult := tc.ForcedChoice(0);
                    if forceResult.err.Some? {
                        break;
                    }
                    break;
                } else {
                    // Weighted choice
                    var weightedResult := tc.WeightedInternal(0.9);
                    if !weightedResult.value.Some? || !weightedResult.Unwrap() {
                        break;
                    }
                }
                var charChoice := if ascii then 128 else 0x0000D800;
                var choiceResult := tc.MakeChoice(charChoice as Choice);
                if choiceResult.value.None? { return None; }  // char draw overran: abort
                var charValue := choiceResult.Unwrap();
                assume {:axiom} 0 <= charValue < 0x0000D800;
                chars := chars + [charValue as nat];
            }
            var s: string := "";
            for i := 0 to |chars|
                invariant |s| == i
            {
                assert chars[i] in chars;
                s := s + [chars[i] as char];
            }
            result := Some(s);
        }
    }

    datatype MapTransformable<T, !U> extends Transformable<T> = MapT(elementGenerator: Arbitrary<U>, fn: U -> T, ghost h: nat) {
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
          elementGenerator.internalFunction.Height() < h &&
            elementGenerator.Valid()
        }

        method Apply(tc: TestCase) returns (result: Option<T>)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
          var element := elementGenerator.internalFunction.Apply(tc);
          if element.None? { return None; }
          result := Some(fn(element.value));
        }
    }

    datatype TupleTransformable<T, U> extends Transformable<(T, U)> = TupleT(firstGenerator: Arbitrary<T>, secondGenerator: Arbitrary<U>, ghost h: nat) {
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
            firstGenerator.internalFunction.Height() < h &&
            secondGenerator.internalFunction.Height() < h &&
            firstGenerator.Valid() &&
            secondGenerator.Valid()
        }

        method Apply(tc: TestCase) returns (result: Option<(T, U)>)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            var first := firstGenerator.internalFunction.Apply(tc);
            if first.None? { return None; }
            var second := secondGenerator.internalFunction.Apply(tc);
            if second.None? { return None; }
            result := Some((first.value, second.value));
        }
    }

    // Dedicated fixed-arity tuple generators (3..10). Each draws its N children
    // directly in one Apply and assembles the flat tuple — no nested pairs, no
    // Map flatten. Valid demands every child's Height < h (needed both for the
    // recursive child draws and for Valid's own well-foundedness); the factories
    // set h to the sum of child heights + 1, so each child is < h by nat
    // arithmetic. This is the arity-2 TupleTransformable pattern generalized.
    datatype Tuple3Transformable<A, B, C> extends Transformable<(A, B, C)> =
        Tuple3T(g0: Arbitrary<A>, g1: Arbitrary<B>, g2: Arbitrary<C>, ghost h: nat)
    {
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
            g0.internalFunction.Height() < h && g1.internalFunction.Height() < h &&
            g2.internalFunction.Height() < h &&
            g0.Valid() && g1.Valid() && g2.Valid()
        }
        method Apply(tc: TestCase) returns (result: Option<(A, B, C)>)
            requires allocated(tc) requires tc.Valid() requires this.Valid()
            ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|) ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            var r0 := g0.internalFunction.Apply(tc); if r0.None? { return None; }
            var r1 := g1.internalFunction.Apply(tc); if r1.None? { return None; }
            var r2 := g2.internalFunction.Apply(tc); if r2.None? { return None; }
            result := Some((r0.value, r1.value, r2.value));
        }
    }

    datatype Tuple4Transformable<A, B, C, D> extends Transformable<(A, B, C, D)> =
        Tuple4T(g0: Arbitrary<A>, g1: Arbitrary<B>, g2: Arbitrary<C>, g3: Arbitrary<D>, ghost h: nat)
    {
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
            g0.internalFunction.Height() < h && g1.internalFunction.Height() < h &&
            g2.internalFunction.Height() < h && g3.internalFunction.Height() < h &&
            g0.Valid() && g1.Valid() && g2.Valid() && g3.Valid()
        }
        method Apply(tc: TestCase) returns (result: Option<(A, B, C, D)>)
            requires allocated(tc) requires tc.Valid() requires this.Valid()
            ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|) ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            var r0 := g0.internalFunction.Apply(tc); if r0.None? { return None; }
            var r1 := g1.internalFunction.Apply(tc); if r1.None? { return None; }
            var r2 := g2.internalFunction.Apply(tc); if r2.None? { return None; }
            var r3 := g3.internalFunction.Apply(tc); if r3.None? { return None; }
            result := Some((r0.value, r1.value, r2.value, r3.value));
        }
    }

    datatype Tuple5Transformable<A, B, C, D, E> extends Transformable<(A, B, C, D, E)> =
        Tuple5T(g0: Arbitrary<A>, g1: Arbitrary<B>, g2: Arbitrary<C>, g3: Arbitrary<D>,
                g4: Arbitrary<E>, ghost h: nat)
    {
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
            g0.internalFunction.Height() < h && g1.internalFunction.Height() < h &&
            g2.internalFunction.Height() < h && g3.internalFunction.Height() < h &&
            g4.internalFunction.Height() < h &&
            g0.Valid() && g1.Valid() && g2.Valid() && g3.Valid() && g4.Valid()
        }
        method Apply(tc: TestCase) returns (result: Option<(A, B, C, D, E)>)
            requires allocated(tc) requires tc.Valid() requires this.Valid()
            ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|) ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            var r0 := g0.internalFunction.Apply(tc); if r0.None? { return None; }
            var r1 := g1.internalFunction.Apply(tc); if r1.None? { return None; }
            var r2 := g2.internalFunction.Apply(tc); if r2.None? { return None; }
            var r3 := g3.internalFunction.Apply(tc); if r3.None? { return None; }
            var r4 := g4.internalFunction.Apply(tc); if r4.None? { return None; }
            result := Some((r0.value, r1.value, r2.value, r3.value, r4.value));
        }
    }

    datatype Tuple6Transformable<A, B, C, D, E, F> extends Transformable<(A, B, C, D, E, F)> =
        Tuple6T(g0: Arbitrary<A>, g1: Arbitrary<B>, g2: Arbitrary<C>, g3: Arbitrary<D>,
                g4: Arbitrary<E>, g5: Arbitrary<F>, ghost h: nat)
    {
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
            g0.internalFunction.Height() < h && g1.internalFunction.Height() < h &&
            g2.internalFunction.Height() < h && g3.internalFunction.Height() < h &&
            g4.internalFunction.Height() < h && g5.internalFunction.Height() < h &&
            g0.Valid() && g1.Valid() && g2.Valid() && g3.Valid() && g4.Valid() && g5.Valid()
        }
        method Apply(tc: TestCase) returns (result: Option<(A, B, C, D, E, F)>)
            requires allocated(tc) requires tc.Valid() requires this.Valid()
            ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|) ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            var r0 := g0.internalFunction.Apply(tc); if r0.None? { return None; }
            var r1 := g1.internalFunction.Apply(tc); if r1.None? { return None; }
            var r2 := g2.internalFunction.Apply(tc); if r2.None? { return None; }
            var r3 := g3.internalFunction.Apply(tc); if r3.None? { return None; }
            var r4 := g4.internalFunction.Apply(tc); if r4.None? { return None; }
            var r5 := g5.internalFunction.Apply(tc); if r5.None? { return None; }
            result := Some((r0.value, r1.value, r2.value, r3.value, r4.value, r5.value));
        }
    }

    datatype Tuple7Transformable<A, B, C, D, E, F, G> extends Transformable<(A, B, C, D, E, F, G)> =
        Tuple7T(g0: Arbitrary<A>, g1: Arbitrary<B>, g2: Arbitrary<C>, g3: Arbitrary<D>,
                g4: Arbitrary<E>, g5: Arbitrary<F>, g6: Arbitrary<G>, ghost h: nat)
    {
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
            g0.internalFunction.Height() < h && g1.internalFunction.Height() < h &&
            g2.internalFunction.Height() < h && g3.internalFunction.Height() < h &&
            g4.internalFunction.Height() < h && g5.internalFunction.Height() < h &&
            g6.internalFunction.Height() < h &&
            g0.Valid() && g1.Valid() && g2.Valid() && g3.Valid() && g4.Valid() && g5.Valid() && g6.Valid()
        }
        method Apply(tc: TestCase) returns (result: Option<(A, B, C, D, E, F, G)>)
            requires allocated(tc) requires tc.Valid() requires this.Valid()
            ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|) ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            var r0 := g0.internalFunction.Apply(tc); if r0.None? { return None; }
            var r1 := g1.internalFunction.Apply(tc); if r1.None? { return None; }
            var r2 := g2.internalFunction.Apply(tc); if r2.None? { return None; }
            var r3 := g3.internalFunction.Apply(tc); if r3.None? { return None; }
            var r4 := g4.internalFunction.Apply(tc); if r4.None? { return None; }
            var r5 := g5.internalFunction.Apply(tc); if r5.None? { return None; }
            var r6 := g6.internalFunction.Apply(tc); if r6.None? { return None; }
            result := Some((r0.value, r1.value, r2.value, r3.value, r4.value, r5.value, r6.value));
        }
    }

    datatype Tuple8Transformable<A, B, C, D, E, F, G, H> extends Transformable<(A, B, C, D, E, F, G, H)> =
        Tuple8T(g0: Arbitrary<A>, g1: Arbitrary<B>, g2: Arbitrary<C>, g3: Arbitrary<D>,
                g4: Arbitrary<E>, g5: Arbitrary<F>, g6: Arbitrary<G>, g7: Arbitrary<H>, ghost h: nat)
    {
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
            g0.internalFunction.Height() < h && g1.internalFunction.Height() < h &&
            g2.internalFunction.Height() < h && g3.internalFunction.Height() < h &&
            g4.internalFunction.Height() < h && g5.internalFunction.Height() < h &&
            g6.internalFunction.Height() < h && g7.internalFunction.Height() < h &&
            g0.Valid() && g1.Valid() && g2.Valid() && g3.Valid() &&
            g4.Valid() && g5.Valid() && g6.Valid() && g7.Valid()
        }
        method Apply(tc: TestCase) returns (result: Option<(A, B, C, D, E, F, G, H)>)
            requires allocated(tc) requires tc.Valid() requires this.Valid()
            ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|) ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            var r0 := g0.internalFunction.Apply(tc); if r0.None? { return None; }
            var r1 := g1.internalFunction.Apply(tc); if r1.None? { return None; }
            var r2 := g2.internalFunction.Apply(tc); if r2.None? { return None; }
            var r3 := g3.internalFunction.Apply(tc); if r3.None? { return None; }
            var r4 := g4.internalFunction.Apply(tc); if r4.None? { return None; }
            var r5 := g5.internalFunction.Apply(tc); if r5.None? { return None; }
            var r6 := g6.internalFunction.Apply(tc); if r6.None? { return None; }
            var r7 := g7.internalFunction.Apply(tc); if r7.None? { return None; }
            result := Some((r0.value, r1.value, r2.value, r3.value, r4.value, r5.value, r6.value, r7.value));
        }
    }

    datatype Tuple9Transformable<A, B, C, D, E, F, G, H, I> extends Transformable<(A, B, C, D, E, F, G, H, I)> =
        Tuple9T(g0: Arbitrary<A>, g1: Arbitrary<B>, g2: Arbitrary<C>, g3: Arbitrary<D>,
                g4: Arbitrary<E>, g5: Arbitrary<F>, g6: Arbitrary<G>, g7: Arbitrary<H>,
                g8: Arbitrary<I>, ghost h: nat)
    {
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
            g0.internalFunction.Height() < h && g1.internalFunction.Height() < h &&
            g2.internalFunction.Height() < h && g3.internalFunction.Height() < h &&
            g4.internalFunction.Height() < h && g5.internalFunction.Height() < h &&
            g6.internalFunction.Height() < h && g7.internalFunction.Height() < h &&
            g8.internalFunction.Height() < h &&
            g0.Valid() && g1.Valid() && g2.Valid() && g3.Valid() &&
            g4.Valid() && g5.Valid() && g6.Valid() && g7.Valid() && g8.Valid()
        }
        method Apply(tc: TestCase) returns (result: Option<(A, B, C, D, E, F, G, H, I)>)
            requires allocated(tc) requires tc.Valid() requires this.Valid()
            ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|) ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            var r0 := g0.internalFunction.Apply(tc); if r0.None? { return None; }
            var r1 := g1.internalFunction.Apply(tc); if r1.None? { return None; }
            var r2 := g2.internalFunction.Apply(tc); if r2.None? { return None; }
            var r3 := g3.internalFunction.Apply(tc); if r3.None? { return None; }
            var r4 := g4.internalFunction.Apply(tc); if r4.None? { return None; }
            var r5 := g5.internalFunction.Apply(tc); if r5.None? { return None; }
            var r6 := g6.internalFunction.Apply(tc); if r6.None? { return None; }
            var r7 := g7.internalFunction.Apply(tc); if r7.None? { return None; }
            var r8 := g8.internalFunction.Apply(tc); if r8.None? { return None; }
            result := Some((r0.value, r1.value, r2.value, r3.value, r4.value, r5.value, r6.value, r7.value, r8.value));
        }
    }

    datatype Tuple10Transformable<A, B, C, D, E, F, G, H, I, J> extends Transformable<(A, B, C, D, E, F, G, H, I, J)> =
        Tuple10T(g0: Arbitrary<A>, g1: Arbitrary<B>, g2: Arbitrary<C>, g3: Arbitrary<D>,
                 g4: Arbitrary<E>, g5: Arbitrary<F>, g6: Arbitrary<G>, g7: Arbitrary<H>,
                 g8: Arbitrary<I>, g9: Arbitrary<J>, ghost h: nat)
    {
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
            g0.internalFunction.Height() < h && g1.internalFunction.Height() < h &&
            g2.internalFunction.Height() < h && g3.internalFunction.Height() < h &&
            g4.internalFunction.Height() < h && g5.internalFunction.Height() < h &&
            g6.internalFunction.Height() < h && g7.internalFunction.Height() < h &&
            g8.internalFunction.Height() < h && g9.internalFunction.Height() < h &&
            g0.Valid() && g1.Valid() && g2.Valid() && g3.Valid() && g4.Valid() &&
            g5.Valid() && g6.Valid() && g7.Valid() && g8.Valid() && g9.Valid()
        }
        method Apply(tc: TestCase) returns (result: Option<(A, B, C, D, E, F, G, H, I, J)>)
            requires allocated(tc) requires tc.Valid() requires this.Valid()
            ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|) ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            var r0 := g0.internalFunction.Apply(tc); if r0.None? { return None; }
            var r1 := g1.internalFunction.Apply(tc); if r1.None? { return None; }
            var r2 := g2.internalFunction.Apply(tc); if r2.None? { return None; }
            var r3 := g3.internalFunction.Apply(tc); if r3.None? { return None; }
            var r4 := g4.internalFunction.Apply(tc); if r4.None? { return None; }
            var r5 := g5.internalFunction.Apply(tc); if r5.None? { return None; }
            var r6 := g6.internalFunction.Apply(tc); if r6.None? { return None; }
            var r7 := g7.internalFunction.Apply(tc); if r7.None? { return None; }
            var r8 := g8.internalFunction.Apply(tc); if r8.None? { return None; }
            var r9 := g9.internalFunction.Apply(tc); if r9.None? { return None; }
            result := Some((r0.value, r1.value, r2.value, r3.value, r4.value, r5.value, r6.value, r7.value, r8.value, r9.value));
        }
    }


    // Still a reference trait: a FlatMapFn is a stateful factory (a closure-like
    // object), so it is pinned to `object` and held by reference inside the
    // FlatMap datatype below.
    trait FlatMapFn<T, U> extends object {
        // This method creates a new Arbitrary<U> based on an input T
        method CreateArbitrary(t: T) returns (p: Arbitrary<U>)
            ensures p.Valid()
    }

    datatype FlatMapTransformable<!T, U> extends Transformable<U> = FlatMapT(baseGenerator: Arbitrary<T>, flatMapFn: FlatMapFn<T, U>, ghost h: nat) {
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
            baseGenerator.internalFunction.Height() < h &&
            baseGenerator.Valid()
        }

        method Apply(tc: TestCase) returns (result: Option<U>)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            var intermediateValue := baseGenerator.internalFunction.Apply(tc); // First, generate T
            if intermediateValue.None? { return None; }                       // base overran: abort
            var nextArbitrary := flatMapFn.CreateArbitrary(intermediateValue.value); // Then, create Arbitrary<U>
            // Draw a control marker so the buffer STRICTLY drops before dispatching into the
            // freshly-created nextArbitrary. This is the finite-buffer bound: each flatMap bind
            // consumes >= 1 choice, so the maxSize - |choices| metric decreases. On exhaustion the
            // bind aborts (None), mirroring Hypothesis raising StopTest rather than completing an
            // overrun draw.
            var marker := tc.MakeChoice(2);
            if marker.value.None? { return None; }
            result := nextArbitrary.internalFunction.Apply(tc);
        }
    }

    // Heap-allocated 1-D array generator. Mirrors ListsTransformable to build a
    // seq<S>, then copies it into a freshly-allocated array (the trait's Apply
    // places no constraint on `result`, so returning a fresh array is sound).
    datatype ArraysTransformable<S> extends Transformable<array<S>> = ArraysT(elementGenerator: Arbitrary<S>, minSize: int, maxSize: int, ghost h: nat) {
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
            elementGenerator.internalFunction.Height() < h &&
            0 <= minSize <= maxSize && elementGenerator.Valid()
        }
        method Apply(tc: TestCase) returns (result: Option<array<S>>)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            var xs: seq<S> := [];
            while true
                invariant |xs| <= maxSize
                invariant tc.Valid()
                invariant tc.repr == old(tc.repr)
                invariant |tc.choices| >= old(|tc.choices|)
                invariant tc.maxSize == old(tc.maxSize)
                modifies tc, tc.random
                decreases maxSize-|xs|
            {
                if |xs| < minSize {
                    var forceResult := tc.ForcedChoice(1);
                    if forceResult.err.Some? { break; }
                } else if |xs| >= maxSize {
                    var forceResult := tc.ForcedChoice(0);
                    if forceResult.err.Some? { break; }
                    break;
                } else {
                    var weightedResult := tc.WeightedInternal(0.9);
                    if !weightedResult.value.Some? || !weightedResult.Unwrap() { break; }
                }
                var element := elementGenerator.internalFunction.Apply(tc);
                if element.None? { return None; }
                xs := xs + [element.value];
            }
            var arr := new S[|xs|](idx requires 0 <= idx < |xs| => xs[idx]);
            result := Some(arr);
        }
    }

    // Heap-allocated 2-D / 3-D array generators of FIXED size: the caller fixes
    // the dimensions (rows x cols, rows x cols x layers) and every generated
    // array has exactly that shape. Elements are generated into a flat seq and
    // read through a guarded init function (so no nonlinear index-bound proof is
    // needed); the flat seq always covers the whole array.
    datatype Array2Transformable<S> extends Transformable<array2<S>> = Array2T(elementGenerator: Arbitrary<S>, rows: nat, cols: nat, ghost h: nat) {
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
            elementGenerator.internalFunction.Height() < h &&
            elementGenerator.Valid()
        }
        method {:isolate_assertions} Apply(tc: TestCase) returns (result: Option<array2<S>>)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            ensures result.Some? ==> result.value.Length0 == rows && result.value.Length1 == cols
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            var m: nat := rows;
            var n: nat := cols;
            var dflt := elementGenerator.internalFunction.Apply(tc);
            if dflt.None? { return None; }
            var dv := dflt.value;
            var total := m * n;
            var flat: seq<S> := [dv];
            while |flat| < total
                invariant tc.Valid()
                invariant tc.repr == old(tc.repr)
                invariant |tc.choices| >= old(|tc.choices|)
                invariant tc.maxSize == old(tc.maxSize)
                invariant 1 <= |flat|
                decreases total - |flat|
                modifies tc, tc.random
            {
                var el := elementGenerator.internalFunction.Apply(tc);
                if el.None? { return None; }
                flat := flat + [el.value];
            }
            var arr := new S[m, n]((i: nat, j: nat) => if i * n + j < |flat| then flat[i * n + j] else dv);
            result := Some(arr);
        }
    }

    datatype Array3Transformable<S> extends Transformable<array3<S>> = Array3T(elementGenerator: Arbitrary<S>, rows: nat, cols: nat, layers: nat, ghost h: nat) {
        ghost function Height(): nat { h }
        ghost predicate Valid()
            decreases Height(), 0
        {
            elementGenerator.internalFunction.Height() < h &&
            elementGenerator.Valid()
        }
        method {:isolate_assertions} Apply(tc: TestCase) returns (result: Option<array3<S>>)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            ensures result.Some? ==> result.value.Length0 == rows && result.value.Length1 == cols && result.value.Length2 == layers
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            var m: nat := rows;
            var n: nat := cols;
            var o: nat := layers;
            var dflt := elementGenerator.internalFunction.Apply(tc);
            if dflt.None? { return None; }
            var dv := dflt.value;
            var total := m * n * o;
            var flat: seq<S> := [dv];
            while |flat| < total
                invariant tc.Valid()
                invariant tc.repr == old(tc.repr)
                invariant |tc.choices| >= old(|tc.choices|)
                invariant tc.maxSize == old(tc.maxSize)
                invariant 1 <= |flat|
                decreases total - |flat|
                modifies tc, tc.random
            {
                var el := elementGenerator.internalFunction.Apply(tc);
                if el.None? { return None; }
                flat := flat + [el.value];
            }
            var arr := new S[m, n, o]((i: nat, j: nat, k: nat) =>
                var idx := i * n * o + j * o + k;
                if idx < |flat| then flat[idx] else dv);
            result := Some(arr);
        }
    }

    // ================================================================
    // Core leaf generators for additional Dafny value types. Each follows
    // the BoolsTransformable template (no child generators: childRepr = {},
    // repr = {this} + childRepr). MakeChoice has no proven upper bound on its
    // result, so where a cast needs one we discharge it with the same
    // {:axiom} assume the StringsTransformable above uses for chars.
    // ================================================================

    // Natural numbers in [0, bound). `bound` is informational; values are
    // drawn modulo it at runtime (bv64 -> nat is always nonnegative).
    datatype NatsTransformable extends Transformable<nat> = NatsT(bound: nat) {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        {
            0 < bound <= MaxChoice
        }
        method Apply(tc: TestCase) returns (result: Option<nat>)
            requires allocated(tc)
            requires this.Valid()
            requires tc.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            var c := tc.MakeChoice(bound as Choice);
            if c.value.Some? {
                result := Some(c.Unwrap() as nat);
            } else {
                result := None;
            }
        }
    }

    // Printable-ASCII characters in [32, 127).
    datatype CharsTransformable extends Transformable<char> = CharsT {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        {
            true
        }
        method Apply(tc: TestCase) returns (result: Option<char>)
            requires allocated(tc)
            requires this.Valid()
            requires tc.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            var c := tc.MakeChoice(95);
            if c.value.None? { return None; }
            var v := c.Unwrap() as int;
            assume {:axiom} 0 <= v < 95;
            result := Some((32 + v) as char);
        }
    }

    // Non-negative rationals, generated as numerator / (denominator + 1).
    datatype RealsTransformable extends Transformable<real> = RealsT {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        {
            true
        }
        method Apply(tc: TestCase) returns (result: Option<real>)
            requires allocated(tc)
            requires this.Valid()
            requires tc.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            var cn := tc.MakeChoice(1000000);
            if cn.value.None? { return None; }
            var num := cn.Unwrap() as int;
            var cd := tc.MakeChoice(1000);
            if cd.value.None? { return None; }
            var den := cd.Unwrap() as int;
            result := Some((num as real) / ((den + 1) as real));
        }
    }

    // ----------------------------------------------------------------
    // Fixed-width bit-vector generators. Widths up to 64 draw one choice and
    // narrow it (bound discharged by {:axiom} like the char path); 128 and 256
    // assemble multiple 64-bit words with widening casts (no bound needed).
    // ----------------------------------------------------------------
    datatype BitVectors1Transformable extends Transformable<bv1> = BV1T {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        { true }
        method Apply(tc: TestCase) returns (result: Option<bv1>)
            requires allocated(tc) requires this.Valid()
            requires tc.Valid() ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            var c := tc.MakeChoice(2);
            var v := if c.value.Some? then c.Unwrap() else 0;
            assume {:axiom} v < 2;
            result := Some(v as bv1);
        }
    }

    datatype BitVectors2Transformable extends Transformable<bv2> = BV2T {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        { true }
        method Apply(tc: TestCase) returns (result: Option<bv2>)
            requires allocated(tc) requires this.Valid()
            requires tc.Valid() ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            var c := tc.MakeChoice(4);
            var v := if c.value.Some? then c.Unwrap() else 0;
            assume {:axiom} v < 4;
            result := Some(v as bv2);
        }
    }

    datatype BitVectors8Transformable extends Transformable<bv8> = BV8T {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        { true }
        method Apply(tc: TestCase) returns (result: Option<bv8>)
            requires allocated(tc) requires this.Valid()
            requires tc.Valid() ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            var c := tc.MakeChoice(256);
            var v := if c.value.Some? then c.Unwrap() else 0;
            assume {:axiom} v < 256;
            result := Some(v as bv8);
        }
    }

    datatype BitVectors16Transformable extends Transformable<bv16> = BV16T {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        { true }
        method Apply(tc: TestCase) returns (result: Option<bv16>)
            requires allocated(tc) requires this.Valid()
            requires tc.Valid() ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            var c := tc.MakeChoice(0x10000);
            var v := if c.value.Some? then c.Unwrap() else 0;
            assume {:axiom} v < 0x10000;
            result := Some(v as bv16);
        }
    }

    datatype BitVectors32Transformable extends Transformable<bv32> = BV32T {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        { true }
        method Apply(tc: TestCase) returns (result: Option<bv32>)
            requires allocated(tc) requires this.Valid()
            requires tc.Valid() ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            // The native lane only spans 31 bits, so assemble 32 bits from two 16-bit
            // Choice chunks. Each chunk is < 2^16 (MakeChoice rejects >= n), so the
            // Choice -> bv32 casts are total and the chunks never overlap.
            var c0 := tc.MakeChoice(0x10000);
            var w0 := if c0.value.Some? then c0.Unwrap() else 0;
            var c1 := tc.MakeChoice(0x10000);
            var w1 := if c1.value.Some? then c1.Unwrap() else 0;
            result := Some(((w0 as bv32) << 16) | (w1 as bv32));
        }
    }

    datatype BitVectors64Transformable extends Transformable<bv64> = BV64T {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        { true }
        method Apply(tc: TestCase) returns (result: Option<bv64>)
            requires allocated(tc) requires this.Valid()
            requires tc.Valid() ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            // 64 bits from four 16-bit Choice chunks (the native lane spans only 31).
            var c0 := tc.MakeChoice(0x10000);
            var w0 := if c0.value.Some? then c0.Unwrap() else 0;
            var c1 := tc.MakeChoice(0x10000);
            var w1 := if c1.value.Some? then c1.Unwrap() else 0;
            var c2 := tc.MakeChoice(0x10000);
            var w2 := if c2.value.Some? then c2.Unwrap() else 0;
            var c3 := tc.MakeChoice(0x10000);
            var w3 := if c3.value.Some? then c3.Unwrap() else 0;
            result := Some(((w0 as bv64) << 48) | ((w1 as bv64) << 32) |
                      ((w2 as bv64) << 16) | (w3 as bv64));
        }
    }

    datatype BitVectors128Transformable extends Transformable<bv128> = BV128T {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        { true }
        method Apply(tc: TestCase) returns (result: Option<bv128>)
            requires allocated(tc) requires this.Valid()
            requires tc.Valid() ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            // 128 bits from eight 16-bit Choice chunks.
            var c0 := tc.MakeChoice(0x10000);
            var w0 := if c0.value.Some? then c0.Unwrap() else 0;
            var c1 := tc.MakeChoice(0x10000);
            var w1 := if c1.value.Some? then c1.Unwrap() else 0;
            var c2 := tc.MakeChoice(0x10000);
            var w2 := if c2.value.Some? then c2.Unwrap() else 0;
            var c3 := tc.MakeChoice(0x10000);
            var w3 := if c3.value.Some? then c3.Unwrap() else 0;
            var c4 := tc.MakeChoice(0x10000);
            var w4 := if c4.value.Some? then c4.Unwrap() else 0;
            var c5 := tc.MakeChoice(0x10000);
            var w5 := if c5.value.Some? then c5.Unwrap() else 0;
            var c6 := tc.MakeChoice(0x10000);
            var w6 := if c6.value.Some? then c6.Unwrap() else 0;
            var c7 := tc.MakeChoice(0x10000);
            var w7 := if c7.value.Some? then c7.Unwrap() else 0;
            result := Some(((w0 as bv128) << 112) | ((w1 as bv128) << 96) |
                      ((w2 as bv128) << 80)  | ((w3 as bv128) << 64) |
                      ((w4 as bv128) << 48)  | ((w5 as bv128) << 32) |
                      ((w6 as bv128) << 16)  | (w7 as bv128));
        }
    }

    datatype BitVectors256Transformable extends Transformable<bv256> = BV256T {
        ghost function Height(): nat { 0 }
        ghost predicate Valid()
            decreases Height(), 0
        { true }
        method Apply(tc: TestCase) returns (result: Option<bv256>)
            requires allocated(tc) requires this.Valid()
            requires tc.Valid() ensures tc.Valid() ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0 modifies tc, tc.random
        {
            // 256 bits from sixteen 16-bit Choice chunks.
            var c0 := tc.MakeChoice(0x10000);  var w0 := if c0.value.Some? then c0.Unwrap() else 0;
            var c1 := tc.MakeChoice(0x10000);  var w1 := if c1.value.Some? then c1.Unwrap() else 0;
            var c2 := tc.MakeChoice(0x10000);  var w2 := if c2.value.Some? then c2.Unwrap() else 0;
            var c3 := tc.MakeChoice(0x10000);  var w3 := if c3.value.Some? then c3.Unwrap() else 0;
            var c4 := tc.MakeChoice(0x10000);  var w4 := if c4.value.Some? then c4.Unwrap() else 0;
            var c5 := tc.MakeChoice(0x10000);  var w5 := if c5.value.Some? then c5.Unwrap() else 0;
            var c6 := tc.MakeChoice(0x10000);  var w6 := if c6.value.Some? then c6.Unwrap() else 0;
            var c7 := tc.MakeChoice(0x10000);  var w7 := if c7.value.Some? then c7.Unwrap() else 0;
            var c8 := tc.MakeChoice(0x10000);  var w8 := if c8.value.Some? then c8.Unwrap() else 0;
            var c9 := tc.MakeChoice(0x10000);  var w9 := if c9.value.Some? then c9.Unwrap() else 0;
            var c10 := tc.MakeChoice(0x10000); var w10 := if c10.value.Some? then c10.Unwrap() else 0;
            var c11 := tc.MakeChoice(0x10000); var w11 := if c11.value.Some? then c11.Unwrap() else 0;
            var c12 := tc.MakeChoice(0x10000); var w12 := if c12.value.Some? then c12.Unwrap() else 0;
            var c13 := tc.MakeChoice(0x10000); var w13 := if c13.value.Some? then c13.Unwrap() else 0;
            var c14 := tc.MakeChoice(0x10000); var w14 := if c14.value.Some? then c14.Unwrap() else 0;
            var c15 := tc.MakeChoice(0x10000); var w15 := if c15.value.Some? then c15.Unwrap() else 0;
            result := Some(((w0 as bv256) << 240)  | ((w1 as bv256) << 224) |
                      ((w2 as bv256) << 208)  | ((w3 as bv256) << 192) |
                      ((w4 as bv256) << 176)  | ((w5 as bv256) << 160) |
                      ((w6 as bv256) << 144)  | ((w7 as bv256) << 128) |
                      ((w8 as bv256) << 112)  | ((w9 as bv256) << 96)  |
                      ((w10 as bv256) << 80)  | ((w11 as bv256) << 64)  |
                      ((w12 as bv256) << 48)  | ((w13 as bv256) << 32)  |
                      ((w14 as bv256) << 16)  | (w15 as bv256));
        }
    }

    // Build a map from a sequence of key/value pairs (later-listed keys win,
    // matching Dafny map-update order). Used to derive the Maps generator from
    // a Lists-of-Tuples generator without a bespoke Transformable.
    function SeqToMap<K, V>(pairs: seq<(K, V)>): map<K, V> {
        if |pairs| == 0 then map[]
        else SeqToMap(pairs[1..])[pairs[0].0 := pairs[0].1]
    }

    // Max Height over a seq of arbitraries — used by the Mix factory to pick a
    // datatype Height that dominates all children (so Mix.Valid is well-founded).
    ghost function MaxArbHeight<T>(s: seq<Arbitrary<T>>): nat {
        if |s| == 0 then 0
        else
            var rest := MaxArbHeight(s[1..]);
            var hd := s[0].internalFunction.Height();
            if hd > rest then hd else rest
    }

    lemma MaxArbHeightUpperBound<T>(s: seq<Arbitrary<T>>, i: int)
        requires 0 <= i < |s|
        ensures s[i].internalFunction.Height() <= MaxArbHeight(s)
    {
        if i == 0 {
        } else {
            MaxArbHeightUpperBound(s[1..], i - 1);
        }
    }

    // ================================================================
    // letrec-style recursive generators (Ã  la fast-check's letrec).
    //
    // A `Registry<T>` ties mutually-recursive arbitraries together by name.
    // Build each named arbitrary using `reg.Tie(name)` wherever a recursive
    // position appears, `Register` them, then `Lookup` the entry point:
    //
    //   var reg := new Registry<Tree>("Leaf", 5);            // base key + maxDepth
    //   var node := Arbitrary.Tuple(reg.Tie("Tree"), reg.Tie("Tree"))
    //                 .Map((t) => Node(t.0, t.1));
    //   reg.Register("Leaf", Arbitrary.Just(Leaf));
    //   reg.Register("Node", node);
    //   reg.Register("Tree", Arbitrary.Mix([reg.Tie("Leaf"), reg.Tie("Node")]));
    //   var arb := reg.Lookup("Tree");
    //
    // Each `Tie(name)` returns a FRESH lazy node with a singleton repr, so
    // distinct ties satisfy the pairwise-disjointness preconditions of Tuple/Mix
    // even though they alias the same registry slot. At Apply time a lazy resolves
    // its name in the registry; the TestCase `depth` field is the recursion
    // budget â€” at `maxDepth` the lazy yields the registry's base-case arbitrary
    // instead of recursing, which is what makes generation terminate (the base
    // case must be non-recursive). Like FlatMap, the resolve-through-dispatch step
    // carries an accepted "decreases" obligation and a couple of framing axioms.
    // ================================================================
    class Registry<T(!new)> {
        var arbs: map<string, Arbitrary<T>>
        const baseKey: string
        const maxDepth: nat

        constructor(baseKey: string, maxDepth: nat)
            ensures fresh(this)
            ensures this.baseKey == baseKey && this.maxDepth == maxDepth
        {
            this.arbs := map[];
            this.baseKey := baseKey;
            this.maxDepth := maxDepth;
        }

        // Register (or replace) the arbitrary bound to `key`.
        method Register(key: string, arb: Arbitrary<T>)
            modifies this`arbs
            ensures key in this.arbs && this.arbs[key] == arb
        {
            this.arbs := this.arbs[key := arb];
        }

        // A lazy reference to the arbitrary bound to `key`, resolved at Apply time.
        // Fresh + singleton repr so multiple ties are mutually disjoint.
        method Tie(key: string) returns (a: Arbitrary<T>)
            ensures a.Valid()
        {
            a := Arbitrary(LazyT(this, key));
            assert a.internalFunction is LazyArbitrary<T>;
        }

        function Lookup(key: string): Arbitrary<T>
            reads this
            requires key in this.arbs
        {
            this.arbs[key]
        }
    }

    datatype LazyArbitrary<T(!new)> extends Transformable<T> = LazyT(registry: Registry<T>, key: string) {
        ghost function Height(): nat { 0 }
        // The lazy node owns nothing but itself, so Valid() stays trivially
        // well-formed regardless of the (possibly self-referential) registry it
        // points into. Termination through the letrec cycle rests entirely on the
        // buffer metric (the marker draw below), so Height is 0.
        ghost predicate Valid()
            decreases Height(), 0
        {
            true
        }

        method Apply(tc: TestCase) returns (result: Option<T>)
            requires allocated(tc)
            requires this.Valid()
            requires tc.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, Height(), 0
            modifies tc, tc.random
        {
            var d0 := tc.depth;
            // Draw a control marker so the buffer STRICTLY drops before dispatching into
            // the registry target (not in our repr, so repr can't break the decreases tie).
            // Finite-buffer bound: each recursive expansion consumes >= 1 choice, so the
            // maxSize - |choices| metric decreases through the letrec cycle. On exhaustion
            // the expansion aborts (None), mirroring Hypothesis raising StopTest. The
            // depth/maxDepth budget still steers recursion toward the base case (the
            // max_leaves analog), but termination now rests on the buffer, not the budget.
            var marker := tc.MakeChoice(2);
            if marker.value.None? { return None; }
            // At the depth budget, force the registry's base case (must be
            // non-recursive); otherwise descend one level.
            var useBase := d0 >= registry.maxDepth;
            var k := if useBase then registry.baseKey else key;
            // Framing axioms: the named arbitrary exists and is well-formed, and a
            // registry built before this run cannot alias the fresh-per-run
            // TestCase. (Same style as RunTest's rng-disjointness assumption.)
            assume {:axiom} k in registry.arbs;
            var target := registry.arbs[k];
            assume {:axiom} target.Valid();
            if !useBase {
                tc.depth := d0 + 1;
            }
            result := target.internalFunction.Apply(tc);
            tc.depth := d0;  // restore so siblings recurse to the same budget
        }
    }

    datatype Arbitrary<T> = Arbitrary(internalFunction: Transformable<T>) {


        ghost predicate Valid()
            decreases internalFunction.Height(), 1
        {
            this.internalFunction.Valid()
        }

        method Apply(tc: TestCase) returns (result: Option<T>)
            requires tc.Valid()
            requires this.Valid()
            ensures this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures |tc.choices| >= old(|tc.choices|)
            ensures tc.maxSize == old(tc.maxSize)
            decreases tc.maxSize - |tc.choices|, internalFunction.Height(), 1
            modifies tc, tc.random
        {
          result := this.internalFunction.Apply(tc);
        }

        method Map<U>(fn: T -> U) returns (p: Arbitrary<U>)
            requires Valid()
            ensures p.Valid()
        {
          p := Arbitrary(MapT(this, fn, this.internalFunction.Height() + 1));
          assert p.internalFunction is MapTransformable<U, T>;
        }
        //

        static method Of<T>(args: seq<T>) returns (p: Arbitrary<T>)
            ensures p.Valid()
            requires 0 < |args| <= MaxChoice
        {
            p := Arbitrary(OfT(args));
            assert p.internalFunction is OfTransformable<T>;
        }

        static method Just<T>(value: T) returns (p: Arbitrary<T>)
            ensures p.Valid()
        {
            p := Arbitrary(JustT(value));
            assert p.internalFunction is JustTransformable<T>;
        }

        static method Range(min: int, max: int) returns (p: Arbitrary<int>)
            ensures p.Valid()
            requires min <= max && (0 < max- min < MaxChoice)
        {
            p := Arbitrary(RangeT(min, max));
            assert p.internalFunction is RangeTransformable;
        }

        // static method Nothing<T>() returns (p: Arbitrary<T>)
        //     ensures fresh(p)
        // {
        //     var nothingTransformable := new NothingTransformable<T>();
        //     p := new Arbitrary<T>(nothingTransformable);
        // }

        static method Mix<T>(possibilities: seq<Arbitrary<T>>) returns (p: Arbitrary<T>)
            requires 0 < |possibilities| < MaxChoice
            requires forall i :: 0 <= i < |possibilities| ==> possibilities[i].Valid()
            ensures p.Valid()
        {
            ghost var hh := MaxArbHeight(possibilities) + 1;
            forall i | 0 <= i < |possibilities|
                ensures possibilities[i].internalFunction.Height() < hh
            {
                MaxArbHeightUpperBound(possibilities, i);
            }
            p := Arbitrary(MixT(possibilities, hh));
            assert p.internalFunction is MixTransformable<T>;
        }

        static method Bools() returns (p: Arbitrary<bool>)
            ensures p.Valid()
        {
            p := Arbitrary(BoolsT);
            assert p.internalFunction is BoolsTransformable;
        }

        static method Nats(bound: nat) returns (p: Arbitrary<nat>)
            requires 0 < bound <= MaxChoice
            ensures p.Valid()
        {
            p := Arbitrary(NatsT(bound));
            assert p.internalFunction is NatsTransformable;
        }

        static method Chars() returns (p: Arbitrary<char>)
            ensures p.Valid()
        {
            p := Arbitrary(CharsT);
            assert p.internalFunction is CharsTransformable;
        }

        static method Reals() returns (p: Arbitrary<real>)
            ensures p.Valid()
        {
            p := Arbitrary(RealsT);
            assert p.internalFunction is RealsTransformable;
        }

        static method BitVectors1() returns (p: Arbitrary<bv1>)
            ensures p.Valid()
        { p := Arbitrary(BV1T); assert p.internalFunction is BitVectors1Transformable; }

        static method BitVectors2() returns (p: Arbitrary<bv2>)
            ensures p.Valid()
        { p := Arbitrary(BV2T); assert p.internalFunction is BitVectors2Transformable; }

        static method BitVectors8() returns (p: Arbitrary<bv8>)
            ensures p.Valid()
        { p := Arbitrary(BV8T); assert p.internalFunction is BitVectors8Transformable; }

        static method BitVectors16() returns (p: Arbitrary<bv16>)
            ensures p.Valid()
        { p := Arbitrary(BV16T); assert p.internalFunction is BitVectors16Transformable; }

        static method BitVectors32() returns (p: Arbitrary<bv32>)
            ensures p.Valid()
        { p := Arbitrary(BV32T); assert p.internalFunction is BitVectors32Transformable; }

        static method BitVectors64() returns (p: Arbitrary<bv64>)
            ensures p.Valid()
        { p := Arbitrary(BV64T); assert p.internalFunction is BitVectors64Transformable; }

        static method BitVectors128() returns (p: Arbitrary<bv128>)
            ensures p.Valid()
        { p := Arbitrary(BV128T); assert p.internalFunction is BitVectors128Transformable; }

        static method BitVectors256() returns (p: Arbitrary<bv256>)
            ensures p.Valid()
        { p := Arbitrary(BV256T); assert p.internalFunction is BitVectors256Transformable; }

        // Collections derived from the verified Lists/Tuple/Map combinators â€”
        // generate a seq and project it to the target collection type.
        static method Sets<S(==)>(elementGenerator: Arbitrary<S>, minSize: int, maxSize: int)
            returns (p: Arbitrary<set<S>>)
            requires 0 <= minSize <= maxSize
            requires elementGenerator.Valid()
            ensures p.Valid()
        {
            var listGen := Lists<S>(elementGenerator, minSize, maxSize);
            p := listGen.Map((xs: seq<S>) => (set x | x in xs));
        }

        static method Multisets<S(==)>(elementGenerator: Arbitrary<S>, minSize: int, maxSize: int)
            returns (p: Arbitrary<multiset<S>>)
            requires 0 <= minSize <= maxSize
            requires elementGenerator.Valid()
            ensures p.Valid()
        {
            var listGen := Lists<S>(elementGenerator, minSize, maxSize);
            p := listGen.Map((xs: seq<S>) => multiset(xs));
        }

        static method Maps<K(==), V>(keyGen: Arbitrary<K>, valGen: Arbitrary<V>, minSize: int, maxSize: int)
            returns (p: Arbitrary<map<K, V>>)
            requires 0 <= minSize <= maxSize
            requires keyGen.Valid() && valGen.Valid()
            ensures p.Valid()
        {
            var pairGen := Tuple<K, V>(keyGen, valGen);
            var listGen := Lists<(K, V)>(pairGen, minSize, maxSize);
            p := listGen.Map((pairs: seq<(K, V)>) => SeqToMap(pairs));
        }

        static method Arrays<S>(elementGenerator: Arbitrary<S>, minSize: int, maxSize: int)
            returns (p: Arbitrary<array<S>>)
            requires 0 <= minSize <= maxSize
            requires elementGenerator.Valid()
            ensures p.Valid()
        {
            p := Arbitrary(ArraysT(elementGenerator, minSize, maxSize, elementGenerator.internalFunction.Height() + 1));
            assert p.internalFunction is ArraysTransformable<S>;
        }

        // Fixed-size 2-D array generator: every value is a rows x cols array2<S>.
        static method Array2<S>(elementGenerator: Arbitrary<S>, rows: nat, cols: nat)
            returns (p: Arbitrary<array2<S>>)
            requires elementGenerator.Valid()
            ensures p.Valid()
        {
            p := Arbitrary(Array2T(elementGenerator, rows, cols, elementGenerator.internalFunction.Height() + 1));
            assert p.internalFunction is Array2Transformable<S>;
        }

        // Fixed-size 3-D array generator: every value is a rows x cols x layers array3<S>.
        static method Array3<S>(elementGenerator: Arbitrary<S>, rows: nat, cols: nat, layers: nat)
            returns (p: Arbitrary<array3<S>>)
            requires elementGenerator.Valid()
            ensures p.Valid()
        {
            p := Arbitrary(Array3T(elementGenerator, rows, cols, layers, elementGenerator.internalFunction.Height() + 1));
            assert p.internalFunction is Array3Transformable<S>;
        }

        // (Recursive/letrec generators are provided via the Registry class above,
        // not as a static factory here â€” see Registry.Tie / Register / Lookup.)

        // n-tuple generators (3..10). Each constructs its dedicated TupleN
        // datatype, whose Apply draws the N children directly and builds the flat
        // tuple in one step — no nested pairs, no Map flatten, no intermediate
        // allocations. h is the sum of child heights + 1, so every child is < h.
        static method Tuple3<A, B, C>(a: Arbitrary<A>, b: Arbitrary<B>, c: Arbitrary<C>)
            returns (p: Arbitrary<(A, B, C)>)
            requires a.Valid() && b.Valid() && c.Valid()
            ensures p.Valid()
        {
            ghost var hh := a.internalFunction.Height() + b.internalFunction.Height() +
                            c.internalFunction.Height() + 1;
            p := Arbitrary(Tuple3T(a, b, c, hh));
            assert p.internalFunction is Tuple3Transformable<A, B, C>;
        }

        static method Tuple4<A, B, C, D>(a: Arbitrary<A>, b: Arbitrary<B>, c: Arbitrary<C>, d: Arbitrary<D>)
            returns (p: Arbitrary<(A, B, C, D)>)
            requires a.Valid() && b.Valid() && c.Valid() && d.Valid()
            ensures p.Valid()
        {
            ghost var hh := a.internalFunction.Height() + b.internalFunction.Height() +
                            c.internalFunction.Height() + d.internalFunction.Height() + 1;
            p := Arbitrary(Tuple4T(a, b, c, d, hh));
            assert p.internalFunction is Tuple4Transformable<A, B, C, D>;
        }

        static method Tuple5<A, B, C, D, E>(a: Arbitrary<A>, b: Arbitrary<B>, c: Arbitrary<C>,
                d: Arbitrary<D>, e: Arbitrary<E>)
            returns (p: Arbitrary<(A, B, C, D, E)>)
            requires a.Valid() && b.Valid() && c.Valid() && d.Valid() && e.Valid()
            ensures p.Valid()
        {
            ghost var hh := a.internalFunction.Height() + b.internalFunction.Height() +
                            c.internalFunction.Height() + d.internalFunction.Height() +
                            e.internalFunction.Height() + 1;
            p := Arbitrary(Tuple5T(a, b, c, d, e, hh));
            assert p.internalFunction is Tuple5Transformable<A, B, C, D, E>;
        }

        static method Tuple6<A, B, C, D, E, F>(a: Arbitrary<A>, b: Arbitrary<B>, c: Arbitrary<C>,
                d: Arbitrary<D>, e: Arbitrary<E>, f: Arbitrary<F>)
            returns (p: Arbitrary<(A, B, C, D, E, F)>)
            requires a.Valid() && b.Valid() && c.Valid() && d.Valid() && e.Valid() && f.Valid()
            ensures p.Valid()
        {
            ghost var hh := a.internalFunction.Height() + b.internalFunction.Height() +
                            c.internalFunction.Height() + d.internalFunction.Height() +
                            e.internalFunction.Height() + f.internalFunction.Height() + 1;
            p := Arbitrary(Tuple6T(a, b, c, d, e, f, hh));
            assert p.internalFunction is Tuple6Transformable<A, B, C, D, E, F>;
        }

        static method Tuple7<A, B, C, D, E, F, G>(a: Arbitrary<A>, b: Arbitrary<B>, c: Arbitrary<C>,
                d: Arbitrary<D>, e: Arbitrary<E>, f: Arbitrary<F>, g: Arbitrary<G>)
            returns (p: Arbitrary<(A, B, C, D, E, F, G)>)
            requires a.Valid() && b.Valid() && c.Valid() && d.Valid() && e.Valid() && f.Valid() && g.Valid()
            ensures p.Valid()
        {
            ghost var hh := a.internalFunction.Height() + b.internalFunction.Height() +
                            c.internalFunction.Height() + d.internalFunction.Height() +
                            e.internalFunction.Height() + f.internalFunction.Height() +
                            g.internalFunction.Height() + 1;
            p := Arbitrary(Tuple7T(a, b, c, d, e, f, g, hh));
            assert p.internalFunction is Tuple7Transformable<A, B, C, D, E, F, G>;
        }

        static method Tuple8<A, B, C, D, E, F, G, H>(a: Arbitrary<A>, b: Arbitrary<B>, c: Arbitrary<C>,
                d: Arbitrary<D>, e: Arbitrary<E>, f: Arbitrary<F>, g: Arbitrary<G>, h: Arbitrary<H>)
            returns (p: Arbitrary<(A, B, C, D, E, F, G, H)>)
            requires a.Valid() && b.Valid() && c.Valid() && d.Valid() && e.Valid() && f.Valid() && g.Valid() && h.Valid()
            ensures p.Valid()
        {
            ghost var hh := a.internalFunction.Height() + b.internalFunction.Height() +
                            c.internalFunction.Height() + d.internalFunction.Height() +
                            e.internalFunction.Height() + f.internalFunction.Height() +
                            g.internalFunction.Height() + h.internalFunction.Height() + 1;
            p := Arbitrary(Tuple8T(a, b, c, d, e, f, g, h, hh));
            assert p.internalFunction is Tuple8Transformable<A, B, C, D, E, F, G, H>;
        }

        static method Tuple9<A, B, C, D, E, F, G, H, I>(a: Arbitrary<A>, b: Arbitrary<B>, c: Arbitrary<C>,
                d: Arbitrary<D>, e: Arbitrary<E>, f: Arbitrary<F>, g: Arbitrary<G>, h: Arbitrary<H>, i: Arbitrary<I>)
            returns (p: Arbitrary<(A, B, C, D, E, F, G, H, I)>)
            requires a.Valid() && b.Valid() && c.Valid() && d.Valid() && e.Valid() && f.Valid() && g.Valid() && h.Valid() && i.Valid()
            ensures p.Valid()
        {
            ghost var hh := a.internalFunction.Height() + b.internalFunction.Height() +
                            c.internalFunction.Height() + d.internalFunction.Height() +
                            e.internalFunction.Height() + f.internalFunction.Height() +
                            g.internalFunction.Height() + h.internalFunction.Height() +
                            i.internalFunction.Height() + 1;
            p := Arbitrary(Tuple9T(a, b, c, d, e, f, g, h, i, hh));
            assert p.internalFunction is Tuple9Transformable<A, B, C, D, E, F, G, H, I>;
        }

        static method Tuple10<A, B, C, D, E, F, G, H, I, J>(a: Arbitrary<A>, b: Arbitrary<B>, c: Arbitrary<C>,
                d: Arbitrary<D>, e: Arbitrary<E>, f: Arbitrary<F>, g: Arbitrary<G>, h: Arbitrary<H>,
                i: Arbitrary<I>, j: Arbitrary<J>)
            returns (p: Arbitrary<(A, B, C, D, E, F, G, H, I, J)>)
            requires a.Valid() && b.Valid() && c.Valid() && d.Valid() && e.Valid() && f.Valid() && g.Valid() && h.Valid() && i.Valid() && j.Valid()
            ensures p.Valid()
        {
            ghost var hh := a.internalFunction.Height() + b.internalFunction.Height() +
                            c.internalFunction.Height() + d.internalFunction.Height() +
                            e.internalFunction.Height() + f.internalFunction.Height() +
                            g.internalFunction.Height() + h.internalFunction.Height() +
                            i.internalFunction.Height() + j.internalFunction.Height() + 1;
            p := Arbitrary(Tuple10T(a, b, c, d, e, f, g, h, i, j, hh));
            assert p.internalFunction is Tuple10Transformable<A, B, C, D, E, F, G, H, I, J>;
        }

        static method Lists<S>(elementGenerator: Arbitrary<S>, minSize: int, maxSize: int) returns (p: Arbitrary<seq<S>>)
            requires 0 <= minSize <= maxSize
            requires elementGenerator.Valid()
            ensures p.Valid()
        {
            p := Arbitrary(ListsT(elementGenerator, minSize, maxSize, elementGenerator.internalFunction.Height() + 1));
            assert p.internalFunction is ListsTransformable<S>;
        }

        static method Strings(minLength: int, maxLength: int, ascii: bool) returns (p: Arbitrary<string>)
            requires 0 <= minLength <= maxLength
            ensures p.Valid()
        {
            p := Arbitrary(StringsT(minLength, maxLength, ascii));
            assert p.internalFunction is StringsTransformable;
        }

        static method Tuple<T, U>(firstGenerator: Arbitrary<T>, secondGenerator: Arbitrary<U>) returns (p: Arbitrary<(T, U)>)
            requires firstGenerator.Valid()
            requires secondGenerator.Valid()
            ensures p.Valid()
        {
            ghost var fh := firstGenerator.internalFunction.Height();
            ghost var sh := secondGenerator.internalFunction.Height();
            p := Arbitrary(TupleT(firstGenerator, secondGenerator, (if fh > sh then fh else sh) + 1));
            assert p.internalFunction is TupleTransformable<T, U>;
        }

        method FlatMap<U>(f: FlatMapFn<T, U>) returns (p: Arbitrary<U>)
            requires Valid()
            ensures p.Valid()
        {
            // We need a new Transformable that knows how to do the FlatMap logic.
            p := Arbitrary(FlatMapT(this, f, this.internalFunction.Height() + 1));
            assert p.internalFunction is FlatMapTransformable<T, U>;
        }

    }
}