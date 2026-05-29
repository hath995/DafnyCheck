include "./RandomGenerator.dfy"
include "./TestStatus.dfy"
include "./TestResult.dfy"
module Arbitrary {
  import opened TestResult
  import opened RandomGenerator
  import opened TestTypes
  import opened Std.Wrappers
  class TestCase {
    ghost var repr: set<object>
    var prefix: seq<bv64>
    var random: XoroShift128Plus
    var maxSize: nat
    var printResults: bool
    var depth: nat
    var targetingScore: nat
    var choices: seq<bv64>

    ghost predicate Valid()
      reads this
    {
      this.repr == {this, random}
    }

    constructor(prefix: seq<bv64>, random: XoroShift128Plus, maxSize: nat, printResults: bool)
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
    static method ForChoices(choices: seq<bv64>, printResults: bool) returns (tc: TestCase)
      requires 0 < |choices|
      ensures fresh(tc)
      ensures fresh(tc.random)
      ensures tc.Valid()
      ensures tc.prefix == choices
    {
      var random := XoroShift128Plus.fromSeed(42); // Default seed
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
    method ForcedChoice(n: bv64) returns (result: TestResult<bv64>)
      requires 0 <= n
      ensures result.value.Some? ==> |choices| > old(|choices|)
      ensures old(this.Valid()) ==> this.Valid()
      ensures old(repr) == repr
      modifies this
    {
      if (n < 0) {
        // TODO: Handle IllegalArgumentException
        assert false;
      }
      if (|choices| > maxSize) {
        result := new TestResult<bv64>(Some(OVERRUN), None);
        return;
      }
      choices := choices + [n];
      result := new TestResult<bv64>(None, Some(n));
    }

    // Boolean choice with 50% probability
    method BooleanChoice() returns (result: bool)
      ensures old(this.Valid()) ==> this.Valid()
      // ensures old(repr) == repr
      modifies this, random
    {
      result := Weighted(0.5);
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
      ensures old(this.Valid()) ==> this.Valid()
      ensures old(repr) == repr
    //   ensures result.value.Some?
      modifies this, random
    {
      var intResult: TestResult<bv64>;
      if (p <= 0.0) {
        intResult := ForcedChoice(0);
      } else if (p >= 1.0) {
        intResult := ForcedChoice(1);
      } else {
        var randomValue := this.random.unsafeNextReal();
        var choice := if randomValue < p then 1 else 0;
        // this.repr := {this, c};
        intResult := new TestResult<bv64>(None, Some(choice));
      }
      result := intResult.Map<bool>((i) => i == 1);
    }

    // Internal method to make a choice
    method MakeChoice(n: bv64) returns (result: TestResult<bv64>)
      requires 0 < n
      ensures old(this.Valid()) ==> this.Valid()
      ensures old(repr) == repr
      modifies this`choices, random
      // ensures result.value.Some? ==> result.value.Extract() < n
    {
      result := MakeChoice_(n, (rand) => rand % n);
    }

    // Internal method to make a choice with custom random function
    method MakeChoice_(n: bv64, randomFunc: bv64 -> bv64) returns (result: TestResult<bv64>)
      requires 0 < n
      ensures old(this.Valid()) ==> this.Valid()
      ensures old(repr) == repr
      modifies this`choices, random
      // ensures result.value.Some? ==> exists x: bv64 :: randomFunc(x) == result.value.Extract();
    {
      if (|choices| >= maxSize) {
        result := new TestResult<bv64>(Some(OVERRUN), None);
        return;
      }

      var choiceResult: bv64;
      if (|choices| < |prefix|) {
        choiceResult := prefix[|choices|];
      } else {
        var rand := this.random.unsafeNext();
        choiceResult := randomFunc(rand);
      }
      if (choiceResult > n) {
        result := new TestResult<bv64>(Some(INVALID), None);
        return;
      }
      choices := choices + [choiceResult];
      result := new TestResult<bv64>(None, Some(choiceResult));
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
    function GetChoices(): seq<bv64>
      reads this
    {
      choices
    }

    // Apply a possibility to generate a value
    method Any<T>(possibility: Arbitrary<T>) returns (result: T)
      requires possibility.internalFunction.repr !! this.repr
      requires possibility.Valid()
      requires Valid()
      // decreases parentRepr
      modifies this, random
      ensures Valid()
      ensures this.random == old(this.random)
      ensures this.repr == old(this.repr)
      ensures possibility.Valid()
      ensures possibility.internalFunction.repr == old(possibility.internalFunction.repr)
    {
      this.depth := this.depth + 1;
      result := possibility.Apply(this);
    //   this.depth := this.depth - 1;
    }
  }

    const MaxLong := 0xFFFFFFFFFFFFFFFF
    trait Transformable<T> {
        ghost var repr: set<object>
        ghost var childRepr: set<object>
        method Apply(tc: TestCase) returns (result: T)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            requires tc.repr !! this.repr
            ensures this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures this.repr == old(this.repr)
            decreases repr, childRepr
            modifies tc, tc.random

        ghost predicate Valid()
            reads this, repr, childRepr
            ensures Valid() ==> this in repr
            ensures Valid() ==> childRepr < this.repr
            ensures Valid() ==> this.repr == {this} + childRepr
            decreases repr, childRepr
    }

    class OfTransformable<T> extends Transformable<T> {
        var args: seq<T>
        constructor(args: seq<T>)
            ensures fresh(this)
            ensures fresh(this.repr)
            requires 0 < |args| <= MaxLong
            ensures Valid()
        {
            this.args := args;
            this.childRepr := {};
            this.repr := {this} + this.childRepr;
        }

        ghost predicate Valid()
            reads this
            ensures Valid() ==> this in repr
            ensures Valid() ==> childRepr < this.repr
            ensures Valid() ==> this.repr == {this} + childRepr
            decreases repr, childRepr
        {
            this in repr && 0 < |args| <= MaxLong && childRepr < this.repr && this.repr == {this} + childRepr
        }

        method Apply(tc: TestCase) returns (result: T)
            requires allocated(tc)
            requires this.Valid()
            requires tc.Valid()
            requires tc.repr !! this.repr
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures this.repr == old(this.repr)
            decreases repr, childRepr
            modifies tc, tc.random
        {
            var choiceResult := tc.MakeChoice(|args| as bv64);
            if choiceResult.value.Some? {
                expect choiceResult.value.Extract() as int < |args|;
                return args[choiceResult.Unwrap() as int];
            }else{
                return args[0];
            }
        }
    }

    class JustTransformable<T> extends Transformable<T> {
        var value: T
        constructor(value: T)
            ensures fresh(this)
            ensures fresh(this.repr)
            ensures Valid()
        {
            this.value := value;
            this.childRepr := {};
            this.repr := {this} + this.childRepr;
        }

        ghost predicate Valid()
            reads this
            ensures Valid() ==> this in repr
            ensures Valid() ==> childRepr < this.repr
            ensures Valid() ==> this.repr == {this} + childRepr
            decreases repr, childRepr
        {
            this in this.repr && childRepr < this.repr && this.repr == {this} + childRepr
        }

        method Apply(tc: TestCase) returns (result: T)
            requires allocated(tc)
            requires this.Valid()
            requires tc.Valid()
            requires tc.repr !! this.repr
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures this.repr == old(this.repr)
            decreases repr, childRepr
            modifies tc, tc.random
        {
            result := this.value;
        }
    }

    class RangeTransformable extends Transformable<int> {
        var min: int
        var max: int
        constructor(min: int, max: int)
            ensures fresh(this)
            ensures fresh(this.repr)
            requires min <= max && (0 < max - min <= MaxLong)
            ensures Valid()
        {
            this.min := min;
            this.max := max;
            this.childRepr := {};
            this.repr := {this} + this.childRepr;
        }

        ghost predicate Valid()
            reads this
            ensures Valid() ==> this in repr
            ensures Valid() ==> childRepr < this.repr
            ensures Valid() ==> this.repr == {this} + childRepr
            decreases repr, childRepr
        {
            this in repr && min <= max && (0 < max - min <= MaxLong) && childRepr < this.repr && this.repr == {this} + childRepr
        }

        method Apply(tc: TestCase) returns (result: int)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            requires tc.repr !! this.repr
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures this.repr == old(this.repr)
            decreases repr, childRepr
            modifies tc, tc.random
        {
            var choiceResult := tc.MakeChoice((max - min) as bv64);
            if choiceResult.value.Some? {
                result := min + (choiceResult.Unwrap() as int);
            } else {
                result := min;
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

    class MixTransformable<T> extends Transformable<T> {
        var possibilities: seq<Arbitrary<T>>
        constructor(possibilities: seq<Arbitrary<T>>)
            ensures fresh(this)
            // ensures fresh(this.repr)
            requires 0 < |possibilities| < MaxLong
            requires forall x,y :: x in possibilities && y in possibilities ==> x.internalFunction.repr !! y.internalFunction.repr
            requires forall i :: 0 <= i < |possibilities| ==> possibilities[i].Valid()
            ensures Valid()
        {
            this.possibilities := possibilities;
            this.childRepr := set p, q | p in possibilities && q in p.internalFunction.repr :: q;
            this.repr := {this} + this.childRepr;
        }

        ghost predicate Valid()
            reads this, repr, childRepr
            ensures Valid() ==> this in repr
            ensures Valid() ==> childRepr < this.repr
            ensures Valid() ==> this.repr == {this} + childRepr
            decreases repr, childRepr
        {
            this in repr && 
            0 < |possibilities| < MaxLong && 
            (forall i :: 0 <= i < |possibilities| ==> possibilities[i].internalFunction in childRepr) &&
            (forall i :: 0 <= i < |possibilities| ==> possibilities[i].internalFunction.repr <= childRepr) &&
            (forall x,y :: x in possibilities && y in possibilities ==> x.internalFunction.repr !! y.internalFunction.repr) &&
            (forall i :: 0 <= i < |possibilities| ==> possibilities[i].Valid()) &&
            childRepr < this.repr && 
            this.repr == {this} + childRepr
        }

        method Apply(tc: TestCase) returns (result: T)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            requires tc.repr !! this.repr
            ensures this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures this.repr == old(this.repr)
            decreases repr, childRepr
            modifies tc, tc.random
        {
            var choiceResult := tc.MakeChoice(|possibilities| as bv64);
            if choiceResult.value.Some? {
                var choice := choiceResult.Unwrap() as int;
                expect choice < |possibilities|;
                // result := tc.Any(possibilities[choice]);
                result := possibilities[choice].internalFunction.Apply(tc);
            } else {
                // result := tc.Any(possibilities[0]);
                result := possibilities[0].internalFunction.Apply(tc);
            }
        }
    }

    class BoolsTransformable extends Transformable<bool> {
        constructor()
            ensures fresh(this)
            ensures fresh(this.repr)
            ensures Valid()
        {
            this.childRepr := {};
            this.repr := {this} + this.childRepr;
        }

        ghost predicate Valid()
            reads this
            ensures Valid() ==> this in repr
            ensures Valid() ==> childRepr < this.repr
            ensures Valid() ==> this.repr == {this} + childRepr
            decreases repr, childRepr
        {
            this.repr == {this} + childRepr && childRepr < this.repr
        }

        method Apply(tc: TestCase) returns (result: bool)
            requires allocated(tc)
            requires this.Valid()
            requires tc.repr !! this.repr
            ensures this.repr == old(this.repr)
            requires tc.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            decreases repr, childRepr
            modifies tc, tc.random
        {
            var choiceResult := tc.MakeChoice(2);
            if choiceResult.value.Some? {
                result := choiceResult.Unwrap() == 1;
            } else {
                result := false;
            }
        }
    }

    class ListsTransformable<S> extends Transformable<seq<S>> {
        var elementGenerator: Arbitrary<S>
        var minSize: int
        var maxSize: int
        constructor(elementGenerator: Arbitrary<S>, minSize: int, maxSize: int)
            requires 0 <= minSize <= maxSize
            requires elementGenerator.Valid()
            ensures elementGenerator.internalFunction.repr < this.repr
            ensures this.repr == {this}+elementGenerator.internalFunction.repr
            ensures fresh(this)
            ensures Valid()
        {
            this.elementGenerator := elementGenerator;
            this.minSize := minSize;
            this.maxSize := maxSize;
            this.childRepr := elementGenerator.internalFunction.repr;
            this.repr := {this} + this.childRepr;
        }

        ghost predicate Valid()
            decreases repr, childRepr
            ensures Valid() ==> this in repr
            ensures Valid() ==> childRepr < this.repr
            ensures Valid() ==> this.repr == {this} + childRepr
            reads this, repr, childRepr
        {
            this in this.repr &&
            elementGenerator.internalFunction in this.repr &&
            elementGenerator.internalFunction.repr < this.repr &&
            0 <= minSize <= maxSize && elementGenerator.Valid() &&
            childRepr < this.repr && this.repr == {this} + childRepr
        }

        method Apply(tc: TestCase) returns (result: seq<S>)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            requires tc.repr !! this.repr
            // requires elementGenerator.internalFunction.repr == childRepr;
            ensures this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures this.repr == old(this.repr)
            decreases repr, childRepr
            modifies tc, tc.random
        {
            result := [];
            while true
                invariant |result| <= maxSize
                invariant tc.Valid()
                invariant tc.repr == old(tc.repr)
                modifies tc, tc.random
                decreases maxSize-|result|
            {
                if |result| < minSize {
                    // Force continue
                    var forceResult := tc.ForcedChoice(1);
                    if forceResult.err.Some? {
                        break;
                    }
                } else if |result| >= maxSize {
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
                result := result + [element];
            }
        }
    }

    class StringsTransformable extends Transformable<string> {
        var minLength: int
        var maxLength: int
        var ascii: bool
        constructor(minLength: int, maxLength: int, ascii: bool)
            ensures fresh(this)
            ensures fresh(this.repr)
            requires 0 <= minLength <= maxLength
            ensures Valid()
        {
            this.minLength := minLength;
            this.maxLength := maxLength;
            this.ascii := ascii;
            this.childRepr := {};
            this.repr := {this} + this.childRepr;
        }

        ghost predicate Valid()
            decreases repr, childRepr
            ensures Valid() ==> this in repr
            ensures Valid() ==> childRepr < this.repr
            ensures Valid() ==> this.repr == {this} + childRepr
            reads this, repr, childRepr
        {
          this in repr && 0 <= minLength <= maxLength && childRepr < this.repr && this.repr == {this} + childRepr
        }

        method {:isolate_assertions} Apply(tc: TestCase) returns (result: string)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            requires tc.repr !! this.repr
            ensures this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures this.repr == old(this.repr)
            decreases repr, childRepr
            modifies tc, tc.random
        {
            var chars: seq<nat> := [];
            while true
                invariant |chars| <= maxLength
                invariant tc.Valid()
                invariant tc.repr == old(tc.repr)
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
                var choiceResult := tc.MakeChoice(charChoice as bv64);
                var charValue := if choiceResult.value.Some? then choiceResult.Unwrap() else 0;
                assume {:axiom} 0 <= charValue < 0x0000D800;
                chars := chars + [charValue as nat];
            }
            result := "";
            for i := 0 to |chars|
                invariant |result| == i
            {
                assert chars[i] in chars; 
                result := result + [chars[i] as char];
            }
        }
    }

    class MapTransformable<T, U> extends Transformable<T> {
      var elementGenerator: Arbitrary<U>
      var fn: U-> T
      constructor(elementGenerator: Arbitrary<U>, fn: U->T)
          requires elementGenerator.Valid()
          ensures elementGenerator.internalFunction.repr < this.repr
          ensures this.repr == {this}+elementGenerator.internalFunction.repr
          ensures this.fn == fn
          ensures fresh(this)
          ensures Valid()
      {
        this.elementGenerator := elementGenerator;
        this.childRepr := elementGenerator.internalFunction.repr;
        this.fn := fn;
        this.repr := {this}+this.childRepr;
      }

        ghost predicate Valid()
            decreases repr, childRepr
            ensures Valid() ==> this in repr
            ensures Valid() ==> childRepr < this.repr
            ensures Valid() ==> this.repr == {this} + childRepr
            reads this, repr, childRepr
        {
          this in repr && this.repr == {this}+childRepr &&
            childRepr < repr &&
            elementGenerator.internalFunction in this.repr &&
            elementGenerator.internalFunction.repr < this.repr &&
            elementGenerator.Valid()
        }

        method Apply(tc: TestCase) returns (result: T)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            requires tc.repr !! this.repr
            ensures this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures this.repr == old(this.repr)
            decreases repr, childRepr
            modifies tc, tc.random
        {
          var element := elementGenerator.internalFunction.Apply(tc);
          result := fn(element);
        }
    }

    class TupleTransformable<T, U> extends Transformable<(T, U)> {
        var firstGenerator: Arbitrary<T>
        var secondGenerator: Arbitrary<U>
        
        constructor(firstGenerator: Arbitrary<T>, secondGenerator: Arbitrary<U>)
            requires firstGenerator.Valid()
            requires secondGenerator.Valid()
            ensures firstGenerator.internalFunction.repr < this.repr
            ensures secondGenerator.internalFunction.repr < this.repr
            ensures this.repr == {this} + firstGenerator.internalFunction.repr + secondGenerator.internalFunction.repr
            ensures fresh(this)
            ensures Valid()
        {
            this.firstGenerator := firstGenerator;
            this.secondGenerator := secondGenerator;
            this.childRepr := firstGenerator.internalFunction.repr + secondGenerator.internalFunction.repr;
            this.repr := {this} + this.childRepr;
        }

        ghost predicate Valid()
            decreases repr, childRepr
            ensures Valid() ==> this in repr
            ensures Valid() ==> childRepr < this.repr
            ensures Valid() ==> this.repr == {this} + childRepr
            reads this, repr, childRepr
        {
            this in repr && 
            this.repr == {this} + childRepr &&
            childRepr < repr &&
            firstGenerator.internalFunction in this.repr &&
            secondGenerator.internalFunction in this.repr &&
            firstGenerator.internalFunction.repr < this.repr &&
            secondGenerator.internalFunction.repr < this.repr &&
            firstGenerator.Valid() &&
            secondGenerator.Valid()
        }

        method Apply(tc: TestCase) returns (result: (T, U))
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            requires tc.repr !! this.repr
            ensures this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures this.repr == old(this.repr)
            decreases repr, childRepr
            modifies tc, tc.random
        {
            var first := firstGenerator.internalFunction.Apply(tc);
            var second := secondGenerator.internalFunction.Apply(tc);
            result := (first, second);
        }
    }


    trait FlatMapFn<T, U> {
        // This method creates a new Arbitrary<U> based on an input T
        method CreateArbitrary(t: T) returns (p: Arbitrary<U>)
            ensures p.Valid()
            ensures fresh(p.internalFunction.repr)
    }

    class FlatMapTransformable<T, U> extends Transformable<U> {
        var baseGenerator: Arbitrary<T> // The original generator
        var flatMapFn: FlatMapFn<T, U> // The factory function

        constructor(baseGenerator: Arbitrary<T>, flatMapFn: FlatMapFn<T, U>)
            requires baseGenerator.Valid()
            requires flatMapFn !in baseGenerator.internalFunction.repr
            ensures fresh(this)
            ensures this.childRepr == baseGenerator.internalFunction.repr+{flatMapFn}
            ensures Valid()
        {
            this.baseGenerator := baseGenerator;
            this.flatMapFn := flatMapFn;
            this.childRepr := baseGenerator.internalFunction.repr+{flatMapFn};
            this.repr := {this} + this.childRepr;
        }

        ghost predicate Valid()
            reads this, repr, childRepr
            ensures Valid() ==> this in repr
            ensures Valid() ==> childRepr < this.repr
            ensures Valid() ==> this.repr == {this} + childRepr
            decreases repr, childRepr
        {
            this in repr && this.repr == {this} + childRepr &&
            childRepr < repr &&
            baseGenerator.internalFunction in childRepr &&
            baseGenerator.internalFunction.repr < childRepr &&
            baseGenerator.Valid()
        }

        method Apply(tc: TestCase) returns (result: U)
            requires allocated(tc)
            requires tc.Valid()
            requires this.Valid()
            requires tc.repr !! this.repr
            ensures this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures this.repr == old(this.repr)
            decreases repr, childRepr
            modifies tc, tc.random
        {
            var intermediateValue := baseGenerator.internalFunction.Apply(tc); // First, generate T
            var nextArbitrary := flatMapFn.CreateArbitrary(intermediateValue); // Then, create Arbitrary<U>
            assert tc.repr !! nextArbitrary.internalFunction.repr; // Example assertion, might need to be required
            // KNOWN: "decreases clause might not decrease" verification error here is expected.
            // The repr/childRepr metric can't yet prove termination through the flatMap'd
            // nextArbitrary. Expected to fail until the termination proof is completed (future work).
            result := nextArbitrary.internalFunction.Apply(tc);

        }
    }

    datatype Arbitrary<T> = Arbitrary(internalFunction: Transformable<T>) {


        ghost predicate Valid()
            reads internalFunction, internalFunction.repr
            decreases internalFunction.repr, internalFunction.childRepr
        {
            internalFunction.repr > internalFunction.childRepr &&
            // KNOWN: "decreases clause might not decrease" verification error here is expected.
            // Same root cause as Transformable.Apply above; expected to fail until the
            // termination proof is completed (future work).
            this.internalFunction.Valid()
        }

        method Apply(tc: TestCase) returns (result: T)
            requires tc.Valid()
            requires this.Valid()
            requires tc.repr !! this.internalFunction.repr
            ensures this.Valid()
            ensures tc.Valid()
            ensures tc.repr == old(tc.repr)
            ensures this.internalFunction.repr == old(this.internalFunction.repr)
            decreases this, internalFunction.repr, internalFunction.childRepr
            modifies tc, tc.random
        {
          result := this.internalFunction.Apply(tc);
        }

        method Map<U>(fn: T -> U) returns (p: Arbitrary<U>)
            requires Valid()
            ensures p.Valid()
            ensures p.internalFunction.repr == {p.internalFunction}+this.internalFunction.repr
            ensures fresh(p.internalFunction)
            ensures fresh(this.internalFunction.repr) ==> fresh(p.internalFunction.repr)
        {
          var mapTransformable := new MapTransformable(this, fn);
          p := Arbitrary(mapTransformable);
        }
        // 

        static method Of<T>(args: seq<T>) returns (p: Arbitrary<T>)
            ensures p.Valid()
            ensures fresh(p.internalFunction)
            ensures fresh(p.internalFunction.repr)
            requires 0 < |args| <= MaxLong
        {
            var ofTransformable := new OfTransformable<T>(args);
            p := Arbitrary(ofTransformable);
        }

        static method Just<T>(value: T) returns (p: Arbitrary<T>)
            ensures p.Valid()
            ensures fresh(p.internalFunction)
            ensures fresh(p.internalFunction.repr)
        {
            var justTransformable := new JustTransformable<T>(value);
            p := Arbitrary(justTransformable);
        }

        static method Range(min: int, max: int) returns (p: Arbitrary<int>)
            ensures p.Valid()
            ensures fresh(p.internalFunction)
            ensures fresh(p.internalFunction.repr)
            requires min <= max && (0 < max- min < MaxLong)
        {
            var rangeTransformable := new RangeTransformable(min, max);
            p := Arbitrary(rangeTransformable);
        }

        // static method Nothing<T>() returns (p: Arbitrary<T>)
        //     ensures fresh(p)
        // {
        //     var nothingTransformable := new NothingTransformable<T>();
        //     p := new Arbitrary<T>(nothingTransformable);
        // }

        static method Mix<T>(possibilities: seq<Arbitrary<T>>) returns (p: Arbitrary<T>)
            requires 0 < |possibilities| < MaxLong
            requires forall i :: 0 <= i < |possibilities| ==> possibilities[i].Valid()
            requires forall x,y :: x in possibilities && y in possibilities ==> x.internalFunction.repr !! y.internalFunction.repr
            ensures p.Valid()
            ensures fresh(p.internalFunction)
            ensures forall x :: x in possibilities && fresh(x.internalFunction.repr) ==> fresh(p.internalFunction.repr)
        {
            var mixTransformable := new MixTransformable<T>(possibilities);
            p := Arbitrary(mixTransformable);
        }

        static method Bools() returns (p: Arbitrary<bool>)
            ensures p.Valid()
            ensures fresh(p.internalFunction)
            ensures fresh(p.internalFunction.repr)
        {
            var boolsTransformable := new BoolsTransformable();
            p := Arbitrary(boolsTransformable);
        }

        static method Lists<S>(elementGenerator: Arbitrary<S>, minSize: int, maxSize: int) returns (p: Arbitrary<seq<S>>)
            requires 0 <= minSize <= maxSize
            requires elementGenerator.Valid()
            ensures p.Valid()
            ensures p.internalFunction.repr == {p.internalFunction}+elementGenerator.internalFunction.repr
            ensures fresh(p.internalFunction)
            // ensures fresh(p.internalFunction.repr)
            ensures fresh(elementGenerator.internalFunction) ==>  fresh(p.internalFunction.repr)
        {
            var listsTransformable := new ListsTransformable<S>(elementGenerator, minSize, maxSize);
            p := Arbitrary(listsTransformable);
        }

        static method Strings(minLength: int, maxLength: int, ascii: bool) returns (p: Arbitrary<string>)
            requires 0 <= minLength <= maxLength
            ensures p.Valid()
            ensures fresh(p.internalFunction)
            ensures fresh(p.internalFunction.repr)
        {
            var stringsTransformable := new StringsTransformable(minLength, maxLength, ascii);
            p := Arbitrary(stringsTransformable);
        }

        static method Tuple<T, U>(firstGenerator: Arbitrary<T>, secondGenerator: Arbitrary<U>) returns (p: Arbitrary<(T, U)>)
            requires firstGenerator.Valid()
            requires secondGenerator.Valid()
            requires firstGenerator.internalFunction.repr !! secondGenerator.internalFunction.repr
            ensures p.Valid()
            ensures p.internalFunction.repr == {p.internalFunction} + firstGenerator.internalFunction.repr + secondGenerator.internalFunction.repr
            ensures fresh(p.internalFunction)
            ensures fresh(firstGenerator.internalFunction) && fresh(secondGenerator.internalFunction) ==> fresh(p.internalFunction.repr)
        {
            var tupleTransformable := new TupleTransformable<T, U>(firstGenerator, secondGenerator);
            p := Arbitrary(tupleTransformable);
        }

        method FlatMap<U>(f: FlatMapFn<T, U>) returns (p: Arbitrary<U>)
            requires Valid()
            requires f !in this.internalFunction.repr
            ensures p.Valid()
            ensures p.internalFunction.repr == {p.internalFunction}+this.internalFunction.repr+{f}
            ensures fresh(p.internalFunction)
            ensures fresh(this.internalFunction.repr) ==> fresh(p.internalFunction.repr)
        {
            // We need a new Transformable that knows how to do the FlatMap logic.
            var flatMapTransformable := new FlatMapTransformable(this, f);
            p := Arbitrary(flatMapTransformable);
        }

    }
}