include "../../src/DafnyCheck.dfy"
include "../../src/Arbitrary.dfy"
include "./bitonicSort.dfy"
include "./insertionSort.dfy"

// ============================================================================
// Case study: property-based testing of a *verified* bitonic sort.
//
// bitonicSort/bitonicMerge require a power-of-two length, and that precondition
// is the ghost `IsPowerOfTwo`. A runtime test predicate therefore needs a
// COMPILED power-of-two check bridged to the ghost one (`IsPow2` below) so the
// precondition can be discharged inside a lambda.
//
// Power-of-two-length inputs are generated two ways (per the framework's
// options): fixed-length `Lists(elem, L, L)`, and `FlatMap` over an exponent to
// get a mix of lengths. Bitonic inputs (to exercise `bitonicMerge`, which only
// sorts bitonic sequences) are built by SORTING a random list and ROTATING it,
// via `Map` — a rotation of a sorted run is exactly the bitonic shape.
//
// Each property is run under several fixed RNG SEEDS (see `SEEDS`) so the runs
// are reproducible yet explore different input streams. Since the algorithm is
// verified, the property runs PASS under every seed (a live demo + regression
// guard); one run is *expected to fail under every seed* — feeding bitonicMerge
// arbitrary (non-bitonic) inputs — to show the tool finding a counterexample.
// ============================================================================
module BitonicSortCaseStudy {
  import opened DafnyCheck
  import opened Arbitrary
  import opened RunConfig
  import opened BitonicSort
  import opened InsertionSort
  import opened LTLUtils
  import opened Std.Wrappers

  // A handful of fixed seeds — reproducible, but each drives a different stream
  // of generated inputs.
  const SEEDS: seq<bv64> := [1, 42, 1337, 271828, 8675309]

  // Run `pred` over `arb` once per seed. Returns whether ALL seeds passed and
  // whether ANY seed passed (the latter lets a negative test assert that *every*
  // seed found a counterexample).
  method RunSeeds(pred: seq<int> -> bool, arb: Arbitrary<seq<int>>, name: string)
    returns (allOk: bool, anyOk: bool)
    requires arb.Valid()
  {
    allOk := true;
    anyOk := false;
    var i := 0;
    while i < |SEEDS|
      invariant 0 <= i <= |SEEDS|
      invariant arb.Valid()           // RunTestWithConfig modifies nothing pre-existing
    {
      var cfg := DefaultConfig<seq<int>>().(seed := Some(SEEDS[i]));
      var nm := name + " [seed=" + IntToString(SEEDS[i] as int) + "]";
      var ok := RunTestWithConfig(pred, arb, nm, cfg);
      allOk := allOk && ok;
      anyOk := anyOk || ok;
      i := i + 1;
    }
  }

  // ---- bridge: a compiled power-of-two test, proven to imply the ghost one ----
  lemma NatPowDouble(k: nat)
    ensures natPow(2, k + 1) == 2 * natPow(2, k)
  { }

  function IsPow2(n: nat): bool
    ensures IsPow2(n) ==> IsPowerOfTwo(n)
    decreases n
  {
    if n == 0 then false
    else if n == 1 then
      assert IsPowerOfTwo(1) by { assert natPow(2, 0) == 1; }
      true
    else if n % 2 == 0 then
      var half := IsPow2(n / 2);
      if half then
        assert IsPowerOfTwo(n) by {
          var k :| k >= 0 && n / 2 == natPow(2, k);   // from IsPow2(n/2)'s postcondition
          NatPowDouble(k);
          assert n == natPow(2, k + 1);
        }
        true
      else false
    else false
  }

  // ---- build a bitonic sequence: sort a random list, then rotate it ----
  function SumSeq(s: seq<int>): int {
    if |s| == 0 then 0 else s[0] + SumSeq(s[1..])
  }

  // isort(s) is ascending (hence unimodal/bitonic); any rotation of it is still
  // bitonic. We pick a content-dependent rotation so different inputs give
  // different bitonic shapes.
  function MakeBitonic(s: seq<int>): seq<int>
  {
    if |s| == 0 then s
    else
      var srt := isort(s);
      assert |srt| == |s|;
      rotate(srt, SumSeq(s) % |s|)
  }

  // ---- FlatMap factory: exponent k -> a length-2^k list (k clamped to [0,5]) ----
  @AssumeCrossModuleTermination
  class Pow2Lists extends FlatMapFn<int, seq<int>> {
    constructor() ensures fresh(this) {}
    method CreateArbitrary(k: int) returns (p: Arbitrary<seq<int>>)
      ensures p.Valid()
      ensures fresh(p.internalFunction.repr)
    {
      var kk: nat := if k < 0 then 0 else if k > 5 then 5 else k;
      var elem := Arbitrary<int>.Range(0, 100);
      assert fresh(elem.internalFunction.repr);
      var len := natPow(2, kk);
      p := Arbitrary<seq<int>>.Lists(elem, len, len);
    }
  }

  // Helper: a fixed-length list generator over small ints.
  method FixedLenLists(len: int) returns (arb: Arbitrary<seq<int>>)
    requires 0 <= len
    ensures arb.Valid()
  {
    var elem := Arbitrary<int>.Range(0, 10);
    arb := Arbitrary<seq<int>>.Lists(elem, len, len);
  }

  // Helper: a mixed-length power-of-two list generator (lengths 1,2,4,…,32).
  method Pow2LenLists() returns (arb: Arbitrary<seq<int>>)
    ensures arb.Valid()
  {
    var kGen := Arbitrary<int>.Range(0, 6);
    assert fresh(kGen.internalFunction.repr);
    var fn := new Pow2Lists();
    arb := kGen.FlatMap(fn);
  }

  // ========================================================================
  // Property tests on the full sort. All are postconditions of bitonicSort,
  // so they PASS under every seed — a regression guard and a live demo.
  // ========================================================================

  method {:test} TestSortsAscendingFixed8()
  {
    var arb := FixedLenLists(8);
    var pred := (s: seq<int>) => (|s| == 0 || IsPow2(|s|)) ==> sortedAsc(bitonicSort(s));
    var allOk, _ := RunSeeds(pred, arb, "bitonicSort sorts ascending (n=8)");
    expect allOk, "bitonicSort output should be sorted ascending under every seed";
  }

  method {:test} TestPreservesMultisetFixed8()
  {
    var arb := FixedLenLists(8);
    var pred := (s: seq<int>) => (|s| == 0 || IsPow2(|s|)) ==> multiset(bitonicSort(s)) == multiset(s);
    var allOk, _ := RunSeeds(pred, arb, "bitonicSort preserves multiset (n=8)");
    expect allOk, "bitonicSort should be a permutation of its input under every seed";
  }

  method {:test} TestSortsAscendingMixedLengths()
  {
    var arb := Pow2LenLists();          // lengths 1..32 via FlatMap
    var pred := (s: seq<int>) => (|s| == 0 || IsPow2(|s|)) ==> sortedAsc(bitonicSort(s));
    var allOk, _ := RunSeeds(pred, arb, "bitonicSort sorts ascending (mixed 2^k lengths)");
    expect allOk, "bitonicSort output should be sorted at every power-of-two length, under every seed";
  }

  // Differential test: agrees with an independent reference sort (insertion sort).
  method {:test} TestAgreesWithInsertionSort()
  {
    var arb := FixedLenLists(8);
    var pred := (s: seq<int>) => (|s| == 0 || IsPow2(|s|)) ==> bitonicSort(s) == isort(s);
    var allOk, _ := RunSeeds(pred, arb, "bitonicSort == insertionSort (n=8)");
    expect allOk, "bitonicSort and the reference insertion sort should agree under every seed";
  }

  // ========================================================================
  // bitonicMerge only sorts *bitonic* inputs. Build them by sort+rotate (Map).
  // ========================================================================

  method {:test} TestMergeSortsBitonic()
  {
    var raw := FixedLenLists(8);
    var bitonicArb := raw.Map((s: seq<int>) => MakeBitonic(s));   // sort, then rotate
    var pred := (b: seq<int>) => (|b| == 0 || IsPow2(|b|)) ==> sortedAsc(bitonicMerge(b));
    var allOk, _ := RunSeeds(pred, bitonicArb, "bitonicMerge sorts bitonic inputs (n=8)");
    expect allOk, "bitonicMerge should sort a bitonic (sorted-then-rotated) sequence under every seed";
  }

  method {:test} TestMergePreservesMultiset()
  {
    var arb := FixedLenLists(8);        // multiset preservation holds for ANY input
    var pred := (s: seq<int>) => (|s| == 0 || IsPow2(|s|)) ==> multiset(bitonicMerge(s)) == multiset(s);
    var allOk, _ := RunSeeds(pred, arb, "bitonicMerge preserves multiset (n=8)");
    expect allOk, "bitonicMerge should be a permutation of its input under every seed";
  }

  // ========================================================================
  // Negative demo: bitonicMerge does NOT sort arbitrary (non-bitonic) inputs.
  // Expected to FAIL under EVERY seed — each should find a small counterexample.
  // ========================================================================

  method {:test} TestMergeDoesNotSortArbitrary()
  {
    var arb := FixedLenLists(4);        // length 4 — non-bitonic inputs exist (e.g. [1,0,1,0])
    var pred := (s: seq<int>) => (|s| == 0 || IsPow2(|s|)) ==> sortedAsc(bitonicMerge(s));
    var _, anyOk := RunSeeds(pred, arb, "bitonicMerge sorts ARBITRARY inputs (expected FAIL)");
    expect !anyOk, "bitonicMerge should NOT sort non-bitonic inputs — every seed should find a counterexample";
  }
}
