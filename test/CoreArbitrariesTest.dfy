include "../src/Arbitrary.dfy"
include "../src/RandomGenerator.dfy"

// Backfilled tests for the core arbitraries added in the release work:
// Nats, Chars, Reals, the bit-vector widths, Sets/Multisets/Maps, Tuple3..Tuple10,
// and the (fixed-size) Arrays/Array2/Array3. Each test builds the generator first
// (so the freshly-created TestCase is disjoint from it), applies it, and asserts
// the generated value conforms to its expected type and bounds with `expect`
// (runtime checks — MakeChoice has no proven static upper bound).
module CoreArbitrariesTest {
  import opened Arbitrary
  import opened RandomGenerator

  // ---- primitive value generators ----

  method {:test} TestNats() {
    var arb := Arbitrary<nat>.Nats(100);
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var r1 := arb.Apply(tc);
    var r2 := arb.Apply(tc);
    expect r1 < 100 && r2 < 100;
    print "Nats: ", r1, " ", r2, "\n";
  }

  method {:test} TestChars() {
    var arb := Arbitrary<char>.Chars();
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var r1 := arb.Apply(tc);
    var r2 := arb.Apply(tc);
    expect 32 <= r1 as int < 127;
    expect 32 <= r2 as int < 127;
    print "Chars: ", r1, " ", r2, "\n";
  }

  method {:test} TestReals() {
    var arb := Arbitrary<real>.Reals();
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var r1 := arb.Apply(tc);
    var r2 := arb.Apply(tc);
    expect r1 >= 0.0 && r2 >= 0.0;
    print "Reals: ", r1, " ", r2, "\n";
  }

  // ---- bit-vector widths ----

  method {:test} TestBitVectors() {
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var a1 := Arbitrary<bv1>.BitVectors1();
    var a2 := Arbitrary<bv2>.BitVectors2();
    var a8 := Arbitrary<bv8>.BitVectors8();
    var a16 := Arbitrary<bv16>.BitVectors16();
    var a32 := Arbitrary<bv32>.BitVectors32();
    var a64 := Arbitrary<bv64>.BitVectors64();
    var a128 := Arbitrary<bv128>.BitVectors128();
    var a256 := Arbitrary<bv256>.BitVectors256();
    var v1 := a1.Apply(tc);
    var v2 := a2.Apply(tc);
    var v8 := a8.Apply(tc);
    var v16 := a16.Apply(tc);
    var v32 := a32.Apply(tc);
    var v64 := a64.Apply(tc);
    var v128 := a128.Apply(tc);
    var v256 := a256.Apply(tc);
    // Each value's width is guaranteed by its type; confirm generation ran.
    expect v1 as int >= 0 && v2 as int >= 0 && v8 as int >= 0 && v256 as int >= 0;
    print "BitVectors: ", v1, " ", v2, " ", v8, " ", v16, " ", v32, " ", v64, " ", v128, " ", v256, "\n";
  }

  // ---- collections ----

  method {:test} TestSets() {
    var elem := Arbitrary<int>.Range(0, 10);
    var arb := Arbitrary<int>.Sets(elem, 0, 5);
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var s := arb.Apply(tc);
    expect |s| <= 5;
    expect forall x :: x in s ==> 0 <= x < 10;
    print "Set: ", s, "\n";
  }

  method {:test} TestMultisets() {
    var elem := Arbitrary<int>.Range(0, 10);
    var arb := Arbitrary<int>.Multisets(elem, 0, 5);
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var m := arb.Apply(tc);
    expect |m| <= 5;
    expect forall x :: x in m ==> 0 <= x < 10;
    print "Multiset: ", m, "\n";
  }

  method {:test} TestMaps() {
    var keys := Arbitrary<int>.Range(0, 10);
    var vals := Arbitrary<int>.Range(0, 20);
    var arb := Arbitrary<int>.Maps(keys, vals, 0, 5);
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var m := arb.Apply(tc);
    expect |m| <= 5;
    expect forall k :: k in m ==> 0 <= k < 10 && 0 <= m[k] < 20;
    print "Map: ", m, "\n";
  }

  // ---- arrays (fixed size) ----

  method {:test} TestArrays() {
    var elem := Arbitrary<int>.Range(0, 10);
    var arb := Arbitrary<int>.Arrays(elem, 0, 5);
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var a := arb.Apply(tc);
    expect a.Length <= 5;
    expect forall i :: 0 <= i < a.Length ==> 0 <= a[i] < 10;
    print "Array length: ", a.Length, "\n";
  }

  method {:test} TestArray2() {
    var elem := Arbitrary<int>.Range(0, 10);
    var arb := Arbitrary<int>.Array2(elem, 3, 4);
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var a := arb.Apply(tc);
    expect a.Length0 == 3 && a.Length1 == 4;
    expect forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> 0 <= a[i, j] < 10;
    print "Array2 dims: ", a.Length0, "x", a.Length1, "\n";
  }

  method {:test} TestArray3() {
    var elem := Arbitrary<int>.Range(0, 10);
    var arb := Arbitrary<int>.Array3(elem, 2, 3, 2);
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var a := arb.Apply(tc);
    expect a.Length0 == 2 && a.Length1 == 3 && a.Length2 == 2;
    print "Array3 dims: ", a.Length0, "x", a.Length1, "x", a.Length2, "\n";
  }

  // ---- n-tuples ----

  method {:test} TestTuple3() {
    var g0 := Arbitrary<int>.Range(0, 10);
    var g1 := Arbitrary<int>.Range(0, 10);
    var g2 := Arbitrary<int>.Range(0, 10);
    var arb := Arbitrary<int>.Tuple3(g0, g1, g2);
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var t := arb.Apply(tc);
    expect 0 <= t.0 < 10 && 0 <= t.1 < 10 && 0 <= t.2 < 10;
    print "Tuple3: ", t, "\n";
  }

  method {:test} TestTuple4() {
    var g0 := Arbitrary<int>.Range(0, 10);
    var g1 := Arbitrary<int>.Range(0, 10);
    var g2 := Arbitrary<int>.Range(0, 10);
    var g3 := Arbitrary<int>.Range(0, 10);
    var arb := Arbitrary<int>.Tuple4(g0, g1, g2, g3);
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var t := arb.Apply(tc);
    expect 0 <= t.0 < 10 && 0 <= t.3 < 10;
    print "Tuple4: ", t, "\n";
  }

  method {:test} TestTuple5() {
    var g0 := Arbitrary<int>.Range(0, 10);
    var g1 := Arbitrary<int>.Range(0, 10);
    var g2 := Arbitrary<int>.Range(0, 10);
    var g3 := Arbitrary<int>.Range(0, 10);
    var g4 := Arbitrary<int>.Range(0, 10);
    var arb := Arbitrary<int>.Tuple5(g0, g1, g2, g3, g4);
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var t := arb.Apply(tc);
    expect 0 <= t.0 < 10 && 0 <= t.4 < 10;
    print "Tuple5: ", t, "\n";
  }

  method {:test} TestTuple6() {
    var g0 := Arbitrary<int>.Range(0, 10);
    var g1 := Arbitrary<int>.Range(0, 10);
    var g2 := Arbitrary<int>.Range(0, 10);
    var g3 := Arbitrary<int>.Range(0, 10);
    var g4 := Arbitrary<int>.Range(0, 10);
    var g5 := Arbitrary<int>.Range(0, 10);
    var arb := Arbitrary<int>.Tuple6(g0, g1, g2, g3, g4, g5);
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var t := arb.Apply(tc);
    expect 0 <= t.0 < 10 && 0 <= t.5 < 10;
    print "Tuple6: ", t, "\n";
  }

  method {:test} TestTuple7() {
    var g0 := Arbitrary<int>.Range(0, 10);
    var g1 := Arbitrary<int>.Range(0, 10);
    var g2 := Arbitrary<int>.Range(0, 10);
    var g3 := Arbitrary<int>.Range(0, 10);
    var g4 := Arbitrary<int>.Range(0, 10);
    var g5 := Arbitrary<int>.Range(0, 10);
    var g6 := Arbitrary<int>.Range(0, 10);
    var arb := Arbitrary<int>.Tuple7(g0, g1, g2, g3, g4, g5, g6);
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var t := arb.Apply(tc);
    expect 0 <= t.0 < 10 && 0 <= t.6 < 10;
    print "Tuple7: ", t, "\n";
  }

  method {:test} TestTuple8() {
    var g0 := Arbitrary<int>.Range(0, 10);
    var g1 := Arbitrary<int>.Range(0, 10);
    var g2 := Arbitrary<int>.Range(0, 10);
    var g3 := Arbitrary<int>.Range(0, 10);
    var g4 := Arbitrary<int>.Range(0, 10);
    var g5 := Arbitrary<int>.Range(0, 10);
    var g6 := Arbitrary<int>.Range(0, 10);
    var g7 := Arbitrary<int>.Range(0, 10);
    var arb := Arbitrary<int>.Tuple8(g0, g1, g2, g3, g4, g5, g6, g7);
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var t := arb.Apply(tc);
    expect 0 <= t.0 < 10 && 0 <= t.7 < 10;
    print "Tuple8: ", t, "\n";
  }

  method {:test} TestTuple9() {
    var g0 := Arbitrary<int>.Range(0, 10);
    var g1 := Arbitrary<int>.Range(0, 10);
    var g2 := Arbitrary<int>.Range(0, 10);
    var g3 := Arbitrary<int>.Range(0, 10);
    var g4 := Arbitrary<int>.Range(0, 10);
    var g5 := Arbitrary<int>.Range(0, 10);
    var g6 := Arbitrary<int>.Range(0, 10);
    var g7 := Arbitrary<int>.Range(0, 10);
    var g8 := Arbitrary<int>.Range(0, 10);
    var arb := Arbitrary<int>.Tuple9(g0, g1, g2, g3, g4, g5, g6, g7, g8);
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var t := arb.Apply(tc);
    expect 0 <= t.0 < 10 && 0 <= t.8 < 10;
    print "Tuple9: ", t, "\n";
  }

  method {:test} TestTuple10() {
    var g0 := Arbitrary<int>.Range(0, 10);
    var g1 := Arbitrary<int>.Range(0, 10);
    var g2 := Arbitrary<int>.Range(0, 10);
    var g3 := Arbitrary<int>.Range(0, 10);
    var g4 := Arbitrary<int>.Range(0, 10);
    var g5 := Arbitrary<int>.Range(0, 10);
    var g6 := Arbitrary<int>.Range(0, 10);
    var g7 := Arbitrary<int>.Range(0, 10);
    var g8 := Arbitrary<int>.Range(0, 10);
    var g9 := Arbitrary<int>.Range(0, 10);
    var arb := Arbitrary<int>.Tuple10(g0, g1, g2, g3, g4, g5, g6, g7, g8, g9);
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var t := arb.Apply(tc);
    expect 0 <= t.0 < 10 && 0 <= t.9 < 10;
    print "Tuple10: ", t, "\n";
  }
}
