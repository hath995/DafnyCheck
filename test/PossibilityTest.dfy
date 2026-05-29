include "../src/Arbitrary.dfy"
include "../src/RandomGenerator.dfy"

module PossibilityTest {
    import opened Arbitrary
    import opened RandomGenerator
    import opened Std.Strings

    method {:test} TestBool()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var boolArb := Arbitrary<bool>.Bools();
        assert fresh(rng);
        assert fresh(tc);
        assert fresh(boolArb.internalFunction);
        assert (boolArb.internalFunction.Valid());
        assert tc.repr !! boolArb.internalFunction.repr;

        var res1 := boolArb.Apply(tc);
        var res2 := boolArb.Apply(tc);
        var res3 := boolArb.Apply(tc);
        var res4 := boolArb.Apply(tc);
        var res5 := boolArb.Apply(tc);
        print "\nres1, ", res1, "\n";
        print "res2, ", res2, "\n";
        print "res3, ", res3, "\n";
        print "res4, ", res4, "\n";
        print "res5, ", res5, "\n";
    }

    method {:test} TestOf()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var ofArb := Arbitrary<int>.Of([10, 20, 30, 40, 50]);

        var res1 := ofArb.Apply(tc);
        var res2 := ofArb.Apply(tc);
        var res3 := ofArb.Apply(tc);
        var res4 := ofArb.Apply(tc);
        var res5 := ofArb.Apply(tc);
        print "\nOf res1, ", res1, "\n";
        print "Of res2, ", res2, "\n";
        print "Of res3, ", res3, "\n";
        print "Of res4, ", res4, "\n";
        print "Of res5, ", res5, "\n";
    }

    method {:test} TestJust()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var justArb := Arbitrary<string>.Just("Hello World");

        var res1 := justArb.Apply(tc);
        var res2 := justArb.Apply(tc);
        var res3 := justArb.Apply(tc);
        var res4 := justArb.Apply(tc);
        var res5 := justArb.Apply(tc);
        print "\nJust res1, ", res1, "\n";
        print "Just res2, ", res2, "\n";
        print "Just res3, ", res3, "\n";
        print "Just res4, ", res4, "\n";
        print "Just res5, ", res5, "\n";
    }

    method {:test} TestRange()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var rangeArb := Arbitrary<int>.Range(5, 15);

        var res1 := rangeArb.Apply(tc);
        var res2 := rangeArb.Apply(tc);
        var res3 := rangeArb.Apply(tc);
        var res4 := rangeArb.Apply(tc);
        var res5 := rangeArb.Apply(tc);
        print "\nRange res1, ", res1, "\n";
        print "Range res2, ", res2, "\n";
        print "Range res3, ", res3, "\n";
        print "Range res4, ", res4, "\n";
        print "Range res5, ", res5, "\n";
    }

    method {:test} TestLists()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var elementArb := Arbitrary<int>.Range(1, 11); // Range 1-10 inclusive
        // assert fresh(elementArb.internalFunction);
        // assert fresh(elementArb.internalFunction.repr);
        var listsArb := Arbitrary<seq<int>>.Lists(elementArb, 1, 10); // Lists of 0-5 elements
        // assert listsArb.internalFunction.repr == {listsArb.internalFunction}+elementArb.internalFunction.repr;
        // assert fresh(listsArb.internalFunction.repr);

        var res1 := listsArb.Apply(tc);
        var res2 := listsArb.Apply(tc);
        var res3 := listsArb.Apply(tc);
        var res4 := listsArb.Apply(tc);
        var res5 := listsArb.Apply(tc);
        print "\nLists res1, ", res1, "\n";
        print "Lists res2, ", res2, "\n";
        print "Lists res3, ", res3, "\n";
        print "Lists res4, ", res4, "\n";
        print "Lists res5, ", res5, "\n";
    }

    method {:test} TestStrings()
    {
        var rng := XoroShift128Plus.fromSeed(420);
        var tc := new TestCase([], rng, 100, true);
        var stringsArb := Arbitrary<string>.Strings(0, 8, true); // ASCII strings of length 3-8

        var res1 := stringsArb.Apply(tc);
        var res2 := stringsArb.Apply(tc);
        var res3 := stringsArb.Apply(tc);
        var res4 := stringsArb.Apply(tc);
        var res5 := stringsArb.Apply(tc);
        print "\nStrings res1, ", res1, "\n";
        print "Strings res2, ", res2, "\n";
        print "Strings res3, ", res3, "\n";
        print "Strings res4, ", res4, "\n";
        print "Strings res5, ", res5, "\n";
    }

    method {:test} TestMapIntTransform()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var intArb := Arbitrary<int>.Range(1, 11); // Range 1-10 inclusive
        var mappedArb := intArb.Map<int>((x) => x * 2); // Double the values

        var res1 := mappedArb.Apply(tc);
        var res2 := mappedArb.Apply(tc);
        var res3 := mappedArb.Apply(tc);
        var res4 := mappedArb.Apply(tc);
        var res5 := mappedArb.Apply(tc);
        print "\nMap Int Transform res1, ", res1, "\n";
        print "Map Int Transform res2, ", res2, "\n";
        print "Map Int Transform res3, ", res3, "\n";
        print "Map Int Transform res4, ", res4, "\n";
        print "Map Int Transform res5, ", res5, "\n";
    }

    method {:test} TestMapStringTransform()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var stringArb := Arbitrary<string>.Strings(3, 8, true); // ASCII strings of length 3-8
        var mappedArb := stringArb.Map<string>((s) => s + "!"); // Add exclamation mark

        var res1 := mappedArb.Apply(tc);
        var res2 := mappedArb.Apply(tc);
        var res3 := mappedArb.Apply(tc);
        var res4 := mappedArb.Apply(tc);
        var res5 := mappedArb.Apply(tc);
        print "\nMap String Transform res1, ", res1, "\n";
        print "Map String Transform res2, ", res2, "\n";
        print "Map String Transform res3, ", res3, "\n";
        print "Map String Transform res4, ", res4, "\n";
        print "Map String Transform res5, ", res5, "\n";
    }

    method {:test} TestMapBoolTransform()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var boolArb := Arbitrary<bool>.Bools();
        var mappedArb := boolArb.Map<bool>((b) => !b); // Negate the boolean

        var res1 := mappedArb.Apply(tc);
        var res2 := mappedArb.Apply(tc);
        var res3 := mappedArb.Apply(tc);
        var res4 := mappedArb.Apply(tc);
        var res5 := mappedArb.Apply(tc);
        print "\nMap Bool Transform res1, ", res1, "\n";
        print "Map Bool Transform res2, ", res2, "\n";
        print "Map Bool Transform res3, ", res3, "\n";
        print "Map Bool Transform res4, ", res4, "\n";
        print "Map Bool Transform res5, ", res5, "\n";
    }

    method {:test} TestMapIntToString()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var intArb := Arbitrary<int>.Range(1, 6); // Range 1-5 inclusive
        var mappedArb := intArb.Map<string>((x) => "Number"+OfInt(x)); // Convert to constant string

        var res1 := mappedArb.Apply(tc);
        var res2 := mappedArb.Apply(tc);
        var res3 := mappedArb.Apply(tc);
        var res4 := mappedArb.Apply(tc);
        var res5 := mappedArb.Apply(tc);
        print "\nMap Int to String res1, ", res1, "\n";
        print "Map Int to String res2, ", res2, "\n";
        print "Map Int to String res3, ", res3, "\n";
        print "Map Int to String res4, ", res4, "\n";
        print "Map Int to String res5, ", res5, "\n";
    }

    method {:test} TestMapChaining()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var intArb := Arbitrary<int>.Range(1, 11); // Range 1-10 inclusive
        var step1 := intArb.Map<int>((x) => x * 2);  // Double the values
        var step2 := step1.Map<string>((x) => "Value: "+OfInt(x));  // Convert to string
        var mappedArb := step2.Map<string>((s) => s + "!");  // Add exclamation mark

        var res1 := mappedArb.Apply(tc);
        var res2 := mappedArb.Apply(tc);
        var res3 := mappedArb.Apply(tc);
        var res4 := mappedArb.Apply(tc);
        var res5 := mappedArb.Apply(tc);
        print "\nMap Chaining res1, ", res1, "\n";
        print "Map Chaining res2, ", res2, "\n";
        print "Map Chaining res3, ", res3, "\n";
        print "Map Chaining res4, ", res4, "\n";
        print "Map Chaining res5, ", res5, "\n";
    }

    method {:test} TestMapWithLists()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var elementArb := Arbitrary<int>.Range(1, 6); // Range 1-5 inclusive
        var listsArb := Arbitrary<seq<int>>.Lists(elementArb, 1, 5); // Lists of 1-5 elements
        var mappedArb := listsArb.Map<seq<string>>((list) => 
            seq<string>(|list|, (i) => "Item: "+OfInt(i))); // Convert each int to string

        var res1 := mappedArb.Apply(tc);
        var res2 := mappedArb.Apply(tc);
        var res3 := mappedArb.Apply(tc);
        var res4 := mappedArb.Apply(tc);
        var res5 := mappedArb.Apply(tc);
        print "\nMap With Lists res1, ", res1, "\n";
        print "Map With Lists res2, ", res2, "\n";
        print "Map With Lists res3, ", res3, "\n";
        print "Map With Lists res4, ", res4, "\n";
        print "Map With Lists res5, ", res5, "\n";
    }

    method {:test} TestTupleIntBool()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var intArb := Arbitrary<int>.Range(1, 6); // Range 1-5 inclusive
        var boolArb := Arbitrary<bool>.Bools();
        var tupleArb := Arbitrary<(int, bool)>.Tuple(intArb, boolArb);

        var res1 := tupleArb.Apply(tc);
        var res2 := tupleArb.Apply(tc);
        var res3 := tupleArb.Apply(tc);
        var res4 := tupleArb.Apply(tc);
        var res5 := tupleArb.Apply(tc);
        print "\nTuple Int Bool res1, ", res1, "\n";
        print "Tuple Int Bool res2, ", res2, "\n";
        print "Tuple Int Bool res3, ", res3, "\n";
        print "Tuple Int Bool res4, ", res4, "\n";
        print "Tuple Int Bool res5, ", res5, "\n";
    }

    method {:test} TestTupleStringInt()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var stringArb := Arbitrary<string>.Strings(3, 8, true); // ASCII strings of length 3-8
        var intArb := Arbitrary<int>.Range(10, 21); // Range 10-20 inclusive
        var tupleArb := Arbitrary<(string, int)>.Tuple(stringArb, intArb);

        var res1 := tupleArb.Apply(tc);
        var res2 := tupleArb.Apply(tc);
        var res3 := tupleArb.Apply(tc);
        var res4 := tupleArb.Apply(tc);
        var res5 := tupleArb.Apply(tc);
        print "\nTuple String Int res1, ", res1, "\n";
        print "Tuple String Int res2, ", res2, "\n";
        print "Tuple String Int res3, ", res3, "\n";
        print "Tuple String Int res4, ", res4, "\n";
        print "Tuple String Int res5, ", res5, "\n";
    }

    method {:test} TestTupleWithJust()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var justArb := Arbitrary<string>.Just("Hello");
        var intArb := Arbitrary<int>.Range(1, 4); // Range 1-3 inclusive
        var tupleArb := Arbitrary<(string, int)>.Tuple(justArb, intArb);

        var res1 := tupleArb.Apply(tc);
        var res2 := tupleArb.Apply(tc);
        var res3 := tupleArb.Apply(tc);
        var res4 := tupleArb.Apply(tc);
        var res5 := tupleArb.Apply(tc);
        print "\nTuple With Just res1, ", res1, "\n";
        print "Tuple With Just res2, ", res2, "\n";
        print "Tuple With Just res3, ", res3, "\n";
        print "Tuple With Just res4, ", res4, "\n";
        print "Tuple With Just res5, ", res5, "\n";
    }

    method {:test} TestTupleChaining()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var intArb := Arbitrary<int>.Range(1, 6); // Range 1-5 inclusive
        var boolArb := Arbitrary<bool>.Bools();
        var tupleArb := Arbitrary<(int, bool)>.Tuple(intArb, boolArb);
        var mappedArb := tupleArb.Map<string>((t: (int, bool)) => "Tuple: " + OfInt(t.0) + " " + (if t.1 then "true" else "false"));

        var res1 := mappedArb.Apply(tc);
        var res2 := mappedArb.Apply(tc);
        var res3 := mappedArb.Apply(tc);
        var res4 := mappedArb.Apply(tc);
        var res5 := mappedArb.Apply(tc);
        print "\nTuple Chaining res1, ", res1, "\n";
        print "Tuple Chaining res2, ", res2, "\n";
        print "Tuple Chaining res3, ", res3, "\n";
        print "Tuple Chaining res4, ", res4, "\n";
        print "Tuple Chaining res5, ", res5, "\n";
    }

    method {:test} TestMixInts()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var intArb1 := Arbitrary<int>.Range(1, 6); // Range 1-5 inclusive
        var intArb2 := Arbitrary<int>.Range(10, 16); // Range 10-15 inclusive
        var intArb3 := Arbitrary<int>.Range(20, 26); // Range 20-25 inclusive
        var mixes := [intArb1, intArb2, intArb3];
        assume {:axiom} forall x,y :: x in mixes && y in mixes ==> x.internalFunction.repr !! y.internalFunction.repr;
        var mixArb := Arbitrary<int>.Mix(mixes);

        var res1 := mixArb.Apply(tc);
        var res2 := mixArb.Apply(tc);
        var res3 := mixArb.Apply(tc);
        var res4 := mixArb.Apply(tc);
        var res5 := mixArb.Apply(tc);
        print "\nMix Ints res1, ", res1, "\n";
        print "Mix Ints res2, ", res2, "\n";
        print "Mix Ints res3, ", res3, "\n";
        print "Mix Ints res4, ", res4, "\n";
        print "Mix Ints res5, ", res5, "\n";
    }

    method {:test} TestMixStrings()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var stringArb1 := Arbitrary<string>.Just("Hello");
        var stringArb2 := Arbitrary<string>.Just("World");
        var stringArb3 := Arbitrary<string>.Just("Test");
        var stringArb4 := Arbitrary<string>.Strings(3, 8, true); // Random ASCII strings
        var mixes := [stringArb1, stringArb2, stringArb3, stringArb4];
        assume {:axiom} forall x,y :: x in mixes && y in mixes ==> x.internalFunction.repr !! y.internalFunction.repr;
        var mixArb := Arbitrary<string>.Mix(mixes);

        var res1 := mixArb.Apply(tc);
        var res2 := mixArb.Apply(tc);
        var res3 := mixArb.Apply(tc);
        var res4 := mixArb.Apply(tc);
        var res5 := mixArb.Apply(tc);
        print "\nMix Strings res1, ", res1, "\n";
        print "Mix Strings res2, ", res2, "\n";
        print "Mix Strings res3, ", res3, "\n";
        print "Mix Strings res4, ", res4, "\n";
        print "Mix Strings res5, ", res5, "\n";
    }

    method {:test} TestMixBools()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var boolArb1 := Arbitrary<bool>.Just(true);
        var boolArb2 := Arbitrary<bool>.Just(false);
        var boolArb3 := Arbitrary<bool>.Bools(); // Random booleans
        assert fresh(boolArb1.internalFunction.repr);
        assert fresh(boolArb2.internalFunction.repr);
        assert fresh(boolArb3.internalFunction.repr);
        var mixes := [boolArb1, boolArb2, boolArb3];
        assume {:axiom} forall x,y :: x in mixes && y in mixes ==> x.internalFunction.repr !! y.internalFunction.repr;
        var mixArb := Arbitrary<bool>.Mix(mixes);
        // assert fresh(mixArb.internalFunction.repr);

        var res1 := mixArb.Apply(tc);
        var res2 := mixArb.Apply(tc);
        var res3 := mixArb.Apply(tc);
        var res4 := mixArb.Apply(tc);
        var res5 := mixArb.Apply(tc);
        print "\nMix Bools res1, ", res1, "\n";
        print "Mix Bools res2, ", res2, "\n";
        print "Mix Bools res3, ", res3, "\n";
        print "Mix Bools res4, ", res4, "\n";
        print "Mix Bools res5, ", res5, "\n";
    }

    method {:test} TestMixWithOf()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var ofArb1 := Arbitrary<int>.Of([1, 2, 3]);
        var ofArb2 := Arbitrary<int>.Of([10, 20, 30]);
        var rangeArb := Arbitrary<int>.Range(100, 106); // Range 100-105 inclusive
        var mixes := [ofArb1, ofArb2, rangeArb];
        assume {:axiom} forall x,y :: x in mixes && y in mixes ==> x.internalFunction.repr !! y.internalFunction.repr;
        var mixArb := Arbitrary<int>.Mix(mixes);

        var res1 := mixArb.Apply(tc);
        var res2 := mixArb.Apply(tc);
        var res3 := mixArb.Apply(tc);
        var res4 := mixArb.Apply(tc);
        var res5 := mixArb.Apply(tc);
        print "\nMix With Of res1, ", res1, "\n";
        print "Mix With Of res2, ", res2, "\n";
        print "Mix With Of res3, ", res3, "\n";
        print "Mix With Of res4, ", res4, "\n";
        print "Mix With Of res5, ", res5, "\n";
    }

    method {:test} TestMixWithLists()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var elementArb1 := Arbitrary<int>.Range(1, 4); // Range 1-3 inclusive
        var elementArb2 := Arbitrary<int>.Range(10, 14); // Range 10-13 inclusive
        var listsArb1 := Arbitrary<seq<int>>.Lists(elementArb1, 1, 3);
        var listsArb2 := Arbitrary<seq<int>>.Lists(elementArb2, 2, 4);
        var mixes := [listsArb1, listsArb2];
        assume {:axiom} forall x,y :: x in mixes && y in mixes ==> x.internalFunction.repr !! y.internalFunction.repr;
        var mixArb := Arbitrary<seq<int>>.Mix(mixes);

        var res1 := mixArb.Apply(tc);
        var res2 := mixArb.Apply(tc);
        var res3 := mixArb.Apply(tc);
        var res4 := mixArb.Apply(tc);
        var res5 := mixArb.Apply(tc);
        print "\nMix With Lists res1, ", res1, "\n";
        print "Mix With Lists res2, ", res2, "\n";
        print "Mix With Lists res3, ", res3, "\n";
        print "Mix With Lists res4, ", res4, "\n";
        print "Mix With Lists res5, ", res5, "\n";
    }

    method {:test} TestMixChaining()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var intArb1 := Arbitrary<int>.Range(1, 4); // Range 1-3 inclusive
        var intArb2 := Arbitrary<int>.Range(10, 14); // Range 10-13 inclusive
        var mixes := [intArb1, intArb2];
        assume {:axiom} forall x,y :: x in mixes && y in mixes ==> x.internalFunction.repr !! y.internalFunction.repr;
        var mixArb := Arbitrary<int>.Mix(mixes);
        var mappedArb := mixArb.Map<string>((x) => "Mixed: " + OfInt(x));

        var res1 := mappedArb.Apply(tc);
        var res2 := mappedArb.Apply(tc);
        var res3 := mappedArb.Apply(tc);
        var res4 := mappedArb.Apply(tc);
        var res5 := mappedArb.Apply(tc);
        print "\nMix Chaining res1, ", res1, "\n";
        print "Mix Chaining res2, ", res2, "\n";
        print "Mix Chaining res3, ", res3, "\n";
        print "Mix Chaining res4, ", res4, "\n";
        print "Mix Chaining res5, ", res5, "\n";
    }

    method {:test} TestMixWithTuple()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var intArb := Arbitrary<int>.Range(1, 4); // Range 1-3 inclusive
        var boolArb := Arbitrary<bool>.Bools();
        var tupleArb1 := Arbitrary<(int, bool)>.Tuple(intArb, boolArb);
        var justTrueArb := Arbitrary<bool>.Just(true);
        var tupleArb2 := Arbitrary<(int, bool)>.Tuple(intArb, justTrueArb);
        var mixes := [tupleArb1, tupleArb2];
        assume {:axiom} forall x,y :: x in mixes && y in mixes ==> x.internalFunction.repr !! y.internalFunction.repr;
        var mixArb := Arbitrary<(int, bool)>.Mix(mixes);

        var res1 := mixArb.Apply(tc);
        var res2 := mixArb.Apply(tc);
        var res3 := mixArb.Apply(tc);
        var res4 := mixArb.Apply(tc);
        var res5 := mixArb.Apply(tc);
        print "\nMix With Tuple res1, ", res1, "\n";
        print "Mix With Tuple res2, ", res2, "\n";
        print "Mix With Tuple res3, ", res3, "\n";
        print "Mix With Tuple res4, ", res4, "\n";
        print "Mix With Tuple res5, ", res5, "\n";
    }

    method {:test} TestMixLargeSequence()
    {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var just1Arb := Arbitrary<int>.Just(1);
        var just2Arb := Arbitrary<int>.Just(2);
        var just3Arb := Arbitrary<int>.Just(3);
        var range1Arb := Arbitrary<int>.Range(10, 15);
        var range2Arb := Arbitrary<int>.Range(20, 25);
        var ofArb := Arbitrary<int>.Of([100, 200, 300]);
        var mixes := [just1Arb, just2Arb, just3Arb, range1Arb, range2Arb, ofArb];
        assume {:axiom} forall x,y :: x in mixes && y in mixes ==> x.internalFunction.repr !! y.internalFunction.repr;
        var mixArb := Arbitrary<int>.Mix(mixes);

        var res1 := mixArb.Apply(tc);
        var res2 := mixArb.Apply(tc);
        var res3 := mixArb.Apply(tc);
        var res4 := mixArb.Apply(tc);
        var res5 := mixArb.Apply(tc);
        print "\nMix Large Sequence res1, ", res1, "\n";
        print "Mix Large Sequence res2, ", res2, "\n";
        print "Mix Large Sequence res3, ", res3, "\n";
        print "Mix Large Sequence res4, ", res4, "\n";
        print "Mix Large Sequence res5, ", res5, "\n";
    }

    @AssumeCrossModuleTermination
    class PruferFlatMap extends FlatMapFn<int, (int, seq<int>)>
    {
       constructor() 
        ensures fresh(this)
       {}

        method CreateArbitrary(t: int) returns (p: Arbitrary<(int, seq<int>)>)
            ensures p.Valid()
            ensures fresh(p.internalFunction.repr)
       {
            expect {:axiom } 0 < t < MaxLong;
            var range := Arbitrary<int>.Range(0, t);
            var pruferSequence := Arbitrary<int>.Lists(range, t, t);
            var length := Arbitrary<int>.Just(t);
            p := Arbitrary<(int, seq<int>)>.Tuple(length, pruferSequence);
       }
    }
    method {:test} TestFlatMap() {
        var rng := XoroShift128Plus.fromSeed(42);
        var tc := new TestCase([], rng, 100, true);
        var range1Arb := Arbitrary<int>.Range(1, 25);
        assert fresh(range1Arb.internalFunction.repr);
        var pfm := new PruferFlatMap();
        var pruferSequenceArb := range1Arb.FlatMap(pfm);
        var res1 := pruferSequenceArb.Apply(tc);
        var res2 := pruferSequenceArb.Apply(tc);
        var res3 := pruferSequenceArb.Apply(tc);
        var res4 := pruferSequenceArb.Apply(tc);
        var res5 := pruferSequenceArb.Apply(tc);
        print "Prufer seq res1, ", res1, "\n";
        print "Prufer seq res2, ", res2, "\n";
        print "Prufer seq res3, ", res3, "\n";
        print "Prufer seq res4, ", res4, "\n";
        print "Prufer seq res5, ", res5, "\n";

    }

}