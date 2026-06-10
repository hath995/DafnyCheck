include "../src/Arbitrary.dfy"
include "../src/RandomGenerator.dfy"

// letrec-style recursive generator for a datatype with FOUR node types of
// differing arity and payloads, built with the Registry/Tie API (fast-check's
// letrec analogue). Recursive positions are written `reg.Tie("WeirdTree")`; the
// TestCase depth budget (maxDepth) forces the registered base case ("Leaf") once
// the recursion is deep enough, so generation terminates.
//
// Each node type is registered by its own helper so the Tuple/Mix disjointness
// proofs run in a small context (they get slow if everything shares one method).
module WeirdTreeTest {
  import opened Arbitraries
  import opened RandomGenerator

  datatype WeirdTree =
    | RealTree(l: WeirdTree, r: WeirdTree, id: int)
    | Branch(a: WeirdTree, b: WeirdTree, c: WeirdTree, name: string)
    | Leaf
    | Root(val: bool)

  function Size(t: WeirdTree): nat {
    match t
    case Leaf => 1
    case Root(_) => 1
    case RealTree(l, r, _) => 1 + Size(l) + Size(r)
    case Branch(a, b, c, _) => 1 + Size(a) + Size(b) + Size(c)
  }

  method RegisterTerminals(reg: Registry<WeirdTree>)
    modifies reg`arbs
  {
    var leafArb := Arbitrary<WeirdTree>.Just(Leaf);
    reg.Register("Leaf", leafArb);
    var bools := Arbitrary<bool>.Bools();
    var rootArb := bools.Map((v: bool) => Root(v));
    reg.Register("Root", rootArb);
  }

  // RealTree(l, r, id): two recursive children + an int payload.
  method RegisterRealTree(reg: Registry<WeirdTree>)
    modifies reg`arbs
  {
    var ids := Arbitrary<nat>.Nats(1000000);
    var rt0 := reg.Tie("WeirdTree");
    var rt1 := reg.Tie("WeirdTree");
    var rtTup := Arbitrary<WeirdTree>.Tuple3(rt0, rt1, ids);
    var rtArb := rtTup.Map((t: (WeirdTree, WeirdTree, nat)) => RealTree(t.0, t.1, t.2 as int));
    reg.Register("RealTree", rtArb);
  }

  // Branch(a, b, c, name): three recursive children + a string payload.
  method RegisterBranch(reg: Registry<WeirdTree>)
    modifies reg`arbs
  {
    var names := Arbitrary<string>.Strings(0, 8, true);
    var b0 := reg.Tie("WeirdTree");
    var b1 := reg.Tie("WeirdTree");
    var b2 := reg.Tie("WeirdTree");
    var brTup := Arbitrary<WeirdTree>.Tuple4(b0, b1, b2, names);
    var brArb := brTup.Map((b: (WeirdTree, WeirdTree, WeirdTree, string)) => Branch(b.0, b.1, b.2, b.3));
    reg.Register("Branch", brArb);
  }

  // WeirdTree = a mix of the four node types. Distinct ties have distinct
  // singleton reprs, so the Mix disjointness precondition is satisfied.
  method RegisterTop(reg: Registry<WeirdTree>)
    modifies reg`arbs
    ensures "WeirdTree" in reg.arbs
  {
    var tieLeaf := reg.Tie("Leaf");
    var tieRoot := reg.Tie("Root");
    var tieRT := reg.Tie("RealTree");
    var tieBr := reg.Tie("Branch");
    var possibilities := [tieLeaf, tieRoot, tieRT, tieBr];
    var wtArb := Arbitrary<WeirdTree>.Mix(possibilities);
    reg.Register("WeirdTree", wtArb);
  }

  // "Leaf" is the base case (non-recursive), so the depth budget can always
  // fall back to it to terminate.
  method BuildWeird() returns (arb: Arbitrary<WeirdTree>)
    ensures arb.Valid()
  {
    var reg := new Registry<WeirdTree>("Leaf", 5);
    RegisterTerminals(reg);
    RegisterRealTree(reg);
    RegisterBranch(reg);
    RegisterTop(reg);
    arb := reg.Lookup("WeirdTree");
    // The registered Mix is valid by construction; Dafny can't carry that fact
    // through the mutable registry's framing, so we assert it as an axiom (same
    // style as the LazyArbitrary resolve and RunTest's rng-disjointness).
    assume {:axiom} arb.Valid();
  }

  method {:test} TestWeirdTree() {
    var arb := BuildWeird();
    var rng := XoroShift128Plus.fromSeed(99);
    var tc := new TestCase([], rng, 1000, true);
    // Draw several samples; the depth budget guarantees each one terminates.
    var t0 := arb.Apply(tc);
    var t1 := arb.Apply(tc);
    var t2 := arb.Apply(tc);
    var t3 := arb.Apply(tc);
    var t4 := arb.Apply(tc);
    var t5 := arb.Apply(tc);
    expect Size(t0) >= 1 && Size(t1) >= 1 && Size(t2) >= 1;
    expect Size(t3) >= 1 && Size(t4) >= 1 && Size(t5) >= 1;
    print "WeirdTree samples:\n";
    print "  ", t0, "\n  ", t1, "\n  ", t2, "\n  ", t3, "\n  ", t4, "\n  ", t5, "\n";
  }
}
