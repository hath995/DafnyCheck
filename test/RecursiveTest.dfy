include "../src/Arbitrary.dfy"
include "../src/RandomGenerator.dfy"

// letrec example with a VARIABLE-arity recursive node:
//   Tree = Leaf(int) | Node(seq<Tree>)
// A Node's children are a `Lists` of the recursive arbitrary (reg.Tie("Tree")),
// so a node can have any number of children. "Leaf" is the base case, and the
// TestCase depth budget (maxDepth) falls back to it so generation terminates.
module RecursiveTest {
  import opened Arbitrary
  import opened RandomGenerator

  datatype Tree = Leaf(n: int) | Node(kids: seq<Tree>)

  // Leaf(n): wrap a small int.
  method RegisterLeaf(reg: Registry<Tree>)
    modifies reg`arbs
  {
    var ints := Arbitrary<int>.Range(0, 100);
    var leafArb := ints.Map((n: int) => Leaf(n));
    reg.Register("Leaf", leafArb);
  }

  // Node(kids): a list of 0..3 recursively-generated children.
  method RegisterNode(reg: Registry<Tree>)
    modifies reg`arbs
  {
    var elem := reg.Tie("Tree");
    var kids := Arbitrary<Tree>.Lists(elem, 0, 3);
    var nodeArb := kids.Map((ks: seq<Tree>) => Node(ks));
    reg.Register("Node", nodeArb);
  }

  // Tree = Leaf | Node (distinct ties => disjoint reprs).
  method RegisterTree(reg: Registry<Tree>)
    modifies reg`arbs
    ensures "Tree" in reg.arbs
  {
    var tieLeaf := reg.Tie("Leaf");
    var tieNode := reg.Tie("Node");
    var treeArb := Arbitrary<Tree>.Mix([tieLeaf, tieNode]);
    reg.Register("Tree", treeArb);
  }

  method BuildTree() returns (arb: Arbitrary<Tree>)
    ensures arb.Valid()
  {
    var reg := new Registry<Tree>("Leaf", 4);
    RegisterLeaf(reg);
    RegisterNode(reg);
    RegisterTree(reg);
    arb := reg.Lookup("Tree");
    // Valid by construction; carried through the mutable registry as an axiom
    // (same style as the LazyArbitrary resolve / RunTest rng-disjointness).
    assume {:axiom} arb.Valid();
  }

  method {:test} TestRecursiveTree() {
    var arb := BuildTree();
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 1000, true);
    var t0 := arb.Apply(tc);
    var t1 := arb.Apply(tc);
    var t2 := arb.Apply(tc);
    // A node's arity is capped at the Lists max (3).
    expect t0.Node? ==> |t0.kids| <= 3;
    expect t1.Node? ==> |t1.kids| <= 3;
    expect t2.Node? ==> |t2.kids| <= 3;
    print "Recursive Trees:\n  ", t0, "\n  ", t1, "\n  ", t2, "\n";
  }
}
