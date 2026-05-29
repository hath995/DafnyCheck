include "../../src/ExtendedArbitraries/Json.dfy"
include "../../src/RandomGenerator.dfy"

module ExtJsonTest {
  import opened Arbitrary
  import opened RandomGenerator
  import opened ExtJson

  method {:test} TestJson() {
    var arb := Json();
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var res := arb.Apply(tc);
    expect |res| >= 1;
    print "Json: ", res, "\n";
  }
}
