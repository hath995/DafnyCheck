include "../../src/ExtendedArbitraries/Json.dfy"
include "../../src/RandomGenerator.dfy"

module ExtJsonTest {
  import opened Arbitraries
  import opened RandomGenerator
  import opened ExtJson

  method {:test} TestJson() {
    var arb := Json();
    var rng := XoroShift128Plus.fromSeed(123);
    var tc := new TestCase([], rng, 2000, true);
    // Several samples; the depth budget guarantees each recursive value terminates.
    var r0 := arb.Apply(tc);
    var r1 := arb.Apply(tc);
    var r2 := arb.Apply(tc);
    var r3 := arb.Apply(tc);
    var r4 := arb.Apply(tc);
    var r5 := arb.Apply(tc);
    var r6 := arb.Apply(tc);
    var r7 := arb.Apply(tc);
    expect |r0| >= 1 && |r1| >= 1 && |r2| >= 1 && |r3| >= 1;
    expect |r4| >= 1 && |r5| >= 1 && |r6| >= 1 && |r7| >= 1;
    print "JSON samples:\n  ", r0, "\n  ", r1, "\n  ", r2, "\n  ", r3, "\n";
    print "  ", r4, "\n  ", r5, "\n  ", r6, "\n  ", r7, "\n";
  }
}
