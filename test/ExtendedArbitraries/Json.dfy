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
    var r0_o := arb.Apply(tc); expect r0_o.Some?; var r0 := r0_o.value;
    var r1_o := arb.Apply(tc); expect r1_o.Some?; var r1 := r1_o.value;
    var r2_o := arb.Apply(tc); expect r2_o.Some?; var r2 := r2_o.value;
    var r3_o := arb.Apply(tc); expect r3_o.Some?; var r3 := r3_o.value;
    var r4_o := arb.Apply(tc); expect r4_o.Some?; var r4 := r4_o.value;
    var r5_o := arb.Apply(tc); expect r5_o.Some?; var r5 := r5_o.value;
    var r6_o := arb.Apply(tc); expect r6_o.Some?; var r6 := r6_o.value;
    var r7_o := arb.Apply(tc); expect r7_o.Some?; var r7 := r7_o.value;
    expect |r0| >= 1 && |r1| >= 1 && |r2| >= 1 && |r3| >= 1;
    expect |r4| >= 1 && |r5| >= 1 && |r6| >= 1 && |r7| >= 1;
    print "JSON samples:\n  ", r0, "\n  ", r1, "\n  ", r2, "\n  ", r3, "\n";
    print "  ", r4, "\n  ", r5, "\n  ", r6, "\n  ", r7, "\n";
  }
}
