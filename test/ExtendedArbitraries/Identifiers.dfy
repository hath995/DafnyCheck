include "../../src/ExtendedArbitraries/Identifiers.dfy"
include "../../src/RandomGenerator.dfy"

module ExtIdentifiersTest {
  import opened Arbitraries
  import opened RandomGenerator
  import opened ExtIdentifiers

  method {:test} TestUUID() {
    var arb := UUID();
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var res_o := arb.Apply(tc); expect res_o.Some?; var res := res_o.value;
    // 8-4-4-4-12 layout: 32 hex digits + 4 dashes = 36 chars, dashes fixed.
    expect |res| == 36;
    expect res[8] == '-' && res[13] == '-' && res[18] == '-' && res[23] == '-';
    print "UUID: ", res, "\n";
  }

  method {:test} TestULID() {
    var arb := ULID();
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var res_o := arb.Apply(tc); expect res_o.Some?; var res := res_o.value;
    expect |res| == 26;
    print "ULID: ", res, "\n";
  }
}
