include "../../src/ExtendedArbitraries/Network.dfy"
include "../../src/RandomGenerator.dfy"

module ExtNetworkTest {
  import opened Arbitraries
  import opened RandomGenerator
  import opened ExtNetwork

  method {:test} TestIPv4() {
    var arb := IPv4();
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var res := arb.Apply(tc);
    expect '.' in res;
    print "IPv4: ", res, "\n";
  }

  method {:test} TestIPv6() {
    var arb := IPv6();
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var res := arb.Apply(tc);
    expect ':' in res;
    print "IPv6: ", res, "\n";
  }
}
