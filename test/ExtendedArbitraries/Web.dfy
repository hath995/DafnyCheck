include "../../src/ExtendedArbitraries/Web.dfy"
include "../../src/RandomGenerator.dfy"

module ExtWebTest {
  import opened Arbitraries
  import opened RandomGenerator
  import opened ExtWeb

  method {:test} TestDomain() {
    var arb := Domain();
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var res := arb.Apply(tc);
    expect '.' in res;
    print "Domain: ", res, "\n";
  }

  method {:test} TestEmail() {
    var arb := Email();
    var rng := XoroShift128Plus.fromSeed(42);
    var tc := new TestCase([], rng, 100, true);
    var res := arb.Apply(tc);
    expect '@' in res;
    print "Email: ", res, "\n";
  }
}
