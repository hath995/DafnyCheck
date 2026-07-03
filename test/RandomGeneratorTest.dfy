include "../src/RandomGenerator.dfy"

// Smoke test for the PRNG, extracted from src/RandomGenerator.dfy (test methods
// live under test/, not in the library source). Run with:
//   dafny test ../src/RandomGenerator.dfy RandomGeneratorTest.dfy --standard-libraries --allow-warnings
module RandomGeneratorTest {
  import opened RandomGenerator

  method {:test} reals() {
    var test := XoroShift128Plus.fromSeed(42);
    var te, re := test.nextReal();
    print(te);
    print("\n");
    print(te < 0.9);
    print("\n");
  }
}
