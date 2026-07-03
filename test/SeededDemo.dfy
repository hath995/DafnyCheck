include "../src/SeedSource/SeededTesting.dfy"

// Demonstrates the random-seeded runner end to end. Run it (twice) from this
// test/ directory with a native file to see a different fresh seed each run, e.g.:
//   dafny run --target:cs SeededDemo.dfy --input ../src/SeedSource/SeedSource.cs
//
// Main is in the default module (see SeedSourceDemo.dfy for why, re: Java).
import opened SeedSource
import opened SeededTesting
import opened Arbitraries

method Main() {
  var s := GetSeed();
  print "fresh seed = ", s, "\n";
  var arb := Arbitrary<int>.Range(0, 1000);
  var pred := (n: int) => 0 <= n < 1000;        // a true property
  var ok := RunTestRandom(pred, arb, "0 <= n < 1000 (random seed)");
  print "passed = ", ok, "\n";
}
