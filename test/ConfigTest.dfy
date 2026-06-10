include "../src/DafnyCheck.dfy"

// Exercises RunConfig: seed, run count, verbosity, classifier statistics, and
// always-tested examples, plus the boolean pass/fail return value.
module ConfigTest {
  import opened DafnyCheck
  import opened Arbitraries
  import opened RunConfigs
  import opened Std.Wrappers

  method {:test} TestConfigSeedAndClassifier() {
    var arb := Arbitrary<int>.Range(0, 100);
    // Always-true predicate over the generator's own range => the run passes.
    var cfg := DefaultConfig<int>()
      .(seed := Some(123), numRuns := 50, verbosity := Medium,
        classifier := Some((n: int) => if n < 50 then "low" else "high"));
    var passed := RunTestWithConfig((n: int) => 0 <= n < 100, arb, "config-demo", cfg);
    expect passed;
  }

  method {:test} TestExamplesAlwaysRun() {
    var arb := Arbitrary<int>.Range(0, 100);
    // A supplied example outside the predicate's domain must force a failure,
    // independent of what random generation produces.
    var cfg := DefaultConfig<int>().(examples := [200], verbosity := Off);
    var passed := RunTestWithConfig((n: int) => 0 <= n < 100, arb, "examples-demo", cfg);
    expect !passed;
  }

  method {:test} TestHighVerbosityTrace() {
    // A failing predicate so generation finds a counterexample and then shrinks.
    // At Verbosity.High the run traces every generated value + choice sequence and
    // every accepted shrink step before the final counterexample.
    var arb := Arbitrary<int>.Range(0, 1000);
    var cfg := DefaultConfig<int>().(seed := Some(1), numRuns := 20, verbosity := High, useColor := false);
    var passed := RunTestWithConfig((n: int) => n < 500, arb, "n < 500 (high verbosity)", cfg);
    expect !passed;
  }
}
