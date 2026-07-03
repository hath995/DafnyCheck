include "../DafnyCheck.dfy"
include "./SeedSource.dfy"

// ============================================================================
// SeededTesting — property-based test runners seeded from a *fresh* platform
// random value each run, via SeedSource.GetSeed().
//
// This is deliberately a SEPARATE module rather than baked into DafnyCheck:
// GetSeed is an `{:extern}`, so any module that references it forces the native
// SeedSource file (SeedSource.cs / .py / …) to be supplied at compile time for
// every consumer. Keeping it here means only tests that *opt in* to random
// seeding need a native file; plain DafnyCheck.RunTest stays extern-free and the
// rest of the suite compiles/runs with no extra inputs.
//
// Compile/run a test that uses these with the matching native file, e.g.
//   dafny test --target:cs MyTest.dfy --input src/SeedSource/SeedSource.cs
// ============================================================================
module SeededTesting {
  import opened DafnyCheck
  import opened Arbitraries
  import opened RunConfigs
  import opened Std.Wrappers
  import opened SeedSource

  // Platform-backed monotonic clock: the concrete Clock the seeded runners inject
  // so runs are timed out of the box. It lives here — not in the core — because
  // Now() calls the SeedSource.NowNanos extern, which forces a native file at
  // compile time for every consumer. Keeping it in SeededTesting means only tests
  // that opt into seeded/timed runs need that file; plain DafnyCheck stays
  // extern-free. NowNanos returns a bv64; we widen it to nat for the Clock API.
  class SystemClock extends Clock {
    constructor()
      ensures fresh(this)
    {}

    method Now() returns (t: nat)
    {
      var n := NowNanos();
      t := n as nat;
    }
  }

  // Like RunTest, but draws a fresh random seed for this run and times it.
  method RunTestRandom<T(!new)>(pred: T -> bool, arb: Arbitrary<T>, name: string)
    returns (passed: bool)
    requires arb.Valid()
  {
    var seed := GetSeed();
    var clk := new SystemClock();
    passed := RunTestWithConfig(pred, arb, name,
                                DefaultConfig<T>().(seed := Some(seed), clock := Some(clk)));
  }

  // Like RunTestWithExamples, but with a fresh random seed and timing.
  method RunTestRandomWithExamples<T(!new)>(pred: T -> bool, arb: Arbitrary<T>, name: string, examples: nat)
    returns (passed: bool)
    requires arb.Valid()
    requires 0 < examples
  {
    var seed := GetSeed();
    var clk := new SystemClock();
    passed := RunTestWithConfig(pred, arb, name,
                                DefaultConfig<T>().(seed := Some(seed), numRuns := examples, clock := Some(clk)));
  }

  // Like RunTestWithConfig, but fills any unset field with a fresh default: a
  // random seed if seed is None, and a SystemClock if clock is None. An explicit
  // seed (reproducible) or an explicit/absent clock choice is respected.
  method RunTestRandomWithConfig<T(!new)>(pred: T -> bool, arb: Arbitrary<T>, name: string, cfg: RunConfig<T>)
    returns (passed: bool)
    requires arb.Valid()
  {
    var cfg' := cfg;
    if cfg'.seed.None? {
      var seed := GetSeed();
      cfg' := cfg'.(seed := Some(seed));
    }
    if cfg'.clock.None? {
      var clk := new SystemClock();
      cfg' := cfg'.(clock := Some(clk));
    }
    passed := RunTestWithConfig(pred, arb, name, cfg');
  }

  // ──────────────────────────────────────────────────────────────────────────
  // Seeded *method*-test runners — siblings of the predicate runners above, for
  // testing heap-mutating methods wrapped in a MethodUnderTest. Each draws a
  // fresh seed from SeedSource.GetSeed() and delegates to RunMethodTestWithConfig.
  // ──────────────────────────────────────────────────────────────────────────

  // Like RunMethodTest, but draws a fresh random seed for this run and times it.
  method RunMethodTestRandom<Input(!new), E(==)>(arb: Arbitrary<Input>, sut: MethodUnderTest<Input, E>, name: string)
    returns (passed: bool)
    requires arb.Valid()
    requires sut.Valid()
  {
    var seed := GetSeed();
    var clk := new SystemClock();
    passed := RunMethodTestWithConfig(arb, sut, name,
                                      DefaultConfig<Input>().(seed := Some(seed), clock := Some(clk)));
  }

  // Like RunMethodTestWithExamples, but with a fresh random seed and timing.
  method RunMethodTestRandomWithExamples<Input(!new), E(==)>(
      arb: Arbitrary<Input>, sut: MethodUnderTest<Input, E>, name: string, examples: nat)
    returns (passed: bool)
    requires arb.Valid()
    requires sut.Valid()
    requires 0 < examples
  {
    var seed := GetSeed();
    var clk := new SystemClock();
    passed := RunMethodTestWithConfig(arb, sut, name,
                                      DefaultConfig<Input>().(seed := Some(seed), numRuns := examples, clock := Some(clk)));
  }

  // Like RunMethodTestWithConfig, but fills any unset field with a fresh default:
  // a random seed if seed is None, and a SystemClock if clock is None. An
  // explicit seed is respected (reproducible).
  method RunMethodTestRandomWithConfig<Input(!new), E(==)>(
      arb: Arbitrary<Input>, sut: MethodUnderTest<Input, E>, name: string, cfg: RunConfig<Input>)
    returns (passed: bool)
    requires arb.Valid()
    requires sut.Valid()
  {
    var cfg' := cfg;
    if cfg'.seed.None? {
      var seed := GetSeed();
      cfg' := cfg'.(seed := Some(seed));
    }
    if cfg'.clock.None? {
      var clk := new SystemClock();
      cfg' := cfg'.(clock := Some(clk));
    }
    passed := RunMethodTestWithConfig(arb, sut, name, cfg');
  }
}
