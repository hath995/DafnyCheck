module RunConfigs {
  import opened Std.Wrappers

  // Verbosity levels for test run reporting.
  //   Off    - print nothing
  //   Low    - (default) pass/fail summary + counterexamples
  //   Medium - + classification statistics
  //   High   - + shrink steps and extra detail
  datatype Verbosity = Off | Low | Medium | High

  function VerbosityRank(v: Verbosity): nat {
    match v
    case Off => 0
    case Low => 1
    case Medium => 2
    case High => 3
  }

  // True when `v` is at least as verbose as `threshold`.
  predicate AtLeast(v: Verbosity, threshold: Verbosity) {
    VerbosityRank(v) >= VerbosityRank(threshold)
  }

  // A monotonic wall-clock source, injected so the core stays extern-free.
  //
  // `Now()` returns a timestamp in nanoseconds from a monotonic source; only
  // *differences* are ever consumed, so the origin is irrelevant. It carries no
  // `modifies` clause: reading a clock is a benign real-world side effect the
  // verifier need not model, and an empty frame keeps a Clock out of every
  // repr/Valid apparatus (a TestingState never has to know about it).
  //
  // The trait is deliberately abstract and extern-free: the concrete,
  // platform-backed implementation (SystemClock) lives in SeededTesting, next to
  // the SeedSource extern it calls, so plain DafnyCheck runners need no native
  // file. Timing is opt-in — supply a clock via RunConfig.clock to enable it.
  //
  // {:termination false}: SystemClock lives in another module (SeededTesting),
  // which Dafny only allows extending a trait opted out of cross-module
  // termination checking — the same treatment TestFunction gets.
  trait {:termination false} Clock {
    method Now() returns (t: nat)
  }

  // Optional configuration for a test run. Every field has a sensible default
  // via DefaultConfig(); callers override individual fields with datatype-update
  // syntax, e.g. DefaultConfig().(seed := Some(7), verbosity := High).
  //
  //   numRuns    - number of generated examples to attempt
  //   seed       - RNG seed; None uses the library default (42)
  //   examples   - concrete inputs always tested before random generation
  //   classifier - optional T -> bucket-label function for distribution stats
  //   useColor   - whether reporting emits ANSI color escapes
  //   verbosity  - how much the run prints (see Verbosity)
  //   clock      - optional monotonic time source; Some(_) turns on run timing,
  //                whose detail is gated by verbosity (Low: whole run, Medium:
  //                + per-test, High: + generation/shrinking phases). None (the
  //                default) leaves the run untimed and extern-free.
  datatype RunConfig<!T> = RunConfig(
    numRuns: nat,
    seed: Option<bv64>,
    examples: seq<T>,
    classifier: Option<T -> string>,
    useColor: bool,
    verbosity: Verbosity,
    clock: Option<Clock>
  )

  function DefaultConfig<T>(): RunConfig<T> {
    RunConfig(100, None, [], None, true, Low, None)
  }
}
