# DafnyCheck

A property-based testing library for [Dafny](https://dafny.org/), in the style of
[Minithesis](https://github.com/DRMacIver/minithesis) / Hypothesis: generate random inputs from
composable `Arbitrary<T>` generators, check a property, and **shrink** any failing example down
to a minimal counterexample. It also supports method-under-test testing and stateful
(model-based) testing with LTL temporal properties — the latter a Dafny port of
[`@fast-check/LTL` (LTLTS)](https://github.com/hath995/LTLTS) (after Oskar Wickström /
Quickstrom and Liam O'Connor).

## Layout & documentation

Each user-facing source file has a companion `.md` with its API and signatures:

| File | Docs | What it provides |
|------|------|------------------|
| `src/DafnyCheck.dfy` | [DafnyCheck.md](src/DafnyCheck.md) | the `RunTest*` / `RunMethodTest*` entry points + engine |
| `src/Arbitrary.dfy` | [Arbitrary.md](src/Arbitrary.md) | the `Arbitrary<T>` generator catalog, combinators, `Registry` letrec, `Transformable` |
| `src/RunConfig.dfy` | [RunConfig.md](src/RunConfig.md) | `RunConfig<T>` + `Verbosity` |
| `src/Stateful.dfy` | [Stateful.md](src/Stateful.md) | model-based testing: abstract `StatefulModelTest` (refine it), `RunModelTest` |
| `src/LTL.dfy` | [LTL.md](src/LTL.md) | LTL formula operators (`Always`, `Eventually`, `Until`, …) |
| `src/Reporting.dfy` | [Reporting.md](src/Reporting.md) | colored, verbosity-gated reporting helpers |
| `src/RandomGenerator.dfy` | [RandomGenerator.md](src/RandomGenerator.md) | the xoroshiro128+ PRNG |
| `src/colors.dfy` | [colors.md](src/colors.md) | ANSI color constants |
| `src/ExtendedArbitraries/` | [README.md](src/ExtendedArbitraries/README.md) | UUID, ULID, IPv4/6, email, domain, JSON |

Internal-only files (`TestResult.dfy`, `TestStatus.dfy`, `utils.dfy`, `LTL_contramap.dfy`) hold
types/helpers and aren't documented separately. Tests under `test/` mirror `src/`.

## Build & verify

```sh
dafny verify dfyconfig.toml --allow-warnings
dafny test test/MinithesisTest.dfy --standard-libraries --allow-warnings   # run {:test} methods
```

## The run methods

Everything below returns `bool` — `true` iff every always-tested example and every generated
case passed. Generators are described sparsely here; see [Arbitrary.md](src/Arbitrary.md) for the
full catalog and [RunConfig.md](src/RunConfig.md) for the config fields.

### Predicate tests

```dafny
include "src/DafnyCheck.dfy"
import opened DafnyCheck
import opened Arbitrary
import opened RunConfig
import opened Std.Wrappers

method Example() {
  var arb := Arbitrary<int>.Range(0, 100);              // a generator; see Arbitrary.md

  // Simple form:
  var ok := RunTest((n: int) => 0 <= n < 100, arb, "in range");

  // Configured form — seed, run count, always-tested examples, a classifier
  // (prints a distribution), color, verbosity. All fields optional via DefaultConfig():
  var cfg := DefaultConfig<int>()
    .(seed := Some(7), numRuns := 200, verbosity := Medium,
      examples := [0, 99],
      classifier := Some((n: int) => if n < 50 then "low" else "high"));
  var ok2 := RunTestWithConfig((n: int) => 0 <= n < 100, arb, "in range", cfg);
}
```

### Method-under-test tests

Wrap a heap-mutating method in a `MethodUnderTest<Input, E>` subclass and drive it with
`RunMethodTest` / `RunMethodTestWithConfig` — same shape as above. See
[DafnyCheck.md](src/DafnyCheck.md).

### Stateful (model-based) tests

Write a test by `refines`-ing the abstract `StatefulModelTest` module: supply the concrete `Model`,
system-under-test `SUT`, and command `Cmd` types plus their operations, and inherit the runner. The
engine generates command sequences, drives them against a fresh **mutable** system per case,
`Sample()`s it into a model after each command, and checks an LTL property over those model states
with `RunModelTest`. Because `SUT` is refined to a concrete class, command bodies drive it with **no
downcasts**, and the production class stays **clean** (it extends nothing; commands are a plain
datatype). See [Stateful.md](src/Stateful.md) for the abstract module and a worked circular-queue
FIFO example, and [LTL.md](src/LTL.md) for the temporal operators (`Always`, `Eventually`, `Until`,
`Release`, `Next`, `And`/`Or`/`Not`/`Implies`, …).

## A taste of the generators

```dafny
var xs   := Arbitrary<int>.Lists(Arbitrary<int>.Range(0, 10), 0, 5);     // seq<int>, length 0..5
var pair := Arbitrary<bool>.Bools();                                      // bool
var uuid := ExtIdentifiers.UUID();                                        // UUID strings
```

The full set — primitives, collections, tuples, bit vectors, arrays, `Map`/`Mix`/`FlatMap`, and
the `Registry` letrec for recursive datatypes — is in [Arbitrary.md](src/Arbitrary.md).
