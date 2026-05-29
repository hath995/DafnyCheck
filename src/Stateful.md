# `Stateful.dfy` — model-based testing (module `StatefulTesting`)

Stateful / model-based property testing: drive a sequence of `Command`s against a fresh system
under test, threading an immutable model, and check an [LTL temporal property](LTL.md) over the
sequence of model states. This is the Dafny analogue of
[`@fast-check/LTL` (LTLTS)](https://github.com/hath995/LTLTS)'s `temporalModelRun`, built on the
[`DafnyCheck`](DafnyCheck.md) engine.

## Commands and the system factory

```dafny
trait Command<Model(!new)> {
  ghost var repr: set<Command<Model>>
  ghost predicate Valid() reads this, repr ensures Valid() ==> this in repr
  predicate check(m: Model)                                  // precondition over current model
  method run(m: Model, sys: object) returns (m': Model)      // pure model update + side-effect the SUT
    requires check(m) modifies sys
  function toString(): string                                // for failure reporting
}

trait SystemFactory {
  method Make() returns (sys: object) ensures fresh(sys)     // fresh SUT per test case
}
```

## Run methods

```dafny
type PropertyTest<!T> = T -> bool

// Predicate property over a single drawn input — delegates to DafnyCheck.RunTest.
method RunTest<T(!new)>(test: PropertyTest<T>, arb: Arbitrary<T>, name: string) returns (passed: bool)
  requires arb.Valid()

// Model-based run: generate command sequences, evaluate `ltlProperty` over the model states.
method RunModelTest<Model(!new)>(
    name: string,
    cmds: Arbitrary<Command<Model>>,
    ltlProperty: LTLFormula<Model>,
    initialModel: Model,
    factory: SystemFactory,
    maxSteps: nat)
  returns (passed: bool)
  requires cmds.Valid() && WellFormedFormula(ltlProperty) && 0 < maxSteps

// As above but with run count, seed, color, and verbosity (classifier/examples are not
// applied to model tests in this version).
method RunModelTestWithConfig<Model(!new)>(
    name, cmds, ltlProperty, initialModel, factory, maxSteps,
    numRuns: nat, seed: bv64, useColor: bool, verbosity: Verbosity)
  returns (passed: bool)
```

All return `bool` (`true` = property held on every generated run). On failure the report
includes the violated LTL tags and the command trace. Build `cmds` with the generators in
[`Arbitrary.md`](Arbitrary.md) (e.g. `Of([...commands])` or `Mix`), and build `ltlProperty`
with the operators in [`LTL.md`](LTL.md).
