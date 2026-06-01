# `Stateful.dfy` — model-based testing (module `StatefulTesting`)

Stateful / model-based property testing: generate a sequence of `Command`s, drive them against a
**mutable system under test (SUT)**, project the system into an immutable **model** after every
command, and check an [LTL temporal property](LTL.md) over the resulting sequence of model states.
This is the Dafny analogue of [`@fast-check/LTL` (LTLTS)](https://github.com/hath995/LTLTS)'s
`temporalModelRun`, built on the [`DafnyCheck`](DafnyCheck.md) engine (so it inherits generation,
shrinking, seeding, and reporting for free).

## Intuition

Three moving parts:

- **System (`System<Model>`)** — the real, **mutable** thing you want to test (usually a heap
  object with methods). It is created fresh for each test case and mutated *in place* by commands.
- **Model (`Model`)** — a small, immutable abstraction of the system's *observable* state. The LTL
  property is written against the model, never against the system directly.
- **Sample (`System.Sample`)** — the bridge: a method on the system that reads its current state
  and produces the model you make assertions about.

The runner repeats, for each generated command sequence:

```
sys := factory.Make()              // fresh, Valid() SUT
m   := initialModel                // starting model (should equal a Sample() of the fresh system)
for each generated command cmd, up to maxSteps:
    if cmd.check(m):               // precondition over the *model*; if false, skip the command
        cmd.run(m, sys)            // *** mutate the SUT in place ***
        m := sys.Sample()          // project the mutated system into the next model
        step the LTL formula on m  // advance the temporal property one state
    stop early once the formula is determined (True/False)
```

The key idea: **the model is sampled out of the system, not computed by the command.** `run` drives
the system forward; the *truth* about the new state always comes from `Sample`, so a command can't
"lie" about its effect to make the property pass. `check(m)` is a precondition — a command whose
`check` is false for the current model is silently skipped (not a failure), which is how you say
"this operation is only legal in these states."

## Why `System` is a trait (and the SUT is mutable)

If `run` just returned new data, an ordinary `RunMethodTest` would already suffice — the point of a
*stateful* test is to drive a **mutable** SUT and watch it evolve. To mutate a value in place a
method needs a `modifies` clause, and `modifies` requires a *reference*. A generic type parameter
can't be one (Dafny can't prove a type parameter is a reference type), so `System` is modelled as a
**trait** — exactly mirroring the `Transformable<T>` trait that `Arbitrary<T>` wraps:

- it owns its heap footprint as `ghost var repr: set<object>`, and
- carries a `Valid()` invariant with the standard `Valid() ==> this in repr` shape.

A trait instance *is* a reference, so `modifies sys.repr` is legal and a command can mutate the
system in place. Concrete SUTs `extend System<Model>`, put their mutable state (arrays, cells, …)
into `repr`, and implement `Sample`.

## The traits

```dafny
// The mutable system under test. Concrete SUTs extend this.
trait System<Model(!new)> {
  ghost var repr: set<object>
  ghost predicate Valid() reads this, repr ensures Valid() ==> this in repr
  method Sample() returns (m: Model)          // project current state → model
    requires Valid() ensures Valid()
}

// A command drives the system in place.
trait Command<Model(!new)> {
  ghost var repr: set<Command<Model>>
  ghost predicate Valid() reads this, repr ensures Valid() ==> this in repr
  predicate check(m: Model)                   // precondition over the current model
  method run(m: Model, sys: System<Model>)
    requires check(m) requires sys.Valid()
    modifies sys.repr                          // mutate the SUT in place
    ensures sys.Valid()
    ensures fresh(sys.repr - old(sys.repr))    // may grow repr, but only with fresh objects
  function toString(): string reads this       // label for the failure trace
}

// Builds a fresh, valid SUT per test case.
trait SystemFactory<Model(!new)> {
  method Make() returns (sys: System<Model>)
    ensures fresh(sys) ensures fresh(sys.repr) ensures sys.Valid()
}
```

Notes:

- `run` mutates `sys` in place; it does **not** return a model. A command typically downcasts
  `sys as ConcreteSUT` in its body to call the SUT's methods. It may grow `sys.repr` (e.g. allocate
  internal nodes) provided the additions are `fresh` and `Valid()` is restored — that's what the
  `ensures fresh(sys.repr - old(sys.repr))` clause guarantees, and it's what lets the runner keep
  modifying the system across steps without listing it in `Apply`'s `modifies` clause (the whole
  `sys.repr` stays fresh and disjoint from the engine's own state).
- `Sample` and the SUT operations are *methods* (not `function`s) so they may read/mutate heap
  freely. Concrete `System`/`Command`/`SystemFactory` classes are annotated
  `@AssumeCrossModuleTermination` and give their methods `decreases 0`, because the engine calls
  them across the module boundary.

## Run methods

```dafny
type PropertyTest<!T> = T -> bool

// Predicate property over a single drawn input — delegates to DafnyCheck.RunTest.
method RunTest<T(!new)>(test: PropertyTest<T>, arb: Arbitrary<T>, name: string) returns (passed: bool)
  requires arb.Valid()

// Model-based run: generate command sequences, sample the system after each command,
// and evaluate `ltlProperty` over the sampled model states. Defaults: 100 runs,
// seed 42, color on, Low verbosity.
method RunModelTest<Model(!new)>(
    name: string,
    cmds: Arbitrary<Command<Model>>,
    ltlProperty: LTLFormula<Model>,
    initialModel: Model,
    factory: SystemFactory<Model>,
    maxSteps: nat)
  returns (passed: bool)
  requires cmds.Valid() && WellFormedFormula(ltlProperty) && 0 < maxSteps

// As above, but exposes run count, seed, color, and verbosity. (The classifier/examples
// knobs of RunConfig are not applied to model tests — commands aren't readily classifiable —
// so they are explicit parameters rather than a RunConfig value.)
method RunModelTestWithConfig<Model(!new)>(
    name, cmds, ltlProperty, initialModel, factory, maxSteps,
    numRuns: nat, seed: bv64, useColor: bool, verbosity: Verbosity)
  returns (passed: bool)
```

The runners are generic over `Model` only — `System<Model>` is plugged in by inheritance, just as a
`Transformable<T>` is plugged into `Arbitrary<T>`. All return `bool` (`true` = the property held on
every generated run). Build `cmds` with the generators in [`Arbitrary.md`](Arbitrary.md) (e.g.
`Of([...commands])` or `Mix`), and build `ltlProperty` with the operators in [`LTL.md`](LTL.md).

## Failure reporting

On failure the report prints the **violated LTL tags**, the **command trace**, and the
**minimised choices** — all from the *minimal* counterexample, not the last thing the shrinker tried:

```dafny
datatype ModelTestOutcome = ModelTestOutcome(tags: set<string>, commandTrace: seq<string>)
```

`ModelTestFunction` extends `TestFunction<ModelTestOutcome>`, so each test case returns its tags +
trace **inside the `TestResult` payload**. `TestingState` tracks that payload as `bestResult` in
lockstep with the minimised choice sequence, and the runner reads the trace/tags off
`GetBestResult()`. Tag an atomic property with `.Tag("name")` (see [LTL.md](LTL.md)) to control what
appears here.

## Worked example — a circular (ring-buffer) FIFO queue (`test/StatefulTest.dfy`)

The SUT is a real fixed-capacity ring buffer mutated in place. The model records the current
contents plus a log of every enqueue and dequeue, and the property asserts FIFO correctness:

```dafny
datatype QueueModel = QueueModel(current: seq<int>, enqueued: seq<int>, dequeued: seq<int>)

@AssumeCrossModuleTermination
class CircularQueue extends System<QueueModel> {
  var data: array<int>            // capacity == data.Length
  var head: nat                   // index of the front element
  var count: nat                  // number of live elements
  var enqLog: seq<int>            // every accepted enqueue, in order
  var deqLog: seq<int>            // every dequeue, in order
  // constructor sets repr := {this, data}

  ghost predicate Valid() reads this, repr ensures Valid() ==> this in repr {
    this in repr && data in repr && repr == {this, data}
    && data.Length > 0 && head < data.Length && count <= data.Length
  }
  method Sample() returns (m: QueueModel) requires Valid() ensures Valid() {
    m := QueueModel(contentsFrom(0), enqLog, deqLog);   // contents in FIFO order
  }
  method enqueue(v: int) requires Valid() requires count < data.Length
    modifies repr ensures Valid() ensures fresh(repr - old(repr)) { /* … */ }
  method dequeue() returns (v: int) requires Valid() requires count > 0
    modifies repr ensures Valid() ensures fresh(repr - old(repr)) { /* … */ }
}
```

A command downcasts and drives the SUT (note: no boilerplate beyond the cast):

```dafny
method run(m: QueueModel, sys: System<QueueModel>)
  requires check(m) requires sys.Valid()
  modifies sys.repr ensures sys.Valid() ensures fresh(sys.repr - old(sys.repr))
{
  if sys is CircularQueue {
    var q := sys as CircularQueue;
    if q.count < q.data.Length { q.enqueue(value); }   // defensive guard
  }
}
```

The property — FIFO order **and** multiset preservation — written against the model:

```dafny
function QueueCorrect(): LTLFormula<QueueModel> /* WellFormed */ {
  Always(And(
    PredOf((m: QueueModel) => m.enqueued == m.dequeued + m.current).Tag("fifo"),
    PredOf((m: QueueModel) =>
      multiset(m.enqueued) == multiset(m.dequeued) + multiset(m.current)).Tag("multiset")), 0)
}
```

`enqueued == dequeued + current` says everything put in (in order) equals everything taken out (in
order) followed by everything still queued — FIFO correctness, which also implies the multiset of
inserted items equals dequeued ⊎ remaining.

Driving correct commands passes; swapping in a **buggy LIFO dequeue** (returns the back element)
fails, and the minimised counterexample isolates the smallest order-violating trace:

```
[circular queue: FIFO + multiset (correct)] PASS (1000 valid examples)

[circular queue: FIFO violated by LIFO dequeue] FAIL
  violated tags: {fifo}
  commands: [Enq(2), Enq(1), BuggyDeq]
  minimised choices: [1, 0, 3]
```

Only `fifo` is reported, not `multiset`: a LIFO pop returns the right *items* in the wrong *order*,
so the multiset invariant still holds — a nice illustration of tags pinpointing *which* property
broke.
