# `Stateful.dfy` — model-based testing (abstract module `StatefulModelTest`)

Stateful / model-based property testing via **module refinement**. You write a test by `refines`-ing
the abstract `StatefulModelTest` module: you supply the concrete `Model`, system-under-test `SUT`,
and command `Cmd` types plus the operations over them, and you inherit the whole runner. The engine
generates command sequences, drives them against a fresh (possibly mutable, heap) system, samples it
into an immutable model after each command, and checks an [LTL temporal property](LTL.md) over the
model trace — all on top of the [`DafnyCheck`](DafnyCheck.md) engine (generation, shrinking, seeding,
reporting). It is the Dafny analogue of
[`@fast-check/LTL` (LTLTS)](https://github.com/hath995/LTLTS)'s `temporalModelRun`.

## Why refinement (and no casts, no test damage)

A *stateful* test drives a **mutable** SUT in place. Mutating a heap object needs a `modifies`
clause, and `modifies` requires a *reference*. Neither a generic **type parameter** nor an abstract
**type** is assignable to `object` in Dafny, so `modifies sys` / `sys in repr` are type errors for
both — you cannot frame a generic SUT's heap directly.

Module refinement sidesteps this: in the *refining* module the deferred `type SUT` becomes a
**concrete class**, so command bodies call its methods directly — **no downcasts**. The only thing
that must cross the abstract/concrete boundary is the SUT's heap footprint, and that is threaded as
an explicit ghost `set<object>` (`repr`), which *is* allowed in `modifies`/`reads`. The result:

- the production class stays **completely clean** — it extends nothing and has no testing concepts;
- commands are a plain **datatype** (no per-command classes, no `repr`/`Valid` boilerplate);
- the runner (`Apply` loop, `RunModelTest`) is written **once** in the abstract module.

## The abstract module — what you refine

```dafny
abstract module StatefulModelTest {
  type Model(!new)            // immutable observation of the system
  type SUT                    // the system under test (refined to a concrete class)
  type Cmd(!new)              // the command alphabet (refined to a datatype)

  // The SUT's heap footprint is an explicit ghost set, so the abstract `SUT`
  // never appears in a reads/modifies clause.
  ghost predicate ValidSUT(s: SUT, repr: set<object>) reads repr
  function InitialModel(): Model

  method MakeSUT() returns (s: SUT, ghost repr: set<object>)
    ensures ValidSUT(s, repr) ensures fresh(repr)
  method Sample(s: SUT, ghost repr: set<object>) returns (m: Model)
    requires ValidSUT(s, repr) ensures ValidSUT(s, repr)
  predicate Check(cmd: Cmd, m: Model)                       // precondition over the model
  method RunCmd(cmd: Cmd, m: Model, s: SUT, ghost repr: set<object>)
    returns (ghost repr': set<object>)                      // footprint may grow
    requires Check(cmd, m) requires ValidSUT(s, repr)
    modifies repr
    ensures ValidSUT(s, repr') ensures repr <= repr' ensures fresh(repr' - repr)
  function CmdString(cmd: Cmd): string                      // label for the failure trace

  // ... inherited runner ...
  method RunModelTest(name: string, cmds: Arbitrary<Cmd>, ltlProperty: LTLFormula<Model>, maxSteps: nat)
    returns (passed: bool)
    requires cmds.Valid() && WellFormedFormula(ltlProperty) && 0 < maxSteps
  method RunModelTestWithConfig(name, cmds, ltlProperty, maxSteps,
    numRuns: nat, seed: bv64, useColor: bool, verbosity: Verbosity) returns (passed: bool)
}
```

The runner repeats, for each generated command sequence:

```
s, repr := MakeSUT()                  // fresh SUT + its footprint
m := InitialModel()
for each generated cmd, up to maxSteps:
    if Check(cmd, m):                 // precondition over the model; if false, skip
        repr := RunCmd(cmd, m, s, repr)   // *** mutate the SUT in place (footprint may grow) ***
        m := Sample(s, repr)              // project the mutated system into the next model
        step the LTL formula on m
    stop early once the formula is determined
```

The model is **sampled out of the system**, not computed by the command — so a command can't lie
about its effect. `Check` is a skip-precondition: a command whose `Check` is false in the current
model is silently skipped (not a failure). `RunCmd` returns the (possibly grown) footprint `repr'`,
so SUTs that allocate as they run (linked lists, trees, …) are supported; a preallocated/bounded SUT
just returns `repr` unchanged.

## Failure reporting

On failure the report prints the **violated LTL tags**, the **command trace**, and the **minimised
choices**, all from the *minimal* counterexample. Each test case returns a
`ModelTestOutcome(tags, commandTrace)` as its `TestResult` payload; `TestingState` tracks that
payload as `bestResult` in lockstep with the minimised choice sequence, so the trace is never a stale
shrink probe. Tag atomic properties with `.Tag("name")` (see [LTL.md](LTL.md)).

## Worked example — a circular (ring-buffer) FIFO queue (`test/StatefulTest.dfy`)

The production class extends nothing; commands are a datatype; `SUT` is refined to the class, so
`RunCmd` drives it with no casts.

```dafny
module CircularQueueModelTest refines StatefulModelTest {
  datatype QueueModel = QueueModel(current: seq<int>, enqueued: seq<int>, dequeued: seq<int>)
  type Model = QueueModel
  datatype QueueCmd = Enq(v: nat) | Deq | BuggyDeq
  type Cmd = QueueCmd

  class CircularQueue {                          // clean: no testing concepts
    var data: array<int>
    var head: nat
    var count: nat
    var enqLog: seq<int>
    var deqLog: seq<int>
    predicate Inv() reads this { data.Length > 0 && head < data.Length && count <= data.Length }
    method enqueue(v: int) requires Inv() requires count < data.Length
      modifies this, data ensures Inv() ensures data == old(data) { /* … */ }
    method dequeue() returns (v: int) requires Inv() requires count > 0
      modifies this ensures Inv() ensures data == old(data) { /* … */ }
    // ... contentsFrom(i), dequeueLifo() (the buggy LIFO pop) ...
  }
  type SUT = CircularQueue

  ghost predicate ValidSUT(s: SUT, repr: set<object>) { s in repr && s.data in repr && s.Inv() }
  function InitialModel(): Model { QueueModel([], [], []) }
  method MakeSUT() returns (s: SUT, ghost repr: set<object>) { s := new CircularQueue(4); repr := {s, s.data}; }
  method Sample(s: SUT, ghost repr: set<object>) returns (m: Model) { m := QueueModel(s.contentsFrom(0), s.enqLog, s.deqLog); }
  predicate Check(cmd: Cmd, m: Model) {
    match cmd { case Enq(_) => true case Deq => |m.current| > 0 case BuggyDeq => |m.current| > 0 }
  }
  method RunCmd(cmd: Cmd, m: Model, s: SUT, ghost repr: set<object>) returns (ghost repr': set<object>) {
    match cmd {                                  // s IS a CircularQueue — no casts
      case Enq(v)   => if s.count < s.data.Length { s.enqueue(v); }
      case Deq      => if s.count > 0 { var _ := s.dequeue(); }
      case BuggyDeq => if s.count > 0 { var _ := s.dequeueLifo(); }
    }
    repr' := repr;                               // preallocated ring buffer: footprint fixed
  }
  function CmdString(cmd: Cmd): string { match cmd { case Enq(v) => "Enq(" + IntToString(v) + ")" case Deq => "Deq" case BuggyDeq => "BuggyDeq" } }

  // FIFO correctness + multiset preservation, over the model
  function QueueCorrect(): LTLFormula<QueueModel> /* WellFormed */ {
    Always(And(
      PredOf((m: QueueModel) => m.enqueued == m.dequeued + m.current).Tag("fifo"),
      PredOf((m: QueueModel) =>
        multiset(m.enqueued) == multiset(m.dequeued) + multiset(m.current)).Tag("multiset")), 0)
  }

  method Main() {
    var goodCmds := Arbitrary<QueueCmd>.Of([Enq(1), Enq(2), Enq(3), Deq]);
    var _ := RunModelTest("queue (correct)", goodCmds, QueueCorrect(), 30);
    var badCmds := Arbitrary<QueueCmd>.Of([Enq(1), Enq(2), Enq(3), BuggyDeq]);
    var _ := RunModelTest("queue (buggy LIFO)", badCmds, QueueCorrect(), 30);
  }
}
```

`enqueued == dequeued + current` says everything enqueued, in order, equals everything dequeued (in
order) followed by everything still queued — FIFO correctness, which also implies the multiset of
inserted items equals dequeued ⊎ remaining. Correct commands pass; the buggy LIFO dequeue fails:

```
[queue (correct)] PASS (1000 valid examples)

[queue (buggy LIFO)] FAIL
  violated tags: {fifo}
  commands: [Enq(2), Enq(1), BuggyDeq]
  minimised choices: [1, 0, 3]
```

Only `fifo` is reported, not `multiset`: a LIFO pop returns the right *items* in the wrong *order*,
so the multiset invariant still holds — tags pinpoint *which* property broke.
