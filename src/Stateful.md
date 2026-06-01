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
  // `prev` (model before this command) and `cmd` let Sample build a *transition*
  // model — e.g. carry the previous observation + an event for `cmd`.
  method Sample(prev: Model, cmd: Cmd, s: SUT, ghost repr: set<object>) returns (m: Model)
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
    if Check(cmd, m):                     // precondition over the model; if false, skip
        repr := RunCmd(cmd, m, s, repr)   // *** mutate the SUT in place (footprint may grow) ***
        m := Sample(m, cmd, s, repr)      // project the mutated system into the next model
        step the LTL formula on m
    stop early once the formula is determined
```

The model is **sampled out of the system**, not computed by the command — so a command can't lie
about its effect. `Sample` receives the command so the model can carry an **event** for the
transition that produced it (e.g. `Enqueued(v)` / `Dequeued`). Relational step properties are then
expressed with LTL's **`Comparison`** operator — `ComparisonOf((p, c) => …)`, where `p` is the
current state and `c` the next — so the model needs *only* the current observation plus the event;
it does **not** store the previous observation (the temporal operator supplies it). For example,
"after an enqueue, `next.current == cur.current + [v]`" is
`Implies(ReqNext(PredOf(c => c.event.Enqueued?)), ComparisonOf((p, c) => … p.current + [v] == c.current))`.
None of this requires the SUT to log its own history. `Check` is a skip-precondition: a command
whose `Check` is false in the current model is silently skipped (not a failure). `RunCmd` returns the
(possibly grown) footprint `repr'`, so SUTs that allocate as they run (linked lists, trees, …) are
supported; a preallocated/bounded SUT just returns `repr` unchanged.

## Failure reporting

On failure the report prints the **violated LTL tags**, the **command trace**, and the **minimised
choices**, all from the *minimal* counterexample. Each test case returns a
`ModelTestOutcome(tags, commandTrace)` as its `TestResult` payload; `TestingState` tracks that
payload as `bestResult` in lockstep with the minimised choice sequence, so the trace is never a stale
shrink probe. Tag atomic properties with `.Tag("name")` (see [LTL.md](LTL.md)).

## Worked example — a circular (ring-buffer) FIFO queue (`test/StatefulTest.dfy`)

The production class extends nothing **and stores only the ring buffer** — no enqueue/dequeue logs
(those would be pure test instrumentation). The model carries only the current contents plus an
`event`; the LTL **`Comparison`** operator relates each state to the next, so no `previous` field is
needed. Commands are a datatype, and `SUT` is refined to the class, so `RunCmd` drives it with no
casts.

```dafny
module CircularQueueModelTest refines StatefulModelTest {
  const CAP: nat := 4
  datatype Event = Init | Enqueued(v: int) | Dequeued
  datatype QueueModel = QueueModel(current: seq<int>, event: Event)   // no `previous`
  type Model = QueueModel
  datatype QueueCmd = Enq(v: nat) | Deq | BuggyDeq
  type Cmd = QueueCmd

  class CircularQueue {                          // clean: ONLY a ring buffer, no logs
    var data: array<int>
    var head: nat
    var count: nat
    predicate Inv() reads this { data.Length > 0 && head < data.Length && count <= data.Length }
    function contentsFrom(i: nat): seq<int> reads this, data requires Inv() requires i <= count { /* … */ }
    method enqueue(v: int) requires Inv() requires count < data.Length
      modifies this, data ensures Inv() ensures data == old(data) { /* … */ }
    method dequeue() returns (v: int) requires Inv() requires count > 0
      modifies this ensures Inv() ensures data == old(data) { /* … */ }
    method dequeueLifo() returns (v: int) /* buggy: removes the back */ { /* … */ }
  }
  type SUT = CircularQueue

  ghost predicate ValidSUT(s: SUT, repr: set<object>) { s in repr && s.data in repr && s.Inv() }
  function InitialModel(): Model { QueueModel([], Init) }
  method MakeSUT() returns (s: SUT, ghost repr: set<object>) { s := new CircularQueue(CAP); repr := {s, s.data}; }

  // Sample carries the freshly-observed contents + an event for `cmd` (no previous).
  method Sample(prev: Model, cmd: Cmd, s: SUT, ghost repr: set<object>) returns (m: Model) {
    var cur := s.contentsFrom(0);
    var ev := match cmd { case Enq(v) => Enqueued(v) case Deq => Dequeued case BuggyDeq => Dequeued };
    m := QueueModel(cur, ev);
  }
  // Capacity-aware, so an accepted command always actually fires.
  predicate Check(cmd: Cmd, m: Model) {
    match cmd { case Enq(_) => |m.current| < CAP case Deq => |m.current| > 0 case BuggyDeq => |m.current| > 0 }
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

  // Each transition is consistent with its event — using Next + Implies + Comparison.
  // `p` is the current state, `c` the next; no `previous` field is stored.
  function StepConsistent(): LTLFormula<QueueModel> /* WellFormed */ {
    Always(And(
      Implies(WeakNext(PredOf((c: QueueModel) => c.event.Enqueued?)),
              ComparisonOf((p: QueueModel, c: QueueModel) =>
                c.event.Enqueued? ==> c.current == p.current + [c.event.v]).Tag("enqueue-step")),
      Implies(WeakNext(PredOf((c: QueueModel) => c.event.Dequeued?)),
              ComparisonOf((p: QueueModel, c: QueueModel) =>
                c.event.Dequeued? ==> |p.current| > 0 && c.current == p.current[1..]).Tag("dequeue-step"))
    ), 0)
  }

  method Main() {
    var goodCmds := Arbitrary<QueueCmd>.Of([Enq(1), Enq(2), Enq(3), Deq]);
    var _ := RunModelTest("queue (correct)", goodCmds, StepConsistent(), 30);
    var badCmds := Arbitrary<QueueCmd>.Of([Enq(1), Enq(2), Enq(3), BuggyDeq]);
    var _ := RunModelTest("queue (buggy LIFO)", badCmds, StepConsistent(), 30);
  }
}
```

Each implication reads: *if the next state's event is this command, then the comparison between the
current state `p` and the next state `c` holds.* An enqueue must extend the contents by `v`; a
dequeue must drop the front. The correct queue passes; the buggy LIFO dequeue removes the *back*, so
after it `c.current != p.current[1..]`:

```
[queue (correct)] PASS (1000 valid examples)

[queue (buggy LIFO)] FAIL
  violated tags: {dequeue-step}
  commands: [Enq(2), Enq(1), BuggyDeq]
  minimised choices: [1, 0, 3]
```

The minimal counterexample needs two distinct elements then a buggy dequeue: the prior state `p` has
`p.current = [2,1]`, the buggy pop yields `c.current = [2]`, but `p.current[1..] = [1]` — the
`dequeue-step` comparison fails.
