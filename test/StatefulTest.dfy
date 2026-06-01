include "../src/Stateful.dfy"

// Model-based test of a circular FIFO queue, by *refining* `StatefulModelTest`.
//
// The production class `CircularQueue` is now genuinely clean: it stores only
// the ring buffer (data/head/count) — no enqueue/dequeue logs, which would be
// pure test instrumentation. The model carries the current contents, the SUT's
// `count` field, and an `event` for the command just run. Two kinds of LTL
// property are checked:
//
//   * step-consistency (relational, via the Comparison operator):
//       Enqueued(v): next.current == cur.current + [v]
//       Dequeued   : next.current == cur.current[1..]   (front removed, FIFO)
//   * a plain state invariant: count == |current|.
//
// Demo 1: correct Enqueue/Dequeue → PASS.
// Demo 2: a buggy LIFO dequeue    → FAIL on `dequeue-step` (removes the back).
module CircularQueueModelTest refines StatefulModelTest {
  const CAP: nat := 4

  // ---- the model carries the current contents, the SUT's count field, and the
  //      event that produced this state. The previous contents are NOT stored:
  //      the LTL Comparison operator gives access to the prior state directly. ----
  datatype Event = Init | Enqueued(v: int) | Dequeued | Other
  datatype QueueModel = QueueModel(current: seq<int>, count: nat, expectedCount: nat, event: Event)
  type Model = QueueModel

  datatype QueueCmd = Enq(v: nat) | Deq | BuggyDeq | BumpCount
  type Cmd = QueueCmd

  // ---- the clean production class: ONLY a ring buffer, no test logs ----
  class CircularQueue {
    var data: array<int>
    var head: nat
    var count: nat

    constructor(capacity: nat)
      requires capacity > 0
      ensures fresh(this) && fresh(data)
      ensures data.Length == capacity && head == 0 && count == 0
    {
      data := new int[capacity]; head := 0; count := 0;
    }

    predicate Inv() reads this { data.Length > 0 && head < data.Length && count <= data.Length }

    // Current contents in FIFO order — a normal observation (not history).
    function contentsFrom(i: nat): seq<int>
      reads this, data requires Inv() requires i <= count decreases count - i
    {
      if i == count then [] else [data[(head + i) % data.Length]] + contentsFrom(i + 1)
    }

    method enqueue(v: int)
      requires Inv() requires count < data.Length
      modifies this, data ensures Inv() ensures data == old(data)
    { data[(head + count) % data.Length] := v; count := count + 1; }

    method dequeue() returns (v: int)
      requires Inv() requires count > 0
      modifies this ensures Inv() ensures data == old(data)
    { v := data[head]; head := (head + 1) % data.Length; count := count - 1; }

    // BUG: removes the most-recently enqueued element (LIFO) instead of the front.
    method dequeueLifo() returns (v: int)
      requires Inv() requires count > 0
      modifies this ensures Inv() ensures data == old(data)
    { v := data[(head + count - 1) % data.Length]; count := count - 1; }

    // BUG: bumps the count without adding an element, desyncing the count field
    // from the number of logical operations performed.
    method bumpCount()
      requires Inv() requires count < data.Length
      modifies this ensures Inv() ensures data == old(data)
    { count := count + 1; }
  }
  type SUT = CircularQueue

  // ---- deferred operations ----
  ghost predicate ValidSUT(s: SUT, repr: set<object>) { s in repr && s.data in repr && s.Inv() }

  function InitialModel(): Model { QueueModel([], 0, 0, Init) }

  method MakeSUT() returns (s: SUT, ghost repr: set<object>)
  { s := new CircularQueue(CAP); repr := {s, s.data}; }

  // Build the transition model: previous contents, the event for `cmd`, and the
  // freshly-sampled current contents.
  method Sample(prev: Model, cmd: Cmd, s: SUT, ghost repr: set<object>) returns (m: Model)
  {
    var cur := s.contentsFrom(0);
    var ev := match cmd {
      case Enq(v)    => Enqueued(v)
      case Deq       => Dequeued
      case BuggyDeq  => Dequeued      // BuggyDeq is *supposed* to be a dequeue
      case BumpCount => Other         // not a logical enqueue/dequeue
    };
    // `expectedCount` is tracked *independently* of the SUT, from the logical
    // effect of each command — so comparing it to the SUT's count field is a real
    // cross-check (unlike count == |current|, which the sampling forces to hold).
    var expected := match cmd {
      case Enq(_)    => prev.expectedCount + 1
      case Deq       => if prev.expectedCount > 0 then prev.expectedCount - 1 else 0
      case BuggyDeq  => if prev.expectedCount > 0 then prev.expectedCount - 1 else 0
      case BumpCount => prev.expectedCount       // a count bump is no logical op
    };
    m := QueueModel(cur, s.count, expected, ev);   // count read straight from the SUT
  }

  // Capacity-aware preconditions, so an accepted command always actually fires.
  predicate Check(cmd: Cmd, m: Model)
  {
    match cmd {
      case Enq(_)    => |m.current| < CAP
      case Deq       => |m.current| > 0
      case BuggyDeq  => |m.current| > 0
      case BumpCount => |m.current| < CAP        // needs room to bump count
    }
  }

  method RunCmd(cmd: Cmd, m: Model, s: SUT, ghost repr: set<object>)
    returns (ghost repr': set<object>)
  {
    match cmd {                                   // s is a CircularQueue — no casts
      case Enq(v)    => if s.count < s.data.Length { s.enqueue(v); }
      case Deq       => if s.count > 0 { var _ := s.dequeue(); }
      case BuggyDeq  => if s.count > 0 { var _ := s.dequeueLifo(); }
      case BumpCount => if s.count < s.data.Length { s.bumpCount(); }
    }
    repr' := repr;                                // preallocated ring buffer: footprint fixed
  }

  function CmdString(cmd: Cmd): string
  {
    match cmd {
      case Enq(v)    => "Enq(" + IntToString(v) + ")"
      case Deq       => "Deq"
      case BuggyDeq  => "BuggyDeq"
      case BumpCount => "BumpCount"
    }
  }

  // ---- the LTL property, expressed with Next / Implies / Comparison ----
  // For each kind of transition: if the NEXT state's event is that command, then
  // the Comparison between the current state `p` and the next state `c` must hold.
  // The Comparison operator (CmpFn = (A, A) -> bool) is what removes the need to
  // store the previous contents in the model.
  function StepConsistent(): (r: LTLFormula<QueueModel>)
    ensures WellFormedFormula(r)
  {
    And(
      // enqueue: next.current == cur.current + [v]
      Implies(
        WeakNext(PredOf((c: QueueModel) => c.event.Enqueued?)),
        ComparisonOf((p: QueueModel, c: QueueModel) =>
          c.event.Enqueued? ==> c.current == p.current + [c.event.v]).Tag("enqueue-step")),
      // dequeue: next.current == cur.current[1..]
      Implies(
        WeakNext(PredOf((c: QueueModel) => c.event.Dequeued?)),
        ComparisonOf((p: QueueModel, c: QueueModel) =>
          c.event.Dequeued? ==> |p.current| > 0 && c.current == p.current[1..]).Tag("dequeue-step"))
    )
  }

  // ---- a plain state invariant: the count field matches the actual contents.
  //      (For this SUT it always holds — `contentsFrom` returns exactly `count`
  //      elements — so it documents the invariant / guards the observation logic.) ----
  function CountMatches(): (r: LTLFormula<QueueModel>)
    ensures WellFormedFormula(r)
  {
    PredOf((m: QueueModel) => m.count == |m.current|).Tag("count-matches")
  }

  // ---- a real cross-check: the SUT's count field matches the independently
  //      tracked operation count. A command that corrupts count (BumpCount) is
  //      caught here even though it touches no enqueue/dequeue event. ----
  function CountTracksOps(): (r: LTLFormula<QueueModel>)
    ensures WellFormedFormula(r)
  {
    PredOf((m: QueueModel) => m.count == m.expectedCount).Tag("count-tracks-ops")
  }

  // The full property bundle.
  function QueueProps(): (r: LTLFormula<QueueModel>)
    ensures WellFormedFormula(r)
  {
    Always(AndSeq([StepConsistent(), CountMatches(), CountTracksOps()]), 0)
  }

  // Pattern: `expect` the outcome of every run. A run should normally pass
  // (`expect ok`); when a run is *meant* to expose a bug, invert the check
  // (`expect !ok`) and say in the message which property should catch it.
  method {:test} QueueModelTest()
    decreases 0
  {
    // Correct commands: all properties hold → PASS.
    print "=== circular queue: correct Enqueue/Dequeue ===\n";
    var goodCmds := Arbitrary<QueueCmd>.Of([Enq(1), Enq(2), Enq(3), Deq]);
    var okGood := RunModelTest("queue: all properties (correct)", goodCmds, QueueProps(), 30);
    expect okGood, "correct queue should satisfy step-consistency, count==|current|, and count==expectedCount";

    // Buggy LIFO dequeue: breaks FIFO ordering but keeps counts correct, so we
    // EXPECT a failure — invert the check.
    print "\n=== circular queue: buggy LIFO dequeue (expected FAIL) ===\n";
    var lifoCmds := Arbitrary<QueueCmd>.Of([Enq(1), Enq(2), Enq(3), BuggyDeq]);
    var okLifo := RunModelTest("queue: buggy LIFO", lifoCmds, QueueProps(), 30);
    expect !okLifo, "buggy LIFO dequeue should violate FIFO step-consistency (dequeue-step)";

    // Count corruption: BumpCount desyncs the count field from the tracked op
    // count (step-consistency and count==|current| stay happy). EXPECT a failure.
    print "\n=== circular queue: count corruption (expected FAIL) ===\n";
    var bumpCmds := Arbitrary<QueueCmd>.Of([Enq(1), Deq, BumpCount]);
    var okBump := RunModelTest("queue: count corruption", bumpCmds, QueueProps(), 30);
    expect !okBump, "BumpCount should desync count from expectedCount (count-tracks-ops)";
  }
}
