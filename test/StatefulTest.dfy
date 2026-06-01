include "../src/Stateful.dfy"

// Model-based test of a circular FIFO queue, by *refining* `StatefulModelTest`.
//
// The production class `CircularQueue` is now genuinely clean: it stores only
// the ring buffer (data/head/count) — no enqueue/dequeue logs, which would be
// pure test instrumentation. Instead the *model* is a transition record: the
// current contents, the previous contents, and an `event` for the command just
// run. The LTL property then checks each step relationally:
//
//   Enqueued(v): current == previous + [v]
//   Dequeued   : current == previous[1..]      (front removed, FIFO)
//
// Demo 1: correct Enqueue/Dequeue → PASS.
// Demo 2: a buggy LIFO dequeue    → FAIL on the `step` tag (it removes the back,
//         so current != previous[1..]).
module CircularQueueModelTest refines StatefulModelTest {
  const CAP: nat := 4

  // ---- the model carries only the current contents + the event that produced
  //      this state. The previous contents are NOT stored: the LTL Comparison
  //      operator gives the property access to the prior state directly. ----
  datatype Event = Init | Enqueued(v: int) | Dequeued
  datatype QueueModel = QueueModel(current: seq<int>, event: Event)
  type Model = QueueModel

  datatype QueueCmd = Enq(v: nat) | Deq | BuggyDeq
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
  }
  type SUT = CircularQueue

  // ---- deferred operations ----
  ghost predicate ValidSUT(s: SUT, repr: set<object>) { s in repr && s.data in repr && s.Inv() }

  function InitialModel(): Model { QueueModel([], Init) }

  method MakeSUT() returns (s: SUT, ghost repr: set<object>)
  { s := new CircularQueue(CAP); repr := {s, s.data}; }

  // Build the transition model: previous contents, the event for `cmd`, and the
  // freshly-sampled current contents.
  method Sample(prev: Model, cmd: Cmd, s: SUT, ghost repr: set<object>) returns (m: Model)
  {
    var cur := s.contentsFrom(0);
    var ev := match cmd {
      case Enq(v)   => Enqueued(v)
      case Deq      => Dequeued
      case BuggyDeq => Dequeued      // BuggyDeq is *supposed* to be a dequeue
    };
    m := QueueModel(cur, ev);        // no `previous` — the Comparison sees the prior state
  }

  // Capacity-aware preconditions, so an accepted command always actually fires.
  predicate Check(cmd: Cmd, m: Model)
  {
    match cmd {
      case Enq(_)   => |m.current| < CAP
      case Deq      => |m.current| > 0
      case BuggyDeq => |m.current| > 0
    }
  }

  method RunCmd(cmd: Cmd, m: Model, s: SUT, ghost repr: set<object>)
    returns (ghost repr': set<object>)
  {
    match cmd {                                   // s is a CircularQueue — no casts
      case Enq(v)   => if s.count < s.data.Length { s.enqueue(v); }
      case Deq      => if s.count > 0 { var _ := s.dequeue(); }
      case BuggyDeq => if s.count > 0 { var _ := s.dequeueLifo(); }
    }
    repr' := repr;                                // preallocated ring buffer: footprint fixed
  }

  function CmdString(cmd: Cmd): string
  {
    match cmd {
      case Enq(v)   => "Enq(" + IntToString(v) + ")"
      case Deq      => "Deq"
      case BuggyDeq => "BuggyDeq"
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
    Always(And(
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
    ), 0)
  }

  method {:test} QueueModelTest()
    decreases 0
  {
    print "=== circular queue (transition model): correct Enqueue/Dequeue ===\n";
    var goodCmds := Arbitrary<QueueCmd>.Of([Enq(1), Enq(2), Enq(3), Deq]);
    var _ := RunModelTest("queue: step-consistency (correct)", goodCmds, StepConsistent(), 30);

    print "\n=== circular queue (transition model): buggy LIFO dequeue ===\n";
    var badCmds := Arbitrary<QueueCmd>.Of([Enq(1), Enq(2), Enq(3), BuggyDeq]);
    var _ := RunModelTest("queue: step-consistency (buggy LIFO)", badCmds, StepConsistent(), 30);
  }
}
