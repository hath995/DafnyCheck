include "../src/Stateful.dfy"

// Model-based test of a circular FIFO queue, written by *refining* the abstract
// `StatefulModelTest` module. The production class `CircularQueue` extends
// nothing and contains no testing concepts; commands are a plain datatype; and
// because `SUT` is refined to `CircularQueue`, the command bodies drive the
// queue directly — no downcasts anywhere.
//
// Demo 1: correct Enqueue/Dequeue → PASS.
// Demo 2: a buggy LIFO dequeue    → FAIL on the `fifo` tag (multiset still holds).
module CircularQueueModelTest refines StatefulModelTest {

  // ---- concrete Model and Cmd (plain datatypes) ----
  datatype QueueModel = QueueModel(current: seq<int>, enqueued: seq<int>, dequeued: seq<int>)
  type Model = QueueModel

  datatype QueueCmd = Enq(v: nat) | Deq | BuggyDeq
  type Cmd = QueueCmd

  // ---- the clean production class: extends nothing, no testing concepts ----
  class CircularQueue {
    var data: array<int>
    var head: nat
    var count: nat
    var enqLog: seq<int>
    var deqLog: seq<int>

    constructor(capacity: nat)
      requires capacity > 0
      ensures fresh(this) && fresh(data)
      ensures data.Length == capacity
      ensures head == 0 && count == 0 && enqLog == [] && deqLog == []
    {
      data := new int[capacity];
      head := 0; count := 0; enqLog := []; deqLog := [];
    }

    predicate Inv() reads this { data.Length > 0 && head < data.Length && count <= data.Length }

    function contentsFrom(i: nat): seq<int>
      reads this, data requires Inv() requires i <= count decreases count - i
    {
      if i == count then [] else [data[(head + i) % data.Length]] + contentsFrom(i + 1)
    }

    method enqueue(v: int)
      requires Inv() requires count < data.Length
      modifies this, data ensures Inv() ensures data == old(data)
    {
      data[(head + count) % data.Length] := v; count := count + 1; enqLog := enqLog + [v];
    }

    method dequeue() returns (v: int)
      requires Inv() requires count > 0
      modifies this ensures Inv() ensures data == old(data)
    {
      v := data[head]; head := (head + 1) % data.Length; count := count - 1; deqLog := deqLog + [v];
    }

    // BUG: returns the most-recently enqueued element (LIFO). Inv()-preserving
    // but order-violating.
    method dequeueLifo() returns (v: int)
      requires Inv() requires count > 0
      modifies this ensures Inv() ensures data == old(data)
    {
      v := data[(head + count - 1) % data.Length]; count := count - 1; deqLog := deqLog + [v];
    }
  }
  type SUT = CircularQueue

  // ---- the deferred operations (no restating of requires/modifies/ensures) ----
  ghost predicate ValidSUT(s: SUT, repr: set<object>) { s in repr && s.data in repr && s.Inv() }

  function InitialModel(): Model { QueueModel([], [], []) }

  method MakeSUT() returns (s: SUT, ghost repr: set<object>)
  { s := new CircularQueue(4); repr := {s, s.data}; }

  method Sample(s: SUT, ghost repr: set<object>) returns (m: Model)
  { m := QueueModel(s.contentsFrom(0), s.enqLog, s.deqLog); }

  predicate Check(cmd: Cmd, m: Model)
  {
    match cmd {
      case Enq(_)   => true
      case Deq      => |m.current| > 0
      case BuggyDeq => |m.current| > 0
    }
  }

  method RunCmd(cmd: Cmd, m: Model, s: SUT, ghost repr: set<object>)
    returns (ghost repr': set<object>)
  {
    match cmd {                                   // <-- no casts: s is a CircularQueue
      case Enq(v)   => if s.count < s.data.Length { s.enqueue(v); }
      case Deq      => if s.count > 0 { var _ := s.dequeue(); }
      case BuggyDeq => if s.count > 0 { var _ := s.dequeueLifo(); }
    }
    repr' := repr;                                // ring buffer is preallocated: footprint fixed
  }

  function CmdString(cmd: Cmd): string
  {
    match cmd {
      case Enq(v)   => "Enq(" + IntToString(v) + ")"
      case Deq      => "Deq"
      case BuggyDeq => "BuggyDeq"
    }
  }

  // ---- the LTL property over the model ----
  function FifoAtom(): (r: LTLFormula<QueueModel>) ensures WellFormedFormula(r)
  { PredOf((m: QueueModel) => m.enqueued == m.dequeued + m.current).Tag("fifo") }

  function MultisetAtom(): (r: LTLFormula<QueueModel>) ensures WellFormedFormula(r)
  {
    PredOf((m: QueueModel) =>
      multiset(m.enqueued) == multiset(m.dequeued) + multiset(m.current)).Tag("multiset")
  }

  function QueueCorrect(): (r: LTLFormula<QueueModel>) ensures WellFormedFormula(r)
  { Always(And(FifoAtom(), MultisetAtom()), 0) }

  method Main()
    decreases 0
  {
    print "=== circular queue (refinement): correct Enqueue/Dequeue ===\n";
    var goodCmds := Arbitrary<QueueCmd>.Of([Enq(1), Enq(2), Enq(3), Deq]);
    var _ := RunModelTest("circular queue: FIFO + multiset (correct)", goodCmds, QueueCorrect(), 30);

    print "\n=== circular queue (refinement): buggy LIFO dequeue ===\n";
    var badCmds := Arbitrary<QueueCmd>.Of([Enq(1), Enq(2), Enq(3), BuggyDeq]);
    var _ := RunModelTest("circular queue: FIFO violated by LIFO dequeue", badCmds, QueueCorrect(), 30);
  }
}
