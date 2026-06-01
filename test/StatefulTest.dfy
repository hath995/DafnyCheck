include "../src/Stateful.dfy"

// Model-based test of a *mutable* circular (ring-buffer) FIFO queue.
//
// The system under test is a real heap object mutated in place via the
// `System<Model>` trait (modifies sys.repr). After each accepted command the
// runner Sample()s the queue into an immutable QueueModel and checks an LTL
// invariant over the model trace:
//
//   Always( enqueued == dequeued + current  AND
//           multiset(enqueued) == multiset(dequeued) + multiset(current) )
//
// i.e. everything ever enqueued, in order, equals everything dequeued (in
// order) followed by everything still in the queue — FIFO correctness, which
// also implies the multiset of inserted items equals dequeued ⊎ remaining.
//
// Demo 1: correct Enqueue/Dequeue commands          → PASS.
// Demo 2: a buggy LIFO dequeue (returns the back)    → FAIL on the `fifo` tag
//         (note multiset still holds — LIFO loses *order*, not *items*).
module CircularQueueTest {
  import opened StatefulTesting
  import opened Arbitrary
  import opened LTL
  import opened Std.Wrappers

  // Immutable observation of the queue: current contents (FIFO order), the full
  // log of accepted enqueues, and the full log of dequeues.
  datatype QueueModel = QueueModel(current: seq<int>, enqueued: seq<int>, dequeued: seq<int>)

  // ---- The mutable system under test: a fixed-capacity ring buffer ----
  @AssumeCrossModuleTermination
  class CircularQueue extends System<QueueModel> {
    var data: array<int>     // backing store; capacity == data.Length
    var head: nat            // index of the front element
    var count: nat           // number of live elements
    var enqLog: seq<int>     // every accepted enqueue, in order
    var deqLog: seq<int>     // every dequeue, in order

    constructor(capacity: nat)
      requires capacity > 0
      ensures fresh(this) && fresh(repr) && Valid()
      ensures head == 0 && count == 0 && enqLog == [] && deqLog == []
    {
      data := new int[capacity];
      head := 0; count := 0; enqLog := []; deqLog := [];
      repr := {this, data};
    }

    // Structural invariant only (indices in range). FIFO correctness is the
    // *property under test*, deliberately NOT baked in here, so a buggy command
    // can violate it without breaking Valid().
    ghost predicate Valid()
      reads this, repr
      ensures Valid() ==> this in repr
    {
      this in repr && data in repr && repr == {this, data}
      && data.Length > 0
      && head < data.Length
      && count <= data.Length
    }

    // Current contents in FIFO order: data[head], data[head+1], … (mod capacity).
    function contentsFrom(i: nat): seq<int>
      reads this, repr
      requires Valid()
      requires i <= count
      decreases count - i
    {
      if i == count then []
      else [data[(head + i) % data.Length]] + contentsFrom(i + 1)
    }

    method Sample() returns (m: QueueModel)
      requires Valid()
      ensures Valid()
      decreases 0
    {
      m := QueueModel(contentsFrom(0), enqLog, deqLog);
    }

    method enqueue(v: int)
      requires Valid()
      requires count < data.Length
      modifies repr
      ensures Valid()
      ensures fresh(repr - old(repr))
      decreases 0
    {
      data[(head + count) % data.Length] := v;
      count := count + 1;
      enqLog := enqLog + [v];
    }

    method dequeue() returns (v: int)
      requires Valid()
      requires count > 0
      modifies repr
      ensures Valid()
      ensures fresh(repr - old(repr))
      decreases 0
    {
      v := data[head];
      head := (head + 1) % data.Length;
      count := count - 1;
      deqLog := deqLog + [v];
    }

    // BUG: returns the most-recently enqueued element (LIFO) and leaves `head`
    // alone. Memory-safe and Valid()-preserving, but violates FIFO order.
    method dequeueLifo() returns (v: int)
      requires Valid()
      requires count > 0
      modifies repr
      ensures Valid()
      ensures fresh(repr - old(repr))
      decreases 0
    {
      v := data[(head + count - 1) % data.Length];
      count := count - 1;
      deqLog := deqLog + [v];
    }
  }

  @AssumeCrossModuleTermination
  class QueueFactory extends SystemFactory<QueueModel> {
    constructor() ensures fresh(this) {}
    method Make() returns (sys: System<QueueModel>)
      ensures fresh(sys) && fresh(sys.repr) && sys.Valid()
      decreases 0
    {
      sys := new CircularQueue(4);     // capacity 4
    }
  }

  // ---- Commands ----

  @AssumeCrossModuleTermination
  class EnqueueCmd extends Command<QueueModel> {
    var value: int
    var desc: string
    constructor(v: int, desc: string)
      ensures fresh(this) && Valid() && value == v && this.desc == desc
    { value := v; this.desc := desc; repr := {this}; }

    ghost predicate Valid() reads this, repr ensures Valid() ==> this in repr
    { this in repr && repr == {this} }

    predicate check(m: QueueModel) { true }

    method run(m: QueueModel, sys: System<QueueModel>)
      requires check(m) requires sys.Valid()
      modifies sys.repr ensures sys.Valid() ensures fresh(sys.repr - old(sys.repr))
      decreases 0
    {
      if sys is CircularQueue {
        var q := sys as CircularQueue;
        if q.count < q.data.Length {     // defensive: skip when full
          q.enqueue(value);
        }
      }
    }
    function toString(): string reads this { desc }
  }

  @AssumeCrossModuleTermination
  class DequeueCmd extends Command<QueueModel> {
    constructor() ensures fresh(this) && Valid() { repr := {this}; }
    ghost predicate Valid() reads this, repr ensures Valid() ==> this in repr
    { this in repr && repr == {this} }

    // Only dequeue when the model says the queue is non-empty.
    predicate check(m: QueueModel) { |m.current| > 0 }

    method run(m: QueueModel, sys: System<QueueModel>)
      requires check(m) requires sys.Valid()
      modifies sys.repr ensures sys.Valid() ensures fresh(sys.repr - old(sys.repr))
      decreases 0
    {
      if sys is CircularQueue {
        var q := sys as CircularQueue;
        if q.count > 0 {
          var _ := q.dequeue();
        }
      }
    }
    function toString(): string reads this { "Deq" }
  }

  // Same precondition as DequeueCmd, but drives the buggy LIFO dequeue.
  @AssumeCrossModuleTermination
  class BuggyDequeueCmd extends Command<QueueModel> {
    constructor() ensures fresh(this) && Valid() { repr := {this}; }
    ghost predicate Valid() reads this, repr ensures Valid() ==> this in repr
    { this in repr && repr == {this} }

    predicate check(m: QueueModel) { |m.current| > 0 }

    method run(m: QueueModel, sys: System<QueueModel>)
      requires check(m) requires sys.Valid()
      modifies sys.repr ensures sys.Valid() ensures fresh(sys.repr - old(sys.repr))
      decreases 0
    {
      if sys is CircularQueue {
        var q := sys as CircularQueue;
        if q.count > 0 {
          var _ := q.dequeueLifo();
        }
      }
    }
    function toString(): string reads this { "BuggyDeq" }
  }

  // ---- The LTL property ----

  function FifoAtom(): (r: LTLFormula<QueueModel>)
    ensures WellFormedFormula(r)
  {
    PredOf((m: QueueModel) => m.enqueued == m.dequeued + m.current).Tag("fifo")
  }

  function MultisetAtom(): (r: LTLFormula<QueueModel>)
    ensures WellFormedFormula(r)
  {
    PredOf((m: QueueModel) =>
      multiset(m.enqueued) == multiset(m.dequeued) + multiset(m.current)).Tag("multiset")
  }

  function QueueCorrect(): (r: LTLFormula<QueueModel>)
    ensures WellFormedFormula(r)
  {
    Always(And(FifoAtom(), MultisetAtom()), 0)
  }

  method Main()
    decreases 0
  {
    var empty := QueueModel([], [], []);

    print "=== circular queue: correct Enqueue/Dequeue ===\n";
    var e1 := new EnqueueCmd(1, "Enq(1)");
    var e2 := new EnqueueCmd(2, "Enq(2)");
    var e3 := new EnqueueCmd(3, "Enq(3)");
    var dq := new DequeueCmd();
    var goodCmds := Arbitrary<Command<QueueModel>>.Of([e1, e2, e3, dq]);
    var f1 := new QueueFactory();
    var _ := RunModelTest<QueueModel>(
      "circular queue: FIFO + multiset (correct)", goodCmds, QueueCorrect(), empty, f1, 30);

    print "\n=== circular queue: buggy LIFO dequeue ===\n";
    var e1b := new EnqueueCmd(1, "Enq(1)");
    var e2b := new EnqueueCmd(2, "Enq(2)");
    var e3b := new EnqueueCmd(3, "Enq(3)");
    var bdq := new BuggyDequeueCmd();
    var badCmds := Arbitrary<Command<QueueModel>>.Of([e1b, e2b, e3b, bdq]);
    var f2 := new QueueFactory();
    var _ := RunModelTest<QueueModel>(
      "circular queue: FIFO violated by LIFO dequeue", badCmds, QueueCorrect(), empty, f2, 30);
  }
}
