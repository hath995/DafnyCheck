# `Arbitrary.dfy` — generators (module `Arbitrary`)

The generator library. An `Arbitrary<T>` produces values of type `T` from a `TestCase`'s
random/choice stream, and is the value you hand to the run methods in
[`DafnyCheck.dfy`](DafnyCheck.md). Almost all use goes through the **static factory methods**
and the **combinators** below; you only need the `Transformable` trait if you are writing a
genuinely custom generator.

```dafny
datatype Arbitrary<T> = Arbitrary(internalFunction: Transformable<T>)
```

## Primitive generators (static methods on `Arbitrary`)

```dafny
static method Bools() returns (p: Arbitrary<bool>)
static method Nats(bound: nat) returns (p: Arbitrary<nat>)            // [0, bound), requires 0 < bound <= MaxChoice
static method Range(min: int, max: int) returns (p: Arbitrary<int>)  // [min, max), requires min <= max && 0 < max-min < MaxChoice
static method Chars() returns (p: Arbitrary<char>)                   // printable ASCII [32,127)
static method Reals() returns (p: Arbitrary<real>)                   // non-negative rationals
static method Just<T>(value: T) returns (p: Arbitrary<T>)            // constant
static method Of<T>(args: seq<T>) returns (p: Arbitrary<T>)          // pick one of args, requires 0 < |args| <= MaxChoice
static method Strings(minLength: int, maxLength: int, ascii: bool) returns (p: Arbitrary<string>)

// Fixed-width bit vectors:
static method BitVectors1()  returns (p: Arbitrary<bv1>)
static method BitVectors2()  returns (p: Arbitrary<bv2>)
static method BitVectors8()  returns (p: Arbitrary<bv8>)
static method BitVectors16() returns (p: Arbitrary<bv16>)
static method BitVectors32() returns (p: Arbitrary<bv32>)
static method BitVectors64() returns (p: Arbitrary<bv64>)
static method BitVectors128() returns (p: Arbitrary<bv128>)
static method BitVectors256() returns (p: Arbitrary<bv256>)
```

## Collection generators

```dafny
static method Lists<S>(elementGenerator: Arbitrary<S>, minSize: int, maxSize: int) returns (p: Arbitrary<seq<S>>)
static method Sets<S(==)>(elementGenerator: Arbitrary<S>, minSize: int, maxSize: int) returns (p: Arbitrary<set<S>>)
static method Multisets<S(==)>(elementGenerator: Arbitrary<S>, minSize: int, maxSize: int) returns (p: Arbitrary<multiset<S>>)
static method Maps<K(==), V>(keyGen: Arbitrary<K>, valGen: Arbitrary<V>, minSize: int, maxSize: int) returns (p: Arbitrary<map<K, V>>)

// Heap arrays. 1-D is sized like Lists; 2-D/3-D are FIXED size (rows/cols/layers).
static method Arrays<S>(elementGenerator: Arbitrary<S>, minSize: int, maxSize: int) returns (p: Arbitrary<array<S>>)
static method Array2<S>(elementGenerator: Arbitrary<S>, rows: nat, cols: nat) returns (p: Arbitrary<array2<S>>)
static method Array3<S>(elementGenerator: Arbitrary<S>, rows: nat, cols: nat, layers: nat) returns (p: Arbitrary<array3<S>>)
```

## Tuples

```dafny
static method Tuple<T, U>(firstGenerator: Arbitrary<T>, secondGenerator: Arbitrary<U>) returns (p: Arbitrary<(T, U)>)
static method Tuple3<A, B, C>(a, b, c) returns (p: Arbitrary<(A, B, C)>)
// ... Tuple4 ... Tuple10, each taking N generators.
```

`Tuple3..Tuple10` are backed by dedicated `TupleN` datatypes that draw their N children directly
and build the flat tuple in one step — no nested pairs, no `Map` flatten. The arguments only need
to be `Valid()`; because an `Arbitrary` is now an immutable value, there is no representation-set
disjointness to establish.

## Combinators (instance methods)

```dafny
method Map<U>(fn: T -> U) returns (p: Arbitrary<U>)          // transform generated values
method FlatMap<U>(f: FlatMapFn<T, U>) returns (p: Arbitrary<U>)
static method Mix<T>(possibilities: seq<Arbitrary<T>>) returns (p: Arbitrary<T>)  // pick one generator (oneof)
```

`Mix` only requires each possibility to be `Valid()` — there is no disjointness obligation, since
values cannot alias. `FlatMap` takes a
`trait FlatMapFn<T, U> { method CreateArbitrary(t: T) returns (p: Arbitrary<U>) }`.

## Recursive generators / letrec — `Registry<T>`

fast-check-style `letrec` for recursive datatypes. Build each named arbitrary, writing
`reg.Tie(name)` at recursive positions, `Register` them, then `Lookup` the entry point. The
`TestCase` depth budget (`maxDepth`) falls back to the registered base case so generation
terminates. See [`../test/RecursiveTest.dfy`](../test/RecursiveTest.dfy) and
[`../test/WeirdTreeTest.dfy`](../test/WeirdTreeTest.dfy).

```dafny
class Registry<T(!new)> {
  constructor(baseKey: string, maxDepth: nat)
  method Register(key: string, arb: Arbitrary<T>)        // bind/replace a named arbitrary
  method Tie(key: string) returns (a: Arbitrary<T>)      // lazy reference to a named arbitrary
  function Lookup(key: string): Arbitrary<T>             // requires key in arbs
}
```

```dafny
var reg := new Registry<Tree>("Leaf", 4);          // base-case key + max depth
var elem := reg.Tie("Tree");
var nodes := Arbitrary<Tree>.Lists(elem, 0, 3);
var nodeArb := nodes.Map((ks) => Node(ks));
reg.Register("Leaf", leafArb);
reg.Register("Node", nodeArb);
var tieL := reg.Tie("Leaf"); var tieN := reg.Tie("Node");
reg.Register("Tree", Arbitrary<Tree>.Mix([tieL, tieN]));
var tree := reg.Lookup("Tree");
```

## Drawing values — `TestCase`

You rarely construct a `TestCase` directly except in unit tests of a generator; the run
methods build one for you. Its primitives, used by `Transformable.Apply`:

```dafny
class TestCase {
  constructor(prefix: seq<Choice>, random: XoroShift128Plus, maxSize: nat, printResults: bool)
  static method ForChoices(choices: seq<Choice>, seed: bv64, printResults: bool) returns (tc: TestCase)
  method MakeChoice(n: Choice) returns (result: TestResult<Choice>)     // a draw in [0, n)
  method ForcedChoice(n: Choice) returns (result: TestResult<Choice>)   // force the next choice to n
  method WeightedInternal(p: real) returns (result: TestResult<bool>)   // weighted coin, requires 0.0 <= p <= 1.0
}
```

`Choice` is a native uint32. Draws are finite-buffered: once `|choices|` reaches `maxSize` a draw
overruns, so `Apply` returns `Option<T>` and yields `None` rather than growing the buffer.

## Writing a custom generator — the `Transformable` trait

Only needed when no combination of the above suffices. `Transformable` is a **value trait**
(refined by *datatypes*, not classes — `--general-traits:datatype --type-system-refresh`).
Implement it as a datatype, modeling on the simplest leaf generator (`BoolsTransformable`), then
wrap it with `Arbitrary(yourTransformable)`:

```dafny
trait Transformable<T> {
  ghost function Height(): nat
  ghost predicate Valid()
    decreases Height(), 0
  method Apply(tc: TestCase) returns (result: Option<T>)
    requires tc.Valid() && this.Valid()
    ensures tc.Valid() && tc.repr == old(tc.repr)
    ensures |tc.choices| >= old(|tc.choices|) && tc.maxSize == old(tc.maxSize)
    decreases tc.maxSize - |tc.choices|, Height(), 0
    modifies tc, tc.random
}
```

`Apply` returns `None` when the choice buffer is exhausted (an overrun — Hypothesis's `StopTest`),
which propagates up so the example is discarded. Termination leads with the finite-buffer metric
`tc.maxSize - |tc.choices|`; `Height()` is the structural tie-breaker for combinators that recurse
into a child *without* first consuming a choice. A leaf generator returns `Height() == 0`; a
combinator stores a `ghost h` greater than every child's `Height()` and returns it (its `Valid()`
asserts `child.Height() < h`).

There is **no `repr`/object-graph bookkeeping**: datatype values have no heap identity, so
generators compose freely with no disjointness obligations. Wrapping a freshly-constructed datatype
needs one hint, `assert p.internalFunction is YourTransformable;`, to connect the abstract trait
`Valid()` to the datatype's body (see any factory). The two exceptions that still hold heap
references are `FlatMapFn` (a stateful factory, a reference trait pinned `extends object`) and
`Registry`/`LazyArbitrary` (the `letrec` cycle, which is genuinely heap-mutable).
