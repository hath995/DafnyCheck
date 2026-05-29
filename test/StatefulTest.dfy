include "../src/Stateful.dfy"

// End-to-end demo of both runners:
//   1) Minithesis-style predicate test that should FAIL (and report a small
//      failing input).
//   2) Stateful model test where the commands respect the model invariant —
//      should PASS.
//   3) Same stateful test with a buggy decrement command that ignores its
//      precondition — should FAIL with the tagged Always property violated.
module StatefulTestExample {
  import opened StatefulTesting
  import opened Arbitrary
  import opened LTL
  import opened Std.Wrappers

  // Immutable model — just an int we expect to stay >= 0.
  datatype CounterModel = CounterModel(value: int)

  // Heap-mutable System under test that Commands actually drive.
  class CounterSystem {
    var value: int
    constructor()
      ensures fresh(this)
      ensures this.value == 0
    {
      value := 0;
    }
  }

  @AssumeCrossModuleTermination
  class CounterFactory extends SystemFactory {
    constructor()
      ensures fresh(this)
    {}

    method Make() returns (sys: object)
      ensures fresh(sys)
      decreases 0
    {
      sys := new CounterSystem();
    }
  }

  @AssumeCrossModuleTermination
  class IncCmd extends Command<CounterModel> {
    constructor()
      ensures fresh(this)
      ensures Valid()
    {
      this.repr := {this};
    }

    ghost predicate Valid()
      reads this, repr
      ensures Valid() ==> this in repr
    {
      this in repr && repr == {this}
    }

    predicate check(m: CounterModel) { true }

    method run(m: CounterModel, sys: object) returns (m': CounterModel)
      requires check(m)
      modifies sys
      decreases 0
    {
      if sys is CounterSystem {
        var cs := sys as CounterSystem;
        cs.value := cs.value + 1;
      }
      m' := CounterModel(m.value + 1);
    }

    function toString(): string { "Inc" }
  }

  @AssumeCrossModuleTermination
  class DecCmd extends Command<CounterModel> {
    constructor()
      ensures fresh(this)
      ensures Valid()
    {
      this.repr := {this};
    }

    ghost predicate Valid()
      reads this, repr
      ensures Valid() ==> this in repr
    {
      this in repr && repr == {this}
    }

    // Honest decrement: only allowed when the counter is strictly positive.
    predicate check(m: CounterModel) { m.value > 0 }

    method run(m: CounterModel, sys: object) returns (m': CounterModel)
      requires check(m)
      modifies sys
      decreases 0
    {
      if sys is CounterSystem {
        var cs := sys as CounterSystem;
        cs.value := cs.value - 1;
      }
      m' := CounterModel(m.value - 1);
    }

    function toString(): string { "Dec" }
  }

  // Buggy decrement: precondition is `true` so the model dips below zero.
  // We expect Always(value >= 0) to be falsified once this fires from m=0.
  @AssumeCrossModuleTermination
  class BadDecCmd extends Command<CounterModel> {
    constructor()
      ensures fresh(this)
      ensures Valid()
    {
      this.repr := {this};
    }

    ghost predicate Valid()
      reads this, repr
      ensures Valid() ==> this in repr
    {
      this in repr && repr == {this}
    }

    predicate check(m: CounterModel) { true }

    method run(m: CounterModel, sys: object) returns (m': CounterModel)
      requires check(m)
      modifies sys
      decreases 0
    {
      if sys is CounterSystem {
        var cs := sys as CounterSystem;
        cs.value := cs.value - 1;
      }
      m' := CounterModel(m.value - 1);
    }

    function toString(): string { "BadDec" }
  }

  // Atomic property tagged so the reporter prints "non-negative" on failure.
  function NonNegative(): (r: LTLFormula<CounterModel>)
    ensures WellFormedFormula(r)
  {
    PredOf((m: CounterModel) => m.value >= 0).Tag("non-negative")
  }

  // `Always non-negative` over the whole bounded trace.
  function AlwaysNonNegative(): (r: LTLFormula<CounterModel>)
    ensures WellFormedFormula(r)
  {
    Always(NonNegative(), 0)
  }

  method Main()
    decreases 0
  {
    print "=== predicate-based RunTest demo ===\n";
    var rangeArb := Arbitrary<int>.Range(0, 100);
    // Deliberately failing predicate so we see the failure-report path.
    RunTest((n: int) => n < 5, rangeArb, "n < 5 over Range(0, 100)");

    print "\n=== stateful RunModelTest demo (good commands) ===\n";
    var inc := new IncCmd();
    var dec := new DecCmd();
    var goodCmds := Arbitrary<Command<CounterModel>>.Of([inc, dec]);
    var factory := new CounterFactory();
    RunModelTest<CounterModel>(
      "counter: Always(value >= 0) with check-guarded Dec",
      goodCmds,
      AlwaysNonNegative(),
      CounterModel(0),
      factory,
      20);

    print "\n=== stateful RunModelTest demo (buggy decrement) ===\n";
    var inc2 := new IncCmd();
    var badDec := new BadDecCmd();
    var badCmds := Arbitrary<Command<CounterModel>>.Of([inc2, badDec]);
    var factory2 := new CounterFactory();
    RunModelTest<CounterModel>(
      "counter: Always(value >= 0) with unguarded BadDec",
      badCmds,
      AlwaysNonNegative(),
      CounterModel(0),
      factory2,
      20);
  }
}
