include "./Arbitrary.dfy"
include "./DafnyCheck.dfy"
include "./LTL.dfy"

// Stateful (model-based) property testing on top of Minithesis's TestingState,
// using the LTL formula evaluator from LTL.dfy for temporal properties.
//
// The runner drives a sequence of `Command<Model, System>` against a fresh
// System per test case, threading an immutable Model and Step-ing the LTL
// formula state. It stops when:
//   - the formula is determined (True/False);
//   - the max step budget is reached;
//   - a violation is detected.
// Violated tags + command trace are reported on failure.
module StatefulTesting {
  import opened Arbitrary
  import opened TestResult
  import opened TestTypes
  import opened RandomGenerator
  import opened Std.Wrappers
  import M = DafnyCheck
  import opened LTL
  import opened LTLUtils

  // Predicate-based property: takes one input drawn from an Arbitrary<T>.
  type PropertyTest<!T> = T -> bool

  // A command in a model-based test. `check` is the precondition over the
  // current model state; `run` returns the next model (pure update) and may
  // side-effect the System under test; `toString` is for failure reporting.
  //
  // We use `object` (Dafny's universal reference type) for the System
  // parameter because Dafny type parameters can't be constrained to be
  // reference types and `modifies sys` requires that. Commands typically
  // cast `sys as ConcreteSUT` in their body.
  trait Command<Model(!new)> {
    ghost var repr: set<Command<Model>>

    ghost predicate Valid()
      reads this, repr
      ensures Valid() ==> this in repr

    predicate check(m: Model)
    method run(m: Model, sys: object) returns (m': Model)
      requires check(m)
      modifies sys
      decreases 0
    function toString(): string
  }

  // Factory that allocates a fresh System under test for each test case so
  // shrink/replay starts from a clean slate. Implementations should ensure
  // the returned reference is fresh and no other heap is touched.
  trait  SystemFactory {
    method Make() returns (sys: object)
      ensures fresh(sys)
  }

  // Top-level predicate-based RunTest — delegates straight to Minithesis.
  method RunTest<T(!new)>(test: PropertyTest<T>, arb: Arbitrary<T>, name: string)
    requires arb.Valid()
  {
    M.RunTest(test, arb, name);
  }

  // The model-test runner wraps one test case (one execution of a randomly
  // generated command sequence) as a TestFunction. Many such test cases are
  // run by the underlying TestingState.
  //
  // Per Apply: draw commands one at a time from `cmds`, skip those whose
  // check(m) is false (the user-selected policy), execute the ones that pass,
  // Step the LTL formula, stop when determined or out of budget. Failure tags
  // + command-trace strings are stashed on the instance so the outer runner
  // can print them.
  class ModelTestFunction<Model(!new)> extends M.TestFunction<()> {
    var cmds: Arbitrary<Command<Model>>
    var initialModel: Model
    var factory: SystemFactory
    var ltlProperty: LTLFormula<Model>
    var maxSteps: nat
    var lastFailureTags: set<string>
    var lastCommandTrace: seq<string>

    constructor(
      cmds: Arbitrary<Command<Model>>,
      initialModel: Model,
      factory: SystemFactory,
      ltlProperty: LTLFormula<Model>,
      maxSteps: nat)
      requires cmds.Valid()
      requires WellFormedFormula(ltlProperty)
      ensures fresh(this)
      ensures this.cmds == cmds
      ensures Valid()
    {
      this.cmds := cmds;
      this.initialModel := initialModel;
      this.factory := factory;
      this.ltlProperty := ltlProperty;
      this.maxSteps := maxSteps;
      this.lastFailureTags := {};
      this.lastCommandTrace := [];
      this.repr := {this} + {cmds.internalFunction} + cmds.internalFunction.repr;
    }

    ghost predicate Valid()
      reads this, repr
      ensures Valid() ==> this in repr
    {
      this in repr
      && cmds.internalFunction in repr
      && cmds.internalFunction.repr <= repr
      && this !in cmds.internalFunction.repr
      && this.repr == {this} + {cmds.internalFunction} + cmds.internalFunction.repr
      && cmds.Valid()
      && WellFormedFormula(ltlProperty)
    }

    method  Apply(tc: TestCase) returns (result: TestResult<()>)
      requires Valid()
      requires tc.Valid()
      requires this.repr !! tc.repr
      modifies tc, tc.random, this
      ensures Valid()
      ensures this.repr == old(this.repr)
      ensures this.cmds == old(this.cmds)
      ensures this.ltlProperty == old(this.ltlProperty)
      decreases this.repr
    {
      var sys := factory.Make();
      var m: Model := initialModel;
      var residual: LTLFormula<Model> := Step(ltlProperty, m);
      var step: nat := 0;
      var commandTrace: seq<string> := [];

      while step < maxSteps && !isDetermined(residual)
        invariant Valid()
        invariant tc.Valid()
        invariant tc.random == old(tc.random)
        invariant this.repr !! tc.repr
        invariant WellFormedFormula(residual)
        invariant this.repr == old(this.repr)
        invariant this.cmds == old(this.cmds)
        invariant this.ltlProperty == old(this.ltlProperty)
        decreases maxSteps - step
      {
        // cmds.internalFunction.repr <= this.repr (from Valid()), and
        // this.repr !! tc.repr (loop invariant) → cmds.internalFunction.repr !! tc.repr.
        assert cmds.internalFunction.repr <= this.repr;
        assert cmds.internalFunction.repr !! tc.repr;
        var cmd := tc.Any(cmds);
        if cmd.check(m) {
          var m' := cmd.run(m, sys);
          commandTrace := commandTrace + [cmd.toString()];
          m := m';
          // After the very first Step, the residual is wrapped in a Next
          // operator. StepResidual unwraps it and applies the next state in
          // one shot; plain Step would leave it stuck.
          if isGuarded(residual) {
            residual := StepResidual(residual, m);
          } else {
            residual := Step(residual, m);
          }
        }
        step := step + 1;
      }

      var evaluated := EvaluateValidity(residual);
      var validity := evaluated.0;
      var tags := evaluated.1;
      this.lastFailureTags := tags;
      this.lastCommandTrace := commandTrace;

      if validity.value {
        result := new TestResult<()>(None, Some(()));
      } else {
        result := new TestResult<()>(Some(INTERESTING), Some(()));
      }
    }
  }

  // Top-level stateful runner. Builds the per-test ModelTestFunction, runs
  // it inside Minithesis's TestingState (so we benefit from generation +
  // shrink-on-choices), then prints a summary keyed by the user's `name`.
  method  RunModelTest<Model(!new)>(
    name: string,
    cmds: Arbitrary<Command<Model>>,
    ltlProperty: LTLFormula<Model>,
    initialModel: Model,
    factory: SystemFactory,
    maxSteps: nat)
    requires cmds.Valid()
    requires WellFormedFormula(ltlProperty)
    requires 0 < maxSteps
    decreases 0
  {
    var mtf := new ModelTestFunction<Model>(cmds, initialModel, factory, ltlProperty, maxSteps);
    var rng := new M.SimpleRandomGen();
    var state := new M.TestingState<()>(rng, mtf, 100);
    state.Run();

    var res := state.GetResult();
    var valid := state.GetValidTestCases();
    match res {
      case None =>
        print "[", name, "] PASS (", valid, " valid runs)\n";
      case Some(choices) =>
        print "[", name, "] FAIL\n";
        print "  violated tags: ", TagsToString(mtf.lastFailureTags), "\n";
        print "  commands: [", StringJoin(mtf.lastCommandTrace, ", "), "]\n";
        print "  minimised choices: ", choices, "\n";
    }
  }
}
