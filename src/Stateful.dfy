include "./Arbitrary.dfy"
include "./DafnyCheck.dfy"
include "./LTL.dfy"

// Stateful (model-based) property testing on top of Minithesis's TestingState,
// using the LTL formula evaluator from LTL.dfy for temporal properties.
//
// The runner drives a sequence of `Command<Model>` against a fresh, mutable
// `System<Model>` per test case. After each accepted command it Sample()s the
// system into an immutable Model and Step-s the LTL formula. It stops when:
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
  import opened RunConfig
  import Reporting

  // Predicate-based property: takes one input drawn from an Arbitrary<T>.
  type PropertyTest<!T> = T -> bool

  // Outcome of one model-test case. Carried as the TestResult payload (the
  // TestFunction's type parameter) rather than stashed in instance fields, so
  // it rides along with the minimal counterexample that TestingState tracks in
  // `bestResult` — instead of being overwritten by every later shrink probe.
  datatype ModelTestOutcome = ModelTestOutcome(tags: set<string>, commandTrace: seq<string>)

  // The mutable system under test. Mirrors the `Transformable<T>` trait that
  // `Arbitrary<T>` wraps: it owns its heap footprint `repr` and a `Valid()`
  // invariant, so commands can mutate it *in place* via `modifies sys.repr`
  // (a generic type parameter could not appear in a modifies clause; a trait
  // instance is a reference, so `sys.repr` can). Concrete SUTs extend this,
  // add their mutable state to `repr`, and implement `Sample` to project the
  // current state into an immutable Model for the LTL property.
  trait System<Model(!new)> {
    ghost var repr: set<object>

    ghost predicate Valid()
      reads this, repr
      ensures Valid() ==> this in repr

    method Sample() returns (m: Model)
      requires Valid()
      ensures Valid()
      decreases 0
  }

  // A command in a model-based test. `check` is the precondition over the
  // current model state; `run` mutates the system in place; `toString` is for
  // failure reporting. A command typically downcasts `sys as ConcreteSUT` in
  // its body to call the SUT's methods. `run` may grow `sys.repr` (e.g. allocate
  // internal nodes) as long as the additions are fresh and `Valid()` is restored.
  //
  // The Model is not produced by `run`; after every accepted command the runner
  // calls `sys.Sample()` to obtain the next Model, on which the LTL property is
  // stepped.
  trait Command<Model(!new)> {
    ghost var repr: set<Command<Model>>

    ghost predicate Valid()
      reads this, repr
      ensures Valid() ==> this in repr

    predicate check(m: Model)
    method run(m: Model, sys: System<Model>)
      requires check(m)
      requires sys.Valid()
      modifies sys.repr
      ensures sys.Valid()
      ensures fresh(sys.repr - old(sys.repr))
      decreases 0
    // `reads this` so a command can label itself from its own fields (e.g. the
    // argument it enqueues); the runner calls this from a method, so the read is
    // unconstrained at the call site.
    function toString(): string
      reads this
  }

  // Factory that allocates a fresh, valid System under test for each test case
  // so shrink/replay starts from a clean slate. The returned system and its
  // whole `repr` must be freshly allocated.
  trait SystemFactory<Model(!new)> {
    method Make() returns (sys: System<Model>)
      ensures fresh(sys)
      ensures fresh(sys.repr)
      ensures sys.Valid()
      decreases 0
  }

  // Top-level predicate-based RunTest — delegates straight to DafnyCheck.
  // Returns true iff every generated case passed.
  method RunTest<T(!new)>(test: PropertyTest<T>, arb: Arbitrary<T>, name: string) returns (passed: bool)
    requires arb.Valid()
  {
    passed := M.RunTest(test, arb, name);
  }

  // The model-test runner wraps one test case (one execution of a randomly
  // generated command sequence) as a TestFunction. Many such test cases are
  // run by the underlying TestingState.
  //
  // Per Apply: draw commands one at a time from `cmds`, skip those whose
  // check(m) is false (the user-selected policy), execute the ones that pass,
  // Step the LTL formula, stop when determined or out of budget. The violated
  // tags + command trace are returned in the TestResult's ModelTestOutcome
  // payload, so the outer runner reads them off `bestResult` (the minimised
  // counterexample) rather than off mutable instance state.
  class ModelTestFunction<Model(!new)> extends M.TestFunction<ModelTestOutcome> {
    var cmds: Arbitrary<Command<Model>>
    var initialModel: Model
    var factory: SystemFactory<Model>
    var ltlProperty: LTLFormula<Model>
    var maxSteps: nat

    constructor(
      cmds: Arbitrary<Command<Model>>,
      initialModel: Model,
      factory: SystemFactory<Model>,
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

    method  Apply(tc: TestCase) returns (result: TestResult<ModelTestOutcome>)
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
        // `sys` is allocated inside Apply and only ever mutated in place, so its
        // whole footprint stays fresh and disjoint from tc/this — that is what
        // lets `cmd.run` modify `sys.repr` without it being in Apply's modifies
        // clause, and keeps the tc/this invariants stable across the mutation.
        invariant sys.Valid()
        invariant fresh(sys.repr)
        invariant sys.repr !! tc.repr
        invariant sys.repr !! this.repr
        decreases maxSteps - step
      {
        // cmds.internalFunction.repr <= this.repr (from Valid()), and
        // this.repr !! tc.repr (loop invariant) → cmds.internalFunction.repr !! tc.repr.
        assert cmds.internalFunction.repr <= this.repr;
        assert cmds.internalFunction.repr !! tc.repr;
        var cmd := tc.Any(cmds);
        if cmd.check(m) {
          // Mutate the System in place, then sample it back into a Model. The
          // LTL formula is stepped on the sampled Model.
          cmd.run(m, sys);
          m := sys.Sample();
          commandTrace := commandTrace + [cmd.toString()];
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
      var outcome := ModelTestOutcome(tags, commandTrace);

      if validity.value {
        result := new TestResult<ModelTestOutcome>(None, Some(outcome));
      } else {
        result := new TestResult<ModelTestOutcome>(Some(INTERESTING), Some(outcome));
      }
    }
  }

  // Top-level stateful runner. Builds the per-test ModelTestFunction, runs
  // it inside Minithesis's TestingState (so we benefit from generation +
  // shrink-on-choices), then prints a summary keyed by the user's `name`.
  // Default-config model test: 100 runs, seed 42, color on, Low verbosity.
  method RunModelTest<Model(!new)>(
    name: string,
    cmds: Arbitrary<Command<Model>>,
    ltlProperty: LTLFormula<Model>,
    initialModel: Model,
    factory: SystemFactory<Model>,
    maxSteps: nat)
    returns (passed: bool)
    requires cmds.Valid()
    requires WellFormedFormula(ltlProperty)
    requires 0 < maxSteps
    decreases 0
  {
    passed := RunModelTestWithConfig(name, cmds, ltlProperty, initialModel, factory, maxSteps,
                                     100, 42, true, Low);
  }

  // Config-driven model test. Per the v1 scope, model tests honor run count,
  // seed, color, and verbosity but not the classifier/examples of RunConfig
  // (commands aren't readily classifiable), so those knobs are explicit params
  // rather than a RunConfig value.
  method RunModelTestWithConfig<Model(!new)>(
    name: string,
    cmds: Arbitrary<Command<Model>>,
    ltlProperty: LTLFormula<Model>,
    initialModel: Model,
    factory: SystemFactory<Model>,
    maxSteps: nat,
    numRuns: nat,
    seed: bv64,
    useColor: bool,
    verbosity: Verbosity)
    returns (passed: bool)
    requires cmds.Valid()
    requires WellFormedFormula(ltlProperty)
    requires 0 < maxSteps
    decreases 0
  {
    var mtf := new ModelTestFunction<Model>(cmds, initialModel, factory, ltlProperty, maxSteps);
    var rng := new M.SimpleRandomGen(seed);
    var nr := if numRuns == 0 then 1 else numRuns;
    var state := new M.TestingState<ModelTestOutcome>(rng, mtf, nr, seed, None, verbosity, useColor);
    state.Run();

    var res := state.GetResult();
    var valid := state.GetValidTestCases();
    // bestResult is tracked in lockstep with the minimised `result` (set in
    // ApplyTestFunction and Consider), so it carries the violated tags + command
    // trace of the *minimal* counterexample, not the last shrink probe.
    var best := state.GetBestResult();
    match res {
      case None =>
        if valid == 0 {
          Reporting.ReportUnsatisfiable(name, useColor, verbosity);
          passed := false;
        } else {
          Reporting.ReportSuccess(name, valid, useColor, verbosity);
          passed := true;
        }
      case Some(choices) =>
        passed := false;
        Reporting.ReportFailure(name, useColor, verbosity);
        if verbosity != Off {
          match best {
            case Some(outcome) =>
              print "  violated tags: ", TagsToString(outcome.tags), "\n";
              print "  commands: [", StringJoin(outcome.commandTrace, ", "), "]\n";
            case None =>
          }
          print "  minimised choices: ", choices, "\n";
        }
    }
  }
}
