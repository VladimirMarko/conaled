import Applications.FRP.RegionalSelectionCosts
import Examples.RegionalPlans

/-! The joint native oracle is independent of policy and regional cuts. -/
namespace FRPSpec.Regional.Selection
open Progress Progress.Feedback Optimization.Choice

def inputs : List (Input × Input) :=
  [(.inl true,.inl false),(.inr (false,true),.inr (true,false)),(.inl false,.inl true)]

def Sites.resume (c : Sites) (s : Bool × Bool) : c.plan.State :=
  (resumeState c.left s.1,resumeState c.right s.2)
theorem Sites.observe_resume (c : Sites) (s : Bool × Bool) : c.observe (c.resume s) = s :=
  Prod.ext (resume_logical c.left s.1) (resume_logical c.right s.2)

theorem native_fixture (c : Sites) :
    (run c.plan.machine.mealy c.plan.machine.initial inputs).1 =
      [(true,true),(false,true),(true,false)] ∧
    c.observe (run c.plan.machine.mealy c.plan.machine.initial inputs).2 = (false,true) := by
  have h := c.continuation c.plan.machine.initial inputs
  rw [c.initial_correct] at h
  exact h

theorem unequal_fixture (c : Sites) :
    (run c.plan.machine.mealy (c.resume (true,false)) inputs).1 =
      [(false,true),(false,true),(true,false)] := by
  rw [(c.continuation _ _).1,c.observe_resume]
  rfl

def roomy : Requirements := {capacity := 10000}
def fusedSites : Sites := ⟨.fused,.fused⟩
def splitSites : Sites := ⟨.split,.split⟩
def checkedSites : Sites := ⟨.checked,.checked⟩

/-- Synthetic timings distinguish policy correctness, not empirical speed. -/
def synthetic (r : Requirements) (w : String) (winner : Sites)
    (cs : List Sites := catalog) : Epoch :=
  let ctx := admittedContext cs (eligible r) Sites.name (context r w)
  ⟨ctx,1,ctx.catalog.map fun name => ⟨name,0,if name = winner.name then 1 else 100,true,ctx⟩⟩

example : (synthetic roomy "fixture" checkedSites).complete
    (admittedContext catalog (eligible roomy) Sites.name (context roomy "fixture")) 1 = true := by decide
example : select roomy "fixture" (some (synthetic roomy "fixture" checkedSites)) = some checkedSites := by decide
example : select roomy "fixture" (some (synthetic roomy "fixture" splitSites)) = some splitSites := by decide
example : select {capacity := 0} "fixture" none = none := by decide
example : withFallback roomy "fixture" none [] fusedSites = some fusedSites := by decide
example : withFallback {capacity := 0} "fixture" none [] fusedSites = none := by decide

/-- Both leaves fit this budget, but their enclosing product keeps both states,
the right input, composition frame and boundary copy live. -/
example : (compile Cut.fused).storage ≤ (compile Cut.fused).storage ∧
    ¬ fusedSites.plan.storage ≤ (compile Cut.fused).storage := by decide

example : (assess (.direct : Plan Input Bool) 10000).acceptedFlag = false := rfl
example : (assessAdmission .missingAdapter .semantic).status = .rejected := rfl
example : (Plan.bareNegate : Plan Bool Bool).work < Plan.negate.work ∧
    Plan.negate.work < (Plan.seq (.seq .encode .decode) .bareNegate).work :=
  conversion_reverses_cost

/-- A preprocessing call has no retained state and may choose independently.
This call does not rebind either stateful F/D/N session. -/
def preprocess (useCompiled : Bool) (x : Input) : Bool :=
  if useCompiled then Rich.execute x else Rich.oracle x
example (b : Bool) (x : Input) : preprocess b x = Rich.oracle x := by
  cases b <;> simp [preprocess,Rich.correct]

example : (Sites.plan ⟨.split,.checked⟩).storage = 144 ∧
    (Sites.plan ⟨.checked,.split⟩).storage = 147 := by decide
example : eligible {capacity := 145} ⟨.split,.checked⟩ ∧
    ¬ eligible {capacity := 145} ⟨.checked,.split⟩ := by decide

end FRPSpec.Regional.Selection
