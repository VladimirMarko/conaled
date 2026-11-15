import Applications.FRP.RegionalSpace

/-! Admission for a supplied finite catalog. It does not infer boundedness of
arbitrary Lean functions, and ranking is deliberately outside this contract. -/
namespace FRPSpec.Regional
open Progress Progress.Feedback Applications.Circuits

inductive Route where
  | native
  | regional (cut : Cut)
  | circuitOnly
  | missingAdapter
  deriving DecidableEq, Repr
inductive Guarantee where
  | semantic
  | bounded (capacity : Nat)
  deriving DecidableEq, Repr
inductive Rejection where
  | residualSum
  | incompatiblePort
  | capacity (required available : Nat)
  deriving DecidableEq, Repr

/-- Bound admission also applies to compositions outside the three F/D/N cuts. -/
inductive Assessment (p : Plan A B) (capacity : Nat) where
  | accepted (analysis : p.analyzed = true) (fits : p.storage ≤ capacity)
  | rejected (analysis : p.analyzed = true) (exceeds : ¬ p.storage ≤ capacity)
  | unsupported (missing : p.analyzed = false)

def assess (p : Plan A B) (capacity : Nat) : Assessment p capacity :=
  if ha : p.analyzed = true then
    if hf : p.storage ≤ capacity then .accepted ha hf else .rejected ha hf
  else .unsupported (Bool.eq_false_iff.mpr ha)

def Assessment.acceptedFlag : Assessment p n → Bool
  | .accepted _ _ => true
  | _ => false

/-- A selected executable plan with its joint state interpretation. -/
structure Realization where
  plan : Plan Input Bool
  observe : plan.State → Bool
  initial : observe plan.machine.initial = false
  step : ∀ x s, (plan.machine.step (x,s)).1 = !observe s ∧
    observe (plan.machine.step (x,s)).2 = Rich.oracle x

def selected (c : Cut) : Realization :=
  ⟨compile c,logical c,initial_correct c,fun x s => step_correct c s x⟩
def directRealization : Realization := ⟨.direct,id,rfl,fun _ _ => ⟨rfl,rfl⟩⟩

/-- Certificates refer to the selected executor and declared arena schedule. -/
structure Bounded (r : Realization) (capacity : Nat) : Prop where
  analyzed : r.plan.analyzed = true
  fits : r.plan.storage ≤ capacity

inductive Evidence (r : Realization) : Guarantee → Prop where
  | semantic : Evidence r .semantic
  | bounded : Bounded r n → Evidence r (.bounded n)

inductive Admission (g : Guarantee) where
  | accepted (realization : Realization) (evidence : Evidence realization g)
  | rejected (reason : Rejection)
  | unsupportedAnalysis

def assessAdmission (route : Route) (g : Guarantee) : Admission g :=
  match route with
  | .circuitOnly => .rejected .residualSum
  | .missingAdapter => .rejected .incompatiblePort
  | .native => match g with
    | .semantic => .accepted directRealization .semantic
    | .bounded _ => .unsupportedAnalysis
  | .regional c => match g with
    | .semantic => .accepted (selected c) .semantic
    | .bounded n =>
      if h : (compile c).storage ≤ n then
        .accepted (selected c) (.bounded ⟨by cases c <;> rfl,h⟩)
      else .rejected (.capacity (compile c).storage n)

inductive Status where
  | accepted | rejected | unsupported
  deriving DecidableEq, Repr

def Admission.status : Admission g → Status
  | .accepted _ _ => .accepted
  | .rejected _ => .rejected
  | .unsupportedAnalysis => .unsupported

/-- Rejecting a bound does not reject the semantic meaning or the function route. -/
theorem unknown_is_not_impossible (n : Nat) :
    (assessAdmission .native .semantic).status = .accepted ∧
    (assessAdmission .native (.bounded n)).status = .unsupported := ⟨rfl,rfl⟩

theorem admitted_capacity (c : Cut) (n : Nat) :
    (assessAdmission (.regional c) (.bounded n)).status = .accepted ↔ (compile c).storage ≤ n := by
  simp only [assessAdmission]
  split <;> simp_all [Admission.status]

theorem semantic_preservation (r : Realization) (s : r.plan.State) (xs : List Input) :
    (run r.plan.machine.mealy s xs).1 = (run native.mealy (r.observe s) xs).1 ∧
    r.observe (run r.plan.machine.mealy s xs).2 =
      (run native.mealy (r.observe s) xs).2 := by
  have h := run_related r.plan.machine.mealy native.mealy Eq
    (fun t b => r.observe t = b) Eq
    (by intro x y t b hxy htb; subst y; subst b; exact r.step x t)
    (List.forall₂_same.mpr (fun _ _ => rfl) : List.Forall₂ Eq xs xs) (s := s) rfl
  exact ⟨by simpa only [List.forall₂_eq_eq_eq] using h.1,h.2⟩

theorem bounded_checkpoint (r : Realization) (h : Bounded r n) (live : Nat)
    (hlive : live ∈ r.plan.checkpoints) : r.plan.retained + live ≤ n :=
  (r.plan.checkpoint_bound live hlive).trans h.fits

theorem bounded_execution (r : Realization) (h : Bounded r capacity)
    (x : Input) (s : r.plan.State) :
    ∃ trace, Plan.SpaceRuns r.plan x s (r.plan.machine.step (x,s)) trace ∧
      ∀ live ∈ trace, r.plan.retained + live ≤ capacity :=
  r.plan.sufficient_storage h.analyzed capacity h.fits x s

/-- No queue is introduced: each finite input/scheduler/sink wait precedes the
next accepted tick. This does not assert progress for a blocked environment. -/
theorem bounded_service (r : Realization) (h : Bounded r n)
    (env : Indefinite.Program.Environment) (input : Stream Input) (deadline : Nat) :
    ∃ k, deadline < r.plan.starts env (k+1) ∧
      Plan.Round r.plan env k (input k) (state r.plan.machine input k)
        (r.plan.starts env k) (output r.plan.machine input k,state r.plan.machine input (k+1))
        (r.plan.starts env (k+1)) ∧
      r.plan.stepWork (input k) (state r.plan.machine input k) ≤ r.plan.work ∧
      ∀ live ∈ r.plan.liveTrace (input k) (state r.plan.machine input k),
        r.plan.retained + live ≤ n := by
  refine ⟨deadline,lt_of_lt_of_le (Nat.lt_succ_self deadline) (r.plan.starts_grow env _),
    r.plan.scheduled h.analyzed env input deadline,r.plan.stepWork_le _ _,?_⟩
  exact fun live hlive => (r.plan.live_bound _ _ live hlive).trans h.fits

/-- Existing finite-circuit service retains exactly its original assumptions. -/
theorem circuit_recovery (p : Indefinite.Program a b s)
    (env : Indefinite.Program.Environment) (input : Stream (FirstOrderCompiler.Val Bool a))
    (deadline : Nat) :
    ∃ k, deadline < p.starts env (k+1) ∧
      Indefinite.Program.Round p (env.inputWait k) (env.schedulerWait k) (env.sinkWait k)
        (p.starts env k) (input k) (state p.machine input k)
        (output p.machine input k) (state p.machine input (k+1)) (p.starts env (k+1)) :=
  p.productive env input deadline

/-- Direct and checked ports can coexist; an omitted conversion is rejected. -/
example : (assessAdmission .missingAdapter .semantic).status = .rejected := rfl
example : (assessAdmission .circuitOnly .semantic).status = .rejected := rfl
example : (assessAdmission (.regional .checked) .semantic).status = .accepted := rfl
example : Rich.analyzable Rich.closureCode = false ∧
    Rich.analyzable Rich.loweredCode = true := by decide

/-- Both leaf arenas fit alone. Their enclosing composition must retain the
boundary payload and frame while executing the second leaf. -/
theorem boundary_capacity :
    (Plan.side : Plan Bool Bool).storage ≤ 3 ∧
    (Plan.bareNegate : Plan Bool Bool).storage ≤ 3 ∧
    ¬ (Plan.seq .side .bareNegate : Plan Bool Bool).storage ≤ 3 := by decide

example : (assess (.side : Plan Bool Bool) 3).acceptedFlag = true ∧
    (assess (.bareNegate : Plan Bool Bool) 3).acceptedFlag = true ∧
    (assess (.seq .side .bareNegate : Plan Bool Bool) 3).acceptedFlag = false := by decide

/-- A cheaper direct gate loses after redundant encoding/validation and copies. -/
theorem conversion_reverses_cost :
    (Plan.bareNegate : Plan Bool Bool).work < Plan.negate.work ∧
    Plan.negate.work < (Plan.seq (.seq .encode .decode) .bareNegate).work := by decide

end FRPSpec.Regional
