import Applications.FRP.RegionalAdmission

/-! Independent observations and separating clients for regional compilation. -/
namespace FRPSpec.Regional
open Progress Progress.Feedback Applications.Circuits

/-- The existing function-target reactive compiler and circuit delay agree;
this specialization keeps both native interfaces available. -/
theorem function_circuit_delay : FiniteDelay.machine = Indefinite.delay.machine :=
  FiniteDelay.correct

example (s : Bool) (xs : List Bool) :
    run FiniteDelay.machine.mealy s xs = run Indefinite.delay.machine.mealy s xs := by
  rw [function_circuit_delay]

/-- Useful for continued runs; this does not replay any processed prefix. -/
def resumeState : (c : Cut) → Bool → (compile c).State
  | .fused, b => (⟨⟩,(b,⟨⟩))
  | .split, b => (⟨⟩,(b,⟨⟩))
  | .checked, b => (((⟨⟩,⟨⟩),⟨⟩),(b,⟨⟩))

theorem resume_logical (c : Cut) (b : Bool) : logical c (resumeState c b) = b := by
  cases c <;> rfl

theorem parallel_correct (c : Cut) (s : (compile c).State) (xs : List (Input × Bool)) :
    (run (parallel c).machine.mealy (s,⟨⟩) xs).1 =
      (run native.mealy (logical c s) (xs.map Prod.fst)).1.zip (xs.map Prod.snd) ∧
    logical c (run (parallel c).machine.mealy (s,⟨⟩) xs).2.1 =
      (run native.mealy (logical c s) (xs.map Prod.fst)).2 := by
  have h := run_par (compile c).machine (Feedback.pure (id : Bool → Bool)) s PUnit.unit xs
  rw [run_pure] at h
  simp only [List.map_id] at h
  constructor
  · exact (congrArg Prod.fst h).trans
      (congrArg (fun ys => ys.zip (xs.map Prod.snd)) (continuation c s _).1)
  · exact (congrArg (fun z => logical c z.2.1) h).trans (continuation c s _).2

def sideFixtures : List (Input × Bool) :=
  [(.inl true,false),(.inr (false,true),true),(.inr (true,false),true),(.inl false,false)]

theorem parallel_fixture (c : Cut) :
    (run (parallel c).machine.mealy ((compile c).machine.initial,⟨⟩) sideFixtures).1 =
      [(true,false),(false,true),(true,true),(false,false)] := by
  rw [(parallel_correct c _ _).1,initial_correct]
  rfl

/-- Both regions receive the same immutable source input through an explicit
copy node. Their delayed states remain separate. -/
def shared (c : Cut) : Plan Input (Bool × Bool) :=
  .seq .duplicate (.par (compile c) .rich)

theorem shared_step (c : Cut) (s : (compile c).State) (x : Input) :
    ((shared c).machine.step (x,(⟨⟩,(s,⟨⟩)))).1 =
      (!logical c s,Rich.oracle x) := by
  change (((compile c).machine.step (x,s)).1,Rich.execute x) = _
  exact Prod.ext (step_correct c s x).1 (Rich.correct x)

inductive Command where
  | tick (x : Input)
  | query

/-- Queries observe retained logical state. Only ticks advance the executor. -/
def command (c : Cut) (s : (compile c).State) : Command → (Bool ⊕ Bool) × (compile c).State
  | .query => (.inr (logical c s),s)
  | .tick x => let next := (compile c).machine.step (x,s); (.inl next.1,next.2)

theorem query_inert (c : Cut) (s : (compile c).State) :
    command c s .query = (.inr (logical c s),s) := rfl

theorem query_tick (c : Cut) (s : (compile c).State) (x : Input) :
    command c (command c s .query).2 (.tick x) = command c s (.tick x) := rfl

/-- Resetting state or moving negation across an unchanged seed breaks the source. -/
theorem reset_control :
    (run native.mealy false [.inl true,.inl false]).1 ≠
      [.inl true,.inl false].map (fun x => (native.step (x,false)).1) := by decide

def movedNegation : Initialized Input Bool Bool :=
  ⟨fun (x,s) => (s,!(Rich.oracle x)),false⟩
example : (run movedNegation.mealy false [.inl true]).1 ≠
    (run native.mealy false [.inl true]).1 := by decide

example : (run native.mealy false fixtures.reverse).1 ≠
    (run native.mealy false fixtures).1 := by decide

example : [(true,false),(false,true)].map (fun p => (p.2,p.1)) ≠
    [(true,false),(false,true)] := by decide

/-- Resource numbers are reductions of the compiled syntax and boundary schedule. -/
example : Rich.workBound Rich.code = 18 ∧ Rich.arena Rich.code = 133 := by decide

example (c : Cut) : (assessAdmission (.regional c) (.bounded (compile c).storage)).status = .accepted :=
  (admitted_capacity c _).2 (Nat.le_refl _)
example (c : Cut) : (assessAdmission (.regional c) (.bounded 0)).status = .rejected := by
  cases c <;> decide

/-- Resource clients consume an execution derivation, not merely a bound label. -/
example (c : Cut) (x : Input) (s : (compile c).State) :
    ∃ trace, Plan.SpaceRuns (compile c) x s ((compile c).machine.step (x,s)) trace ∧
      ∀ live ∈ trace, (compile c).retained + live ≤ (compile c).storage :=
  (compile c).sufficient_storage (by cases c <;> rfl) _ (Nat.le_refl _) x s

/-- Actual selected-arm allocations differ, while one static arena bounds both. -/
example : Rich.allocations Rich.code ((),Sum.inl false) ≠
    Rich.allocations Rich.code ((),Sum.inr (true,false)) := by decide
example : 0 < (Rich.allocations Rich.code ((),Sum.inl false)).sum := by decide

/-- The enclosing capacity failure is witnessed by actual live observations. -/
example : ¬ ∀ live ∈ (Plan.seq .side .bareNegate).liveTrace false (⟨⟩,⟨⟩), live ≤ 3 := by
  decide

/-- A function-executable growing state has no uniform retained-list bound. -/
def growing : Initialized Bool Bool (List Bool) :=
  ⟨fun (b,s) => (b,b::s),[]⟩

theorem growing_length (xs : List Bool) (s : List Bool) :
    (run growing.mealy s xs).2.length = s.length + xs.length := by
  induction xs generalizing s with
  | nil => simp [run]
  | cons x xs ih =>
    change (run growing.mealy (x::s) xs).2.length = _
    rw [ih]
    simp
    omega

theorem growing_unbounded (bound : Nat) :
    ∃ xs, bound < (run growing.mealy [] xs).2.length := by
  refine ⟨List.replicate (bound+1) false,?_⟩
  rw [growing_length]
  simp

end FRPSpec.Regional
