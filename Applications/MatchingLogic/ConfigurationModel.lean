import Applications.MatchingLogic.Configuration
import Applications.MatchingLogic.Rules

namespace MatchingLogic.Configuration

abbrev Carrier : SortCode → Type
  | .nat => Nat
  | .cfg => Cfg

def symbolMeaning : Symbol s t → Carrier s → Set (Carrier t)
  | .succ, n => {n+1}
  | .run, n => {Cfg.run n}
  | .done, n => {Cfg.done n}
  | .step, c => outcomes c
  | .defined _ _, _ => Set.univ

abbrev model : Model where
  Carrier := Carrier
  nonempty s := by cases s; exact ⟨0⟩; exact ⟨.run 0⟩
  zero := {0}
  symbol := symbolMeaning
  defined _ _ _ := rfl

def emptyVal : Valuation model [] := fun v => nomatch v

def rhs (p : Pattern Γ .nat) : Pattern Γ .cfg :=
  (Pattern.app .done p).disj (.app .done (.app .succ p))
def outcomePattern (p : Pattern Γ .nat) : Pattern Γ .cfg :=
  (Pattern.app .step (.app .run p)).equal .cfg (rhs p)

@[simp] theorem eval_zero (ρ : Valuation model Γ) : eval model .zero ρ = {0} := rfl
@[simp] theorem eval_succ (p : Pattern Γ .nat) (ρ : Valuation model Γ) :
    eval model (.app .succ p) ρ = Nat.succ '' eval model p ρ := by
  ext d
  simp [eval, model, symbolMeaning, Set.mem_image, eq_comm]
@[simp] theorem eval_run (p : Pattern Γ .nat) (ρ : Valuation model Γ) :
    eval model (.app .run p) ρ = Cfg.run '' eval model p ρ := by
  ext d
  simp [eval, model, symbolMeaning, Set.mem_image, eq_comm]
@[simp] theorem eval_done (p : Pattern Γ .nat) (ρ : Valuation model Γ) :
    eval model (.app .done p) ρ = Cfg.done '' eval model p ρ := by
  ext d
  simp [eval, model, symbolMeaning, Set.mem_image, eq_comm]
@[simp] theorem eval_step (p : Pattern Γ .cfg) (ρ : Valuation model Γ) :
    eval model (.app .step p) ρ = post (eval model p ρ) := rfl

/-- The whole symbolic outcome set agrees with the independent native relation. -/
theorem symbolic_outcomes (v : Var Γ .nat) (ρ : Valuation model Γ) :
    eval model (.app .step (.app .run (.var v))) ρ = outcomes (.run (ρ v)) := by
  ext d
  simp [eval, model, symbolMeaning]

theorem symbolic_exact (v : Var Γ .nat) (ρ : Valuation model Γ) :
    eval model (.app .step (.app .run (.var v))) ρ = {.done (ρ v),.done (ρ v+1)} := by
  rw [symbolic_outcomes, outcomes_run]

theorem symbolic_terminal (v : Var Γ .nat) (ρ : Valuation model Γ) :
    eval model (.app .step (.app .done (.var v))) ρ = ∅ := by
  ext d
  simp [eval, model, symbolMeaning]

theorem terminal_family (ρ : Valuation model Γ) :
    eval model (.ex .nat (.app .step (.app .run (.var .here)))) ρ = {c | ∃ n, c = .done n} := by
  ext c
  change (∃ n : Nat, c ∈ eval model (.app .step (.app .run (.var .here))) (ρ.extend n)) ↔ _
  constructor
  · rintro ⟨n,h⟩
    rw [symbolic_exact (.here : Var (.nat :: Γ) .nat) (ρ.extend n)] at h
    rcases h with h | h
    · exact ⟨n,h⟩
    · exact ⟨n+1,h⟩
  · rintro ⟨n,rfl⟩
    refine ⟨n,?_⟩
    rw [symbolic_exact (.here : Var (.nat :: Γ) .nat) (ρ.extend n)]
    exact Or.inl rfl

theorem symbolic_excluded (v : Var Γ .nat) (ρ : Valuation model Γ) :
    Cfg.done (ρ v+2) ∉ eval model (.app .step (.app .run (.var v))) ρ := by
  rw [symbolic_outcomes]
  exact excluded _

theorem safety_iff (v : Var Γ .nat) (ρ : Valuation model Γ) (B : Set Cfg) :
    (eval model (.app .step (.app .run (.var v))) ρ ⊆ B) ↔ Safe (.run (ρ v)) B := by
  rw [symbolic_outcomes]
  rfl

inductive Axiom : {Γ : Context} → {s : SortCode} → Pattern Γ s → Prop
  | outcomes (v : Var Γ .nat) : Axiom (outcomePattern (.var v))
  | zero_functional : Axiom ((Pattern.zero : Pattern Γ .nat).functional .cfg)

theorem axioms_valid (p : Pattern Γ s) (h : Axiom p) : Valid model p := by
  cases h with
  | outcomes v =>
    rw [valid_iff]
    intro ρ d
    apply (mem_eval_equal ..).mpr
    rw [symbolic_exact]
    ext c
    unfold rhs
    rw [mem_eval_disj model (.app .done (.var v)) (.app .done (.app .succ (.var v))) ρ c]
    simp [eval, model, symbolMeaning]
  | zero_functional =>
    rw [valid_iff]
    intro ρ d
    exact (mem_eval_functional ..).mpr ⟨0,rfl⟩

def initialStep : Pattern [] .cfg := .app .step (.app .run .zero)
def initialResults : Pattern [] .cfg := rhs .zero

/-- Report inference 1: global specification validity permits generalization. -/
def inferenceGeneralized : Derives Axiom (outcomePattern (.var (.here : Var [.nat] .nat))).all :=
  .generalize (.specAxiom _ (.outcomes .here))

/-- Report inference 2: the singleton premise is supplied by an explicit axiom. -/
def inferenceAtZero : Derives Axiom (initialStep.equal .cfg initialResults) :=
  .mp (.functionalSubstitution (outcomePattern (.var (.here : Var [.nat] .nat))) .zero)
    (inferenceGeneralized.conj (.specAxiom _ .zero_functional))

/-- Report inference 3: equality symmetry derived through the selected rules. -/
def inferenceSymmetry : Derives Axiom (initialResults.equal .cfg initialStep) :=
  .mp (.equalityElimination
      ((Pattern.var (.here : Var [.cfg] .cfg)).equal .cfg (initialStep.rename Var.there))
      initialStep initialResults)
    (inferenceAtZero.conj (.equalityIntroduction initialStep .cfg))

theorem inference_valid : Valid model (initialResults.equal .cfg initialStep) :=
  inferenceSymmetry.sound model axioms_valid

theorem initial_exact : eval model initialStep emptyVal = {.done 0,.done 1} := by
  ext d
  simp [initialStep, eval, model, symbolMeaning]

theorem initial_nonempty : (eval model initialStep emptyVal).Nonempty := by
  rw [initial_exact]
  exact ⟨.done 0,by simp⟩

theorem initial_not_singleton (a : Cfg) : eval model initialStep emptyVal ≠ {a} := by
  rw [initial_exact]
  intro h
  have h0 : Cfg.done 0 ∈ ({a} : Set Cfg) := by rw [← h]; simp
  have h1 : Cfg.done 1 ∈ ({a} : Set Cfg) := by rw [← h]; simp
  have h01 : Cfg.done 0 = Cfg.done 1 := h0.trans h1.symm
  cases h01

/-- Nonemptiness cannot replace functionality; this is not the empty-set case. -/
theorem unrestricted_substitution_rejected :
    Valid model ((Pattern.var (.here : Var [.cfg] .cfg)).functional .cfg).all ∧
      eval model (initialStep.functional .cfg) emptyVal = ∅ := by
  constructor
  · rw [valid_iff]
    intro ρ d
    apply (mem_eval_all ..).mpr
    intro a
    exact (mem_eval_functional ..).mpr ⟨a,rfl⟩
  · ext d
    change (d ∈ eval model (initialStep.functional .cfg) emptyVal) ↔ False
    rw [mem_eval_functional model initialStep emptyVal d]
    simpa using (not_exists.mpr initial_not_singleton)

theorem terminal_not_singleton (a : Cfg) :
    eval model (.app .step (.app .done .zero)) emptyVal ≠ {a} := by
  have he : eval model (.app .step (.app .done .zero)) emptyVal = ∅ := by
    ext d
    simp [eval, model, symbolMeaning]
  rw [he]
  simp

end MatchingLogic.Configuration
