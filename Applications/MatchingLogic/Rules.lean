import Applications.MatchingLogic.Semantics

/-! The selected rules of Figure 5 of Roșu (2017). Specification assumptions
are globally valid. This datatype does not claim completeness. -/
namespace MatchingLogic
inductive Propositional where
  | atom : Nat → Propositional
  | neg : Propositional → Propositional
  | conj : Propositional → Propositional → Propositional
  | imp : Propositional → Propositional → Propositional

def Propositional.Holds (v : Nat → Prop) : Propositional → Prop
  | .atom i => v i
  | .neg p => ¬p.Holds v
  | .conj p q => p.Holds v ∧ q.Holds v
  | .imp p q => p.Holds v → q.Holds v

def Propositional.instantiate (v : Nat → Pattern Γ s) : Propositional → Pattern Γ s
  | .atom i => v i
  | .neg p => .neg (p.instantiate v)
  | .conj p q => .conj (p.instantiate v) (q.instantiate v)
  | .imp p q => (p.instantiate v).imp (q.instantiate v)

theorem Propositional.eval_instantiate (M : Model) (p : Propositional)
    (v : Nat → Pattern Γ s) (ρ : Valuation M Γ) (d : M.Carrier s) :
    d ∈ eval M (p.instantiate v) ρ ↔ p.Holds (fun i => d ∈ eval M (v i) ρ) := by
  induction p with
  | atom i => rfl
  | neg p ih => exact not_congr ih
  | conj p q ihp ihq => exact and_congr ihp ihq
  | imp p q ihp ihq => simpa only [instantiate, mem_eval_imp, Holds] using imp_congr ihp ihq

abbrev Specification := ∀ {Γ s}, Pattern Γ s → Prop
inductive Derives (A : Specification) : {Γ : Context} → {s : SortCode} → Pattern Γ s → Type
  | specAxiom (p : Pattern Γ s) : A p → Derives A p
  | propositional (p : Propositional) (v : Nat → Pattern Γ s)
      (tautology : ∀ truth : Nat → Prop, p.Holds truth) : Derives A (p.instantiate v)
  | mp : Derives A (p.imp q) → Derives A p → Derives A q
  | generalize : Derives A p → Derives A p.all
  | functionalSubstitution (p : Pattern (t :: Γ) s) (q : Pattern Γ t) :
      Derives A ((p.all.conj (q.functional s)).imp (p.substOne q))
  | equalityIntroduction (p : Pattern Γ t) (s : SortCode) : Derives A (p.equal s p)
  | equalityElimination (p : Pattern (t :: Γ) s) (q r : Pattern Γ t) :
      Derives A (((q.equal s r).conj (p.substOne q)).imp (p.substOne r))

theorem Derives.sound (M : Model) (axioms : ∀ {Γ s} (p : Pattern Γ s), A p → Valid M p)
    (h : Derives A p) : Valid M p := by
  induction h with
  | specAxiom p hp => exact axioms p hp
  | propositional p v ht =>
    rw [valid_iff]
    intro ρ d
    exact (p.eval_instantiate M v ρ d).mpr (ht _)
  | mp _ _ himp hp =>
    rw [valid_iff] at himp hp ⊢
    intro ρ d
    exact (mem_eval_imp ..).mp (himp ρ d) (hp ρ d)
  | generalize _ ih =>
    rw [valid_iff] at ih ⊢
    intro ρ d
    exact (mem_eval_all ..).mpr (fun a => ih (ρ.extend a) d)
  | functionalSubstitution p q =>
    rw [valid_iff]
    intro ρ d
    apply (mem_eval_imp ..).mpr
    rintro ⟨ha,hf⟩
    obtain ⟨a,he⟩ := (mem_eval_functional ..).mp hf
    rw [eval_substOne M p q ρ a he]
    exact (mem_eval_all ..).mp ha a
  | equalityIntroduction p s =>
    rw [valid_iff]
    intro ρ d
    exact (mem_eval_equal ..).mpr rfl
  | equalityElimination p q r =>
    rw [valid_iff]
    intro ρ d
    apply (mem_eval_imp ..).mpr
    rintro ⟨he,hp⟩
    rw [← eval_substOne_congr M p q r ρ ((mem_eval_equal ..).mp he)]
    exact hp

/-- A derived propositional step, not an extra semantic admission rule. -/
def Derives.conj {Γ : Context} {s : SortCode} {p q : Pattern Γ s} (hp : Derives A p) (hq : Derives A q) : Derives A (p.conj q) := by
  let f : Propositional := .imp (.atom 0) (.imp (.atom 1) (.conj (.atom 0) (.atom 1)))
  let v : Nat → Pattern Γ s := fun i => if i = 0 then p else q
  have ht : ∀ truth, f.Holds truth := by intro truth; exact fun a b => ⟨a,b⟩
  have h := Derives.propositional (A := A) f v ht
  exact .mp (.mp h hp) hq
end MatchingLogic
