import Applications.Elaboration.Syntax

/-! Explicit partial assignments and their meanings. Refinement preserves
already assigned values; constraint sets can be strengthened independently. -/
namespace Elaboration

inductive Obligation where
  | assigned : Nat → Obligation
  | universeZero : Nat → Obligation
  | metaEq : Nat → Nat → Obligation
  deriving DecidableEq, Repr

structure Assignment where
  metas : Nat → Option Nat
  level : Nat → Option Nat

def Assignment.value (θ : Assignment) (k : Nat) : Nat := (θ.metas k).getD 0

def Obligation.Holds (θ : Assignment) : Obligation → Prop
  | .assigned k => ∃ n, θ.metas k = some n
  | .universeZero k => θ.level k = some 0
  | .metaEq k n => θ.metas k = some n

def Solves (θ : Assignment) (cs : List Obligation) : Prop :=
  ∀ c ∈ cs, c.Holds θ

def Assignment.Refines (θ η : Assignment) : Prop :=
  (∀ k n, θ.metas k = some n → η.metas k = some n) ∧
  (∀ k n, θ.level k = some n → η.level k = some n)

theorem Assignment.Refines.refl (θ : Assignment) : θ.Refines θ := ⟨fun _ _ => id, fun _ _ => id⟩

theorem Assignment.Refines.trans {θ η ζ : Assignment}
    (h : θ.Refines η) (k : η.Refines ζ) : θ.Refines ζ :=
  ⟨fun i n hi => k.1 i n (h.1 i n hi), fun i n hi => k.2 i n (h.2 i n hi)⟩

theorem Obligation.Holds.refine {θ η : Assignment} (h : θ.Refines η)
    {c : Obligation} (hc : c.Holds θ) : c.Holds η := by
  cases c with
  | assigned k => obtain ⟨n, hn⟩ := hc; exact ⟨n, h.1 k n hn⟩
  | universeZero k => exact h.2 k 0 hc
  | metaEq k n => exact h.1 k n hc

theorem Solves.refine {θ η : Assignment} (h : θ.Refines η)
    {cs : List Obligation} (hc : Solves θ cs) : Solves η cs :=
  fun c hm => (hc c hm).refine h

@[simp] theorem solves_append (θ : Assignment) (a b : List Obligation) :
    Solves θ (a ++ b) ↔ Solves θ a ∧ Solves θ b := by
  simp only [Solves, List.mem_append, or_imp, forall_and]

/-- Constraint refinement means inclusion of solution sets, not equality of
search algorithms or a promise that the stronger problem is solvable. -/
def RefinesConstraints (a b : List Obligation) : Prop := ∀ θ, Solves θ b → Solves θ a

theorem refine_constraints_comp {a b c : List Obligation}
    (h : RefinesConstraints a b) (k : RefinesConstraints b c) : RefinesConstraints a c :=
  fun θ hc => h θ (k θ hc)

theorem add_constraints (a b : List Obligation) : RefinesConstraints a (a ++ b) :=
  fun θ h => (solves_append θ a b).mp h |>.1

def Source.requirements : Source Γ Δ t → List Obligation
  | .lit _ | .bound _ | .named _ => []
  | .hole k => [.assigned k]
  | .add a b => a.requirements ++ b.requirements
  | .vector u n a => .universeZero u :: (n.requirements ++ a.requirements)
  | .total p => p.requirements

/-- Target typing for open meta/universe assignments is separate from syntax's
intrinsic object sort. No default value is accepted as a solved metavariable. -/
def Core.Typed (θ : Assignment) : Core Γ Δ t → Prop
  | .numeral _ | .variable _ | .constant _ => True
  | .metavariable k => ∃ n, θ.metas k = some n
  | .plus a b => a.Typed θ ∧ b.Typed θ
  | .pack u n a => θ.level u = some 0 ∧ n.Typed θ ∧ a.Typed θ
  | .fold p => p.Typed θ

theorem lower_typed (s : Source Γ Δ t) (θ : Assignment) :
    (lower s).Typed θ ↔ Solves θ s.requirements := by
  induction s <;> simp_all [lower, Core.Typed, Source.requirements,
    Solves, Obligation.Holds, or_imp, forall_and]

/-- Solved terms are stable under further assignment refinement. -/
theorem Source.eval_refine (s : Source Γ Δ t) {θ η : Assignment}
    (h : θ.Refines η) (hs : Solves θ s.requirements) (ρ δ) :
    s.eval θ.value ρ δ = s.eval η.value ρ δ := by
  induction s with
  | lit | bound | named => rfl
  | hole k =>
    obtain ⟨n, hn⟩ := hs (.assigned k) (by simp [Source.requirements])
    simp [Source.eval, Assignment.value, hn, h.1 k n hn]
  | add a b ia ib =>
    have hab := (solves_append θ _ _).mp hs
    simp [Source.eval, ia hab.1, ib hab.2]
  | vector u n a iN iA =>
    have hn : Solves θ n.requirements := fun c hc => hs c (by simp [Source.requirements, hc])
    have ha : Solves θ a.requirements := fun c hc => hs c (by simp [Source.requirements, hc])
    simp [Source.eval, iN hn, iA ha]
  | total p ih => exact congrArg consume (ih hs)

/-- Intermediate solution spaces reuse the shared relational composition API. -/
def solutionRep (cs : List Obligation) : Relational.RelRep where
  R := Assignment
  S := Unit
  Rel θ _ := Solves θ cs

def refinementSquare (h : RefinesConstraints a b) :
    Relational.RelSquare (solutionRep b) (solutionRep a) where
  impl := id
  spec := id
  preserves := h _

theorem refinement_composes (h : RefinesConstraints a b) (k : RefinesConstraints b c) :
    Relational.compose (refinementSquare h) (refinementSquare k) =
      refinementSquare (refine_constraints_comp h k) :=
  Relational.RelSquare.ext (fun _ => rfl) (fun _ => rfl)

end Elaboration
