import Mathlib.Data.Finset.Basic

/-! Fixed-basis finite Horn support, following the bounded construction in
`docs/research/atomic-base-support-construction.md`. Support carries no selected
proof data. Only atoms and implication are interpreted. -/
namespace SquareKit.HornSupport
universe u

structure Rule (Atom : Type u) where
  premises : Finset Atom
  conclusion : Atom
  deriving DecidableEq

abbrev Base (Atom : Type u) := Finset (Rule Atom)
abbrev Basis (Atom : Type u) := Set (Base Atom)

/-- No implicit assumptions: only rules with empty premises can start a proof. -/
inductive Derivable {Atom : Type u} (B : Base Atom) : Atom → Prop where
  | rule (r : Rule Atom) : r ∈ B →
      (∀ a ∈ r.premises, Derivable B a) → Derivable B r.conclusion

namespace Derivable
variable {Atom : Type u} {B D : Base Atom}

theorem weaken (h : B ⊆ D) {a} (d : Derivable B a) : Derivable D a := by
  induction d with
  | rule r hr _ ih => exact .rule r (h hr) ih

/-- Inductive closure under rules gives a useful way to refute derivability. -/
theorem invariant (P : Atom → Prop)
    (closed : ∀ r ∈ B, (∀ a ∈ r.premises, P a) → P r.conclusion)
    {a} (d : Derivable B a) : P a := by
  induction d with
  | rule r hr _ ih => exact closed r hr ih

@[simp] theorem not_empty {a : Atom} : ¬ Derivable (∅ : Base Atom) a := by
  intro d
  cases d with
  | rule r hr => simp at hr
end Derivable

inductive Formula (Atom : Type u) where
  | atom : Atom → Formula Atom
  | imp : Formula Atom → Formula Atom → Formula Atom
  deriving DecidableEq

/-- The same basis is used at every recursive call. The current base's membership
is required by the laws that use reflexivity, rather than hidden in atom support. -/
def Support {Atom : Type u} (K : Basis Atom) (B : Base Atom) : Formula Atom → Prop
  | .atom a => Derivable B a
  | .imp A C => ∀ D ∈ K, B ⊆ D → Support K D A → Support K D C

variable {Atom : Type u} {K : Basis Atom} {B D : Base Atom}

theorem persistence {A : Formula Atom} (h : B ⊆ D)
    (s : Support K B A) : Support K D A := by
  cases A with
  | atom a => exact s.weaken h
  | imp A C => exact fun E hE hDE => s E hE (Finset.Subset.trans h hDE)

/-- All context members must be supported at the same future base. -/
def Consequence (K : Basis Atom) (B : Base Atom)
    (Γ : List (Formula Atom)) (C : Formula Atom) : Prop :=
  ∀ D ∈ K, B ⊆ D → (∀ A ∈ Γ, Support K D A) → Support K D C

theorem empty_agreement (hB : B ∈ K) {C : Formula Atom} :
    Consequence K B [] C ↔ Support K B C := by
  constructor
  · exact fun h => h B hB (fun _ h => h) (by simp)
  · exact fun h _ _ hBD _ => persistence hBD h

theorem application (hB : B ∈ K) {A C : Formula Atom}
    (f : Support K B (.imp A C)) (a : Support K B A) : Support K B C :=
  f B hB (fun _ h => h) a

theorem introduction {Γ : List (Formula Atom)} {A C : Formula Atom}
    (h : Consequence K B (A :: Γ) C) : Consequence K B Γ (.imp A C) := by
  intro D hD hBD hΓ E hE hDE hA
  apply h E hE (Finset.Subset.trans hBD hDE)
  intro X hX
  rcases List.mem_cons.mp hX with rfl | hX
  · exact hA
  · exact persistence hDE (hΓ X hX)

theorem consequence_application {Γ : List (Formula Atom)} {A C : Formula Atom}
    (f : Consequence K B Γ (.imp A C)) (a : Consequence K B Γ A) :
    Consequence K B Γ C :=
  fun D hD hBD hΓ => application hD (f D hD hBD hΓ) (a D hD hBD hΓ)

/-- A unary rule supports its implication throughout every basis. -/
theorem unary_support [DecidableEq Atom] {p q : Atom}
    (h : (⟨{p}, q⟩ : Rule Atom) ∈ B) :
    Support K B (.imp (.atom p) (.atom q)) := by
  intro D _ hBD hp
  exact .rule ⟨{p}, q⟩ (hBD h) (by simpa [Support] using hp)
end SquareKit.HornSupport
