import SquareKit.HornSupport

/-! Checked fixed-basis fixtures from the atomic-base support construction. -/
namespace Examples.HornSupport
open SquareKit.HornSupport

inductive Atom where
  | p | q | r
  deriving DecidableEq
open Atom

def pq : Rule Atom := ⟨{p}, q⟩
def factP : Rule Atom := ⟨∅, p⟩
def qr : Rule Atom := ⟨{q}, r⟩
def B0 : Base Atom := {pq}
def B1 : Base Atom := {pq, factP}
def B2 : Base Atom := {pq, factP, qr}
def allBases : Basis Atom := Set.univ

theorem strict01 : B0 ⊂ B1 := by decide
theorem strict12 : B1 ⊂ B2 := by decide

theorem B0_none (a : Atom) : ¬ Derivable B0 a := by
  intro d
  exact d.invariant (fun _ => False) (by
    intro rule hr children
    have h : rule = pq := by simpa [B0] using hr
    subst rule
    exact children p (by simp [pq]))

theorem B1_p : Derivable B1 p :=
  .rule factP (by decide) (by simp [factP])
theorem B1_q : Derivable B1 q :=
  .rule pq (by decide) (by simpa [pq] using B1_p)
theorem B1_not_r : ¬ Derivable B1 r := by
  intro d
  have h := d.invariant (fun a => a ≠ r) (by
    intro rule hr _
    simp only [B1, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> decide)
  exact h rfl

theorem B2_p : Derivable B2 p := B1_p.weaken strict12.le
theorem B2_q : Derivable B2 q := B1_q.weaken strict12.le
theorem B2_r : Derivable B2 r :=
  .rule qr (by decide) (by simpa [qr] using B2_q)

theorem B0_pq : Support allBases B0 (.imp (.atom p) (.atom q)) :=
  unary_support (by decide)
theorem B1_pq : Support allBases B1 (.imp (.atom p) (.atom q)) :=
  persistence strict01.le B0_pq
theorem B2_pq : Support allBases B2 (.imp (.atom p) (.atom q)) :=
  persistence strict12.le B1_pq
theorem B0_not_qr : ¬ Support allBases B0 (.imp (.atom q) (.atom r)) :=
  fun h => B1_not_r (h B1 (Set.mem_univ _) strict01.le B1_q)
theorem B1_not_qr : ¬ Support allBases B1 (.imp (.atom q) (.atom r)) :=
  fun h => B1_not_r (application (Set.mem_univ _) h B1_q)
theorem B2_qr : Support allBases B2 (.imp (.atom q) (.atom r)) :=
  unary_support (by decide)

/-- The antecedent itself is an implication. At every future base it can be
applied to the persistent p proof. Introduction must carry that context forward. -/
theorem nested : Support allBases B1
    (.imp (.imp (.atom p) (.atom q)) (.atom q)) := by
  apply (empty_agreement (Set.mem_univ _)).mp
  apply introduction
  intro D hD hBD ctx
  exact application hD (ctx _ (by simp)) (persistence (A := .atom p) hBD B1_p)

/-- Two introductions carry a nonempty context across the inner extension. -/
theorem curried_application : Support allBases B0
    (.imp (.atom p) (.imp (.imp (.atom p) (.atom q)) (.atom q))) := by
  apply (empty_agreement (Set.mem_univ _)).mp
  apply introduction
  apply introduction
  intro D hD _ ctx
  exact application (A := .atom p) hD (ctx _ (by simp)) (ctx _ (by simp))

def singletonBasis : Basis Atom := {∅}
def largerBasis : Basis Atom := {∅, {factP}}

theorem singleton_vacuity : Support singletonBasis ∅ (.imp (.atom p) (.atom q)) := by
  intro D hD _ hp
  have : D = ∅ := Set.mem_singleton_iff.mp hD
  subst D
  exact False.elim (Derivable.not_empty hp)

theorem larger_failure : ¬ Support largerBasis ∅ (.imp (.atom p) (.atom q)) := by
  intro h
  have hp : Derivable {factP} p := .rule factP (by simp) (by simp [factP])
  have hq := h {factP} (by simp [largerBasis]) (Finset.empty_subset _) hp
  have impossible := hq.invariant (fun x => x = p) (by
    intro rule hr _
    have he : rule = factP := Finset.mem_singleton.mp hr
    subst rule
    rfl)
  cases impossible

theorem basis_enlargement : singletonBasis ⊆ largerBasis := by
  intro B h
  simp only [singletonBasis, Set.mem_singleton_iff] at h
  subst B
  simp [largerBasis]
end Examples.HornSupport
