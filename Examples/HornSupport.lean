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
def ruleBase : Base Atom := {pq}
def factBase : Base Atom := {pq, factP}
def chainBase : Base Atom := {pq, factP, qr}
def allBases : Basis Atom := Set.univ

theorem strict01 : ruleBase ⊂ factBase := by decide
theorem strict12 : factBase ⊂ chainBase := by decide

theorem ruleBase_none (a : Atom) : ¬ Derivable ruleBase a := by
  intro d
  exact d.invariant (fun _ => False) (by
    intro rule hr children
    have h : rule = pq := by simpa [ruleBase] using hr
    subst rule
    exact children p (by simp [pq]))

theorem factBase_p : Derivable factBase p :=
  .rule factP (by decide) (by simp [factP])
theorem factBase_q : Derivable factBase q :=
  .rule pq (by decide) (by simpa [pq] using factBase_p)
theorem factBase_not_r : ¬ Derivable factBase r := by
  intro d
  have h := d.invariant (fun a => a ≠ r) (by
    intro rule hr _
    simp only [factBase, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> decide)
  exact h rfl

theorem chainBase_p : Derivable chainBase p := factBase_p.weaken strict12.le
theorem chainBase_q : Derivable chainBase q := factBase_q.weaken strict12.le
theorem chainBase_r : Derivable chainBase r :=
  .rule qr (by decide) (by simpa [qr] using chainBase_q)

theorem ruleBase_pq : Support allBases ruleBase (.imp (.atom p) (.atom q)) :=
  unary_support (by decide)
theorem factBase_pq : Support allBases factBase (.imp (.atom p) (.atom q)) :=
  persistence strict01.le ruleBase_pq
theorem chainBase_pq : Support allBases chainBase (.imp (.atom p) (.atom q)) :=
  persistence strict12.le factBase_pq
theorem ruleBase_not_qr : ¬ Support allBases ruleBase (.imp (.atom q) (.atom r)) :=
  fun h => factBase_not_r (h factBase (Set.mem_univ _) strict01.le factBase_q)
theorem factBase_not_qr : ¬ Support allBases factBase (.imp (.atom q) (.atom r)) :=
  fun h => factBase_not_r (application (Set.mem_univ _) h factBase_q)
theorem chainBase_qr : Support allBases chainBase (.imp (.atom q) (.atom r)) :=
  unary_support (by decide)

/-- The antecedent itself is an implication. At every future base it can be
applied to the persistent p proof. Introduction must carry that context forward. -/
theorem nested : Support allBases factBase
    (.imp (.imp (.atom p) (.atom q)) (.atom q)) := by
  apply (empty_agreement (Set.mem_univ _)).mp
  apply introduction
  intro D hD hBD ctx
  exact application hD (ctx _ (by simp)) (persistence (A := .atom p) hBD factBase_p)

/-- Two introductions carry a nonempty context across the inner extension. -/
theorem curried_application : Support allBases ruleBase
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
