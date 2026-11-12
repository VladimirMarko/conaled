import SquareKit.OracleModality
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Data.Bool.Basic

/-! Persistent truth values with an explicit Kripke implication law.
Lower sets of the dual order are ordered by inclusion, unlike Mathlib's UpperSet. -/

namespace OracleModality.Kripke

universe u
variable {W : Type u} [Preorder W]

abbrev Truth (W : Type u) [Preorder W] := LowerSet (OrderDual W)

theorem persist {U : Truth W} {w v : W} (h : w ≤ v) (hw : w ∈ U) : v ∈ U :=
  U.lower h hw

/-- Explicit persistent implication; this is not pointwise ambient implication. -/
def implication (U V : Truth W) : Truth W where
  carrier := {w : W | ∀ v : W, w ≤ v → v ∈ U → v ∈ V}
  lower' := by
    intro a b hab hb v hav hv
    exact hb v (le_trans hab hav) hv

theorem implication_adjunction (R U V : Truth W) :
    R ≤ implication U V ↔ R ⊓ U ≤ V := by
  constructor
  · intro h w hw
    exact h hw.1 w le_rfl hw.2
  · intro h w hw v hwv hv
    exact h ⟨persist hwv hw, hv⟩

theorem implication_eq_himp (U V : Truth W) : implication U V = U ⇨ V := by
  apply le_antisymm
  · exact le_himp_iff.mpr ((implication_adjunction _ _ _).mp le_rfl)
  · exact (implication_adjunction _ _ _).mpr himp_inf_le

/-- Adequacy of the native algebraic implication for future-stage proof transport. -/
theorem mem_himp (U V : Truth W) (w : W) :
    w ∈ (U ⇨ V) ↔ ∀ v, w ≤ v → v ∈ U → v ∈ V := by
  rw [← implication_eq_himp]
  rfl

abbrev World := Bool × Bool

def leftAnswer : Truth World where
  carrier := {w | w.1 = true}
  lower' := by
    intro a b hab hb
    exact (Bool.le_iff_imp.mp hab.1) hb

def rightAnswer : Truth World where
  carrier := {w | w.2 = true}
  lower' := by
    intro a b hab hb
    exact (Bool.le_iff_imp.mp hab.2) hb

end OracleModality.Kripke
