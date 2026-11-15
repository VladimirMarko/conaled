import SquareKit.IndexedSumFamilies

/-! Selected dependent sums under two nonidentity substitutions, a different
chosen adjoint, and two failure controls for weaker contracts. -/
noncomputable section
namespace Examples.IndexedWitnessAdjunctions
open CategoryTheory Limits ConcreteCategory
open SquareKit.IndexedSumBaseChange SquareKit.IndexedSumFamilies

/-- Both the number of indices and their value types vary with the context. -/
abbrev Indices (n : Nat) := Fin (n + 2)
abbrev Values (n : Nat) (i : Indices n) := Fin (n + i.val + 1)
def sigma : Nat ⟶ Nat := ↾fun n => n + 1
def tau : Nat ⟶ Nat := ↾fun n => n * 2

/-- At context 2 the substitutions reach 5; select index 3 and value 8 : Fin 9. -/
def chosen : Selected Indices Values (sigma (tau 2)) := ⟨⟨3, by decide⟩, ⟨8, by decide⟩⟩

theorem native_result : (chosen.1.val, chosen.2.val) = (3, 8) := rfl

/-- This conclusion consumes both categorical base-change comparisons. -/
theorem categorical_result :
    pullback.fst ((family Indices Values).hom ≫ indexMap Indices) sigma
      (pullback.fst (pullback.snd ((family Indices Values).hom ≫ indexMap Indices) sigma) tau
        (twice Indices Values sigma tau 2 chosen)) =
      ⟨⟨5, ⟨3, by decide⟩⟩, ⟨8, by decide⟩⟩ :=
  twice_value Indices Values sigma tau 2 chosen

/-- Another chosen left adjoint retains this very selected dependent value. -/
theorem alternative_result :
    (((Over.mapPullbackAdj (indexMap Indices)).leftAdjointUniq
      (taggedAdjunction (indexMap Indices))).hom.app (family Indices Values)).left
      ⟨⟨5, chosen.1⟩, chosen.2⟩ = (PUnit.unit, ⟨⟨5, chosen.1⟩, chosen.2⟩) :=
  selected_tagging _ _ _

/-- Changing the sum representations before base change preserves the chosen result. -/
example : pullback.fst ((taggedSum (indexMap Indices)).obj (family Indices Values)).hom sigma
    (taggedFirst Indices Values sigma (tau 2) chosen) =
    (PUnit.unit, ⟨⟨5, ⟨3, by decide⟩⟩, ⟨8, by decide⟩⟩) :=
  taggedFirst_value Indices Values sigma (tau 2) chosen

/-- Truth cannot reconstruct two distinct selected witnesses. -/
theorem no_selection_reconstruction :
    ¬ ∃ recover : Nonempty Bool → Bool, ∀ b : Bool, recover ⟨b⟩ = b := by
  rintro ⟨recover, h⟩
  have e : (Nonempty.intro false : Nonempty Bool) = ⟨true⟩ := Subsingleton.elim _ _
  have bad := (h false).symm.trans ((congrArg recover e).trans (h true))
  cases bad

namespace NonPullback
abbrev emptyMap : Empty ⟶ Unit := ↾Empty.elim
abbrev unitMap : Unit ⟶ Unit := 𝟙 Unit

theorem commutes : emptyMap ≫ unitMap = emptyMap ≫ unitMap := rfl

abbrev X : Over Unit := Over.mk unitMap
abbrev badComparison := (comparison (f := unitMap) (g := unitMap)
  (f' := emptyMap) (g' := emptyMap) commutes).app X

def targetPoint : ((Over.map unitMap ⋙ Over.pullback unitMap).obj X).left :=
  encode unitMap ((Over.map unitMap).obj X) () ⟨(), rfl⟩

/-- The proposed comparison has empty domain and an inhabited codomain. -/
theorem not_invertible : ¬ IsIso badComparison := by
  intro h
  let := h
  exact (pullback.snd X.hom emptyMap ((inv badComparison).left targetPoint)).elim

/-- The missing pullback hypothesis is refuted independently by the universal pair. -/
theorem not_pullback : ¬ IsPullback emptyMap emptyMap unitMap unitMap := by
  intro h
  exact (h.lift (𝟙 Unit) (𝟙 Unit) (by rfl) ()).elim
/-- Every arrow over Empty is invertible, since both its carriers are empty. -/
theorem empty_slice_iso {Y Z : Over Empty} (k : Y ⟶ Z) : IsIso k := by
  refine ⟨⟨Over.homMk (↾fun z => (Z.hom z).elim) (by ext z; exact (Z.hom z).elim), ?_, ?_⟩⟩
  · ext y
    exact (Y.hom y).elim
  · ext z
    exact (Z.hom z).elim

/-- The commuting pullback transformation is the mate of the failed sum comparison. -/
abbrev invertibleMate := mateEquiv (Over.mapPullbackAdj unitMap)
  (Over.mapPullbackAdj emptyMap)
  (comparison (f := unitMap) (g := unitMap) (f' := emptyMap) (g' := emptyMap) commutes)

instance invertibleMate_app (Y : Over Unit) : IsIso (invertibleMate.app Y) :=
  empty_slice_iso _

/-- Invertibility of this original transformation does not imply it for its mate. -/
example : IsIso invertibleMate := NatIso.isIso_of_isIso_app _

theorem inverse_mate_not_invertible :
    ¬ IsIso (((mateEquiv (Over.mapPullbackAdj unitMap)
      (Over.mapPullbackAdj emptyMap)).symm invertibleMate).app X) := by
  simpa only [invertibleMate, Equiv.symm_apply_apply] using not_invertible
end NonPullback
end Examples.IndexedWitnessAdjunctions
