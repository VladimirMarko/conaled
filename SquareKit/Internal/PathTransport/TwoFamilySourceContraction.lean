import SquareKit.Internal.PathTransport.TwoFamilyModelComparisons
import SquareKit.Internal.PathTransport.TwoFamilyFiniteDependentTailBeta
/-! Coherent contractions over the exact source telescope maps. Normalization
is carried through every dependent extension and yields whole-section computation. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
open TwoFamily TwoFamily.FiniteDependentTail
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
structure SourceContraction {Γ Δ : Context.{u}} (i : StrictPseudofunctor Δ Γ) where
  retraction : StrictPseudofunctor Γ Δ
  homotopy : Pseudofunctor.StrongTrans (retraction.comp i).toPseudofunctor
    (StrictPseudofunctor.id Γ).toPseudofunctor
namespace SourceContraction
variable {Γ Δ : Context.{u}} {i : StrictPseudofunctor Δ Γ}
def presentation (c : SourceContraction i) : ContractionPresentation Γ.toStrictTwoCategory where
  source := Δ.toStrictTwoCategory
  sourceObjects := Δ.groupoid
  sourceCells := Δ.locallyGroupoid
  inclusion := i
  retraction := c.retraction
  homotopy := c.homotopy

def Normalized (c : SourceContraction i) : Prop := c.presentation.Normalized

def cast {j : StrictPseudofunctor Δ Γ} (h : i = j) (c : SourceContraction i) : SourceContraction j := h ▸ c

theorem cast_normalized {j : StrictPseudofunctor Δ Γ} (h : i = j) (c : SourceContraction i)
    (hc : c.Normalized) : (c.cast h).Normalized := by cases h; exact hc

noncomputable def extendRaw (A : Family Γ) (c : SourceContraction i) :
    SourceContraction (Γ := A.total) (Δ := (A.reindex i).total) (reindexHigher A.data i) := by
  letI : ∀ x, IsIso (c.homotopy.app x) := fun _ => IsGroupoid.all_isIso _
  exact ⟨contractionRetraction i c.retraction c.homotopy A.data,
    contractionRetractionHomotopy i c.retraction c.homotopy A.data⟩

theorem extendRaw_normalized (A : Family Γ) (c : SourceContraction i) (hc : c.Normalized) :
    (c.extendRaw A).Normalized := by
  let : ∀ x, IsIso (c.homotopy.app x) := fun _ => IsGroupoid.all_isIso _
  exact ⟨contractionRetraction_reflexive i c.retraction c.homotopy hc.1 hc.2 A.data,
    contractionRetractionHomotopy_reflexive A.data i c.retraction c.homotopy hc.1 hc.2⟩

variable (C D : Context.{u})
local notation "M" => structuralModel C D
noncomputable def extend (A : Family Γ) (c : SourceContraction i) :
    SourceContraction (Γ := A.total) (Δ := (A.reindex i).total)
      ((M).lift A ⟨i⟩).down :=
  (c.extendRaw A).cast (lift_eq_reindexHigher C D A i).symm

theorem extend_normalized (A : Family Γ) (c : SourceContraction i) (hc : c.Normalized) :
    (c.extend C D A).Normalized :=
  cast_normalized _ _ (extendRaw_normalized A c hc)

noncomputable def telescope {Γ Δ : (M).Context} {n}
    (T : Typed.StructuralModel.Telescope M Γ n) (i : (M).Substitution Δ Γ)
    (c : {c : SourceContraction i.down // c.Normalized}) :
    {d : SourceContraction (Γ := T.total M) (Δ := (T.pullback M i).total M)
      (T.liftSub M i).down // d.Normalized} :=
  match T with
  | .nil => c
  | .cons A tail => telescope tail ((M).lift A i)
      ⟨c.val.extend C D A, c.val.extend_normalized C D A c.property⟩
noncomputable def eliminate {Γ Δ : (M).Context} {n}
    (T : Typed.StructuralModel.Telescope M Γ n) (i : (M).Substitution Δ Γ)
    (c : {c : SourceContraction i.down // c.Normalized}) (E : (M).Family (T.total M))
    (d : (M).Section _ ((M).subTy E (T.liftSub M i))) : (M).Section _ E :=
  ⟨retractionJ (T.liftSub M i).down (telescope C D T i c).val.retraction
    (telescope C D T i c).val.homotopy E.data d.down⟩

theorem eliminate_beta {Γ Δ : (M).Context} {n}
    (T : Typed.StructuralModel.Telescope M Γ n) (i : (M).Substitution Δ Γ)
    (c : {c : SourceContraction i.down // c.Normalized}) (E : (M).Family (T.total M))
    (d : (M).Section _ ((M).subTy E (T.liftSub M i))) :
    (M).subTm (eliminate C D T i c E d) (T.liftSub M i) = d := by
  apply ULift.ext
  exact retractionJ_beta _ _ _ (telescope C D T i c).property.1
    (telescope C D T i c).property.2 E.data d.down

end SourceContraction
end SquareKit.Internal.PathTransport.HigherInterpretation
