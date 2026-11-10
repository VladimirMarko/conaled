import SquareKit.SmoothQuotientCoverSections
import Examples.ParameterDeformationSections
import Mathlib.CategoryTheory.Sites.EpiMono

/-! Original-cover section recovery on a genuine two-sheet sheaf cover. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Examples.ArbitraryCoverSections
open CategoryTheory CategoryTheory.Limits SquareKit SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport.GroupoidModel
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M}

/-- Two whole copies of the same sheaf, with their actual codiagonal cover. -/
def twoSheet (X : Sheaf topology Type) : X ⨿ X ⟶ X := coprod.desc (𝟙 X) (𝟙 X)

@[simp] theorem left_sheet : coprod.inl ≫ twoSheet X = 𝟙 X :=
  coprod.inl_desc _ _

@[simp] theorem right_sheet : coprod.inr ≫ twoSheet X = 𝟙 X :=
  coprod.inr_desc _ _

instance twoSheet_epi : Epi (twoSheet X) where
  left_cancellation g h he := by
    have e := congrArg (fun k => (coprod.inl : X ⟶ X ⨿ X) ≫ k) he
    simpa only [← Category.assoc, left_sheet, Category.id_comp] using e

instance twoSheet_locallySurjective :
    Presheaf.IsLocallySurjective topology (twoSheet X).hom :=
  (Sheaf.isLocallySurjective_iff_epi (twoSheet X)).mpr inferInstance

/-- Constant deformations supply compatible sections on the original cover
without using its split representation in the input. -/
def constantFamily (f : Y ⟶ X) : CoverSectionFamily (a := a) f where
  sections _ := ParameterDeformationSections.constantSection
  natural _ _ _ := by apply Deformation.ext; rfl
  matching _ _ _ _ := rfl

/-- Both actual sheets recover the selected complete sections after gluing. -/
example :
    restrictSection (twoSheet X) ((constantFamily (a := a) (twoSheet X)).glue) =
      (ParameterDeformationSections.constantSection (a := a) (X := X ⨿ X)).reindex
        (SheafActionQuotient.restriction (twoSheet X)) :=
  (constantFamily (a := a) (twoSheet X)).glue_restrict_section

/-- The cover's actual overlap condition compares its two inclusions. -/
theorem sheet_matching (s : CoverSectionFamily (a := a) (twoSheet X))
    (P : Object a X) :
    ((s.sections coprod.inl).obj P).as = ((s.sections coprod.inr).obj P).as :=
  s.matching _ _ (by rw [left_sheet, right_sheet]) P

/-- Distinct selected context arrows survive gluing even for ineffective
actions; section lifting records the full arrow as its base component. -/
example (P : Object a X) (p q : P ⟶ P) (hne : p ≠ q) :
    ((constantFamily (a := a) (twoSheet X)).glue).lift.map p ≠
      ((constantFamily (a := a) (twoSheet X)).glue).lift.map q := by
  intro he
  exact hne (congrArg Grothendieck.Hom.base he)

/-- This consumer uses the existing nontrivial doubled-origin torsor on an
actual two-sheet cover, with no supplied global trivialization. -/
example (K : Type) [Group K] (c : K) :
    restrict (twoSheet SmoothClutching.base)
      ((((constantFamily (a := ActionQuotientEvidence.ineffective K)
        (twoSheet SmoothClutching.base)).glue).obj
          (ActionQuotientEvidence.nontrivialObject K c)).as) =
      constant (reindex (ActionQuotientEvidence.nontrivialObject K c)
        (twoSheet SmoothClutching.base)) :=
  (constantFamily (a := ActionQuotientEvidence.ineffective K)
    (twoSheet SmoothClutching.base)).glue_restrict _

/-- Pulling back the actual two-sheet cover along any parameter map retains
full-section naturality; no invertibility of the parameter map is required. -/
example (u : Y ⟶ X) :
    restrictSection u ((constantFamily (a := a) (twoSheet X)).glue) =
      ((constantFamily (a := a) (twoSheet X)).baseChange u).glue.reindex
        (SheafActionQuotient.restriction u) :=
  (constantFamily (a := a) (twoSheet X)).glue_baseChange_section u

/-- Covering values determine the full section, including its quotient arrows. -/
example (t : Section (setFamily (family a X)))
    (h : ∀ P, restrict (twoSheet X) ((t.obj P).as) =
      constant (reindex P (twoSheet X))) :
    t = (constantFamily (a := a) (twoSheet X)).glue :=
  (constantFamily (a := a) (twoSheet X)).glue_unique t h

end Examples.ArbitraryCoverSections
