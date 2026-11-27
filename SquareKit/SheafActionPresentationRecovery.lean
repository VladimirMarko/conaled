import SquareKit.StackificationUniversal
import SquareKit.SheafActionPresentation
import SquareKit.SheafActionStackification
import SquareKit.SheafSiteComparisonQuotient

/-! The independent label presentation recovers precisely the globally
trivializable part of the torsor quotient, and generates the full stack locally. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafActionPresentation
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M : Sheaf J (Type (max u v))}
variable (a : SheafActionQuotient.Action G M)
variable {X : Sheaf J (Type (max u v))}

/-- Every regular chart has the identity section of its regular torsor. -/
def toTrivial : Object a X ⥤ (SheafActionStackification.globallyTrivial a).Obj (.mk (op X)) :=
  ((SheafActionStackification.globallyTrivial a).prop (.mk (op X))).lift (quotient a)
    (fun _ => ⟨SheafTorsor.sectionOfArrow (SheafTorsor.Arrow.ident _)⟩)

def toTrivialFullyFaithful : (toTrivial (X := X) a).FullyFaithful where
  preimage h := (quotientFullyFaithful a).preimage h.hom
  map_preimage h := by
    apply ObjectProperty.hom_ext
    exact (quotientFullyFaithful a).map_preimage h.hom
  preimage_map h := (quotientFullyFaithful a).preimage_map h

instance : (toTrivial (X := X) a).Full := (toTrivialFullyFaithful a).full
instance : (toTrivial (X := X) a).Faithful := (toTrivialFullyFaithful a).faithful

/-- A global section derives the chart point and its actual target-preserving arrow. -/
instance toTrivial_essSurj : (toTrivial (X := X) a).EssSurj where
  mem_essImage P := by
    let e := SheafTorsor.ofSection P.obj.torsor P.property.some
    refine ⟨⟨P.obj.sectionMap (SheafTorsor.sectionOfArrow e)⟩, ⟨?_⟩⟩
    exact ((SheafActionStackification.globallyTrivial a).prop (.mk (op X))).isoMk
      (P.obj.chartOfTrivialization e).toIso

instance : (toTrivial (X := X) a).IsEquivalence := {}

/-- This equivalence is derived from the section, label and target-map constructions. -/
def trivialEquivalence : Object a X ≌
    (SheafActionStackification.globallyTrivial a).Obj (.mk (op X)) :=
  (toTrivial a).asEquivalence

/-- Recovering globally trivial objects commutes with parameter restriction. -/
def trivialTransformation : Pseudofunctor.StrongTrans (pseudofunctor a)
    (SheafActionStackification.presentation a) where
  app X := (toTrivial (X := X.as.unop) a).toCatHom
  naturality _ := Iso.refl _
  naturality_naturality := by
    intro X Y f g h
    obtain rfl := LocallyDiscrete.eq_of_hom h
    have hh : h = 𝟙 f := Subsingleton.elim _ _
    subst h
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    ext m
    simp
  naturality_id X := by
    apply Cat.Hom₂.ext
    ext m
    apply ObjectProperty.hom_ext
    change 𝟙 _ = (quotient a).map (𝟙 _)
    exact (quotient a).map_id _ |>.symm
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    ext m
    apply ObjectProperty.hom_ext
    change 𝟙 _ = (quotient a).map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.comp_id]
    exact (quotient a).map_id _ |>.symm

/-- The chart cover is the total space of the given torsor; its tautological
section constructs the local chart comparison without a global trivialization. -/
theorem locallyGenerating :
    StackLocalGeneration.LocallyGenerating (SheafCover.topology (J := J))
      (transformation a) := by
  intro X P
  let f := SplitSheaf.p P.torsor.family
  let Q := SheafActionQuotient.reindex P f
  let e := SheafTorsor.ofSection Q.torsor (SplitSheaf.q P.torsor.family)
  refine ⟨SplitSheaf.extension P.torsor.family, f,
    ⟨_, _, inferInstance, Sieve.ofArrows_mk _ _ ()⟩,
    ⟨Q.sectionMap (SheafTorsor.sectionOfArrow e)⟩, ⟨?_⟩⟩
  exact (Q.chartOfTrivialization e).toIso

/-- Arrow descent follows from the faithful complete chart-arrow comparison. -/
instance isPrestack : (pseudofunctor a).IsPrestack (SheafCover.topology (J := J)) :=
  StackObjectPropertyDescent.isPrestack_of_fullyFaithful (transformation a)
    (fun _ => quotientFullyFaithful a) _

/-- Recovery through the full subcategory has the original quotient map on
objects and arrows, rather than only the same isomorphism classes. -/
theorem toTrivial_comp_inclusion :
    toTrivial (X := X) a ⋙ ((SheafActionStackification.globallyTrivial a).prop (.mk (op X))).ι =
      quotient a := rfl

end SquareKit.SheafActionPresentation

namespace SquareKit.SheafSiteComparison
open CategoryTheory Opposite
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
variable [F.IsContinuous J K] [F.IsCocontinuous J K]
variable {G : Sheaf K GrpCat.{u}} {M X Y : Sheaf K (Type u)}
variable (a : SheafActionQuotient.Action G M)

/-- Site restriction acts on the actual chart map and its independent label. -/
def presentationFunctor : SheafActionPresentation.Object a X ⥤
    SheafActionPresentation.Object (action J K F a) (sheaf J K F X) where
  obj m := ⟨map J K F m.map⟩
  map h := ⟨map J K F h.label, congrArg (map J K F) h.relation⟩
  map_id _ := SheafActionPresentation.Arrow.ext _ _ rfl
  map_comp _ _ := SheafActionPresentation.Arrow.ext _ _ rfl

/-- The new presentation recovers the existing site comparison on every arrow. -/
theorem presentation_quotient :
    presentationFunctor (X := X) J K F a ⋙ SheafActionPresentation.quotient (action J K F a) =
      SheafActionPresentation.quotient a ⋙ quotientFunctor J K F a := rfl

omit [F.IsCocontinuous J K] in
/-- Parameter substitution and site restriction commute before stackification. -/
theorem presentation_restriction (f : Y ⟶ X) :
    SheafActionPresentation.restriction a f ⋙ presentationFunctor J K F a =
      presentationFunctor J K F a ⋙
        SheafActionPresentation.restriction (action J K F a) (map J K F f) := rfl

variable [F.Full] [F.Faithful] [F.IsDenseSubsite J K]

/-- Under the original dense-subsite hypotheses the comparison is exactly the
forward functor of the existing quotient equivalence. -/
def presentationQuotientComparison :
    presentationFunctor (X := X) J K F a ⋙ SheafActionPresentation.quotient (action J K F a) ≅
      SheafActionPresentation.quotient a ⋙ (quotientEquivalence J K F a).functor := Iso.refl _

/-- The existing natural restriction comparison also recovers all presentation arrows. -/
def presentationQuotientRestrictionComparison (f : Y ⟶ X) :
    SheafActionPresentation.quotient a ⋙
      (SheafActionQuotient.restriction f ⋙ quotientFunctor J K F a) ≅
    SheafActionPresentation.quotient a ⋙
      (quotientFunctor J K F a ⋙ SheafActionQuotient.restriction (map J K F f)) :=
  Functor.isoWhiskerLeft _ (quotientRestrictionComparison J K F a f)

end SquareKit.SheafSiteComparison

namespace SquareKit.SheafActionPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M : Sheaf J (Type (max u v))}
variable (a : SheafActionQuotient.Action G M)
variable (T : Pseudofunctor (LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ)
  Cat.{max u v, max (u + 1) (v + 1)}) [T.IsStack (SheafCover.topology (J := J))]

/-- Restriction along the chart unit is an equivalence on strong transformations
and their modifications, for every target stack. -/
def universalEquivalence :
    (SheafActionQuotient.Stack.pseudofunctor a ⟶ T) ≌ (pseudofunctor a ⟶ T) :=
  StackificationUniversal.universalEquivalence (fun _ => quotientFullyFaithful a)
    (locallyGenerating a) T

@[simp] theorem universalEquivalence_functor :
    (universalEquivalence a T).functor =
      StackLocalGeneration.restriction (transformation a) T := rfl

end SquareKit.SheafActionPresentation
