import SquareKit.SheafGroupoidCompletion
import SquareKit.SheafGroupoidChartPresentation
import SquareKit.SheafActionRefinement

/-! Recovery of the existing action and site-change clients from actual arrows. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SquareKit.SheafGroupoidCompletion
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M A : Sheaf J (Type (max u v))}
variable (a : SheafActionQuotient.Action G M)
  (e : A ≅ SheafGroupoidAction.arrows (G := G) (M := M))
  {X Y : Sheaf J (Type (max u v))}

/-- Actual arrows recover the original globally trivial quotient objects. -/
def trivialEquivalence : (operations a e).Object X ≌
    (SheafActionStackification.globallyTrivial a).Obj (.mk (op X)) :=
  (presentationEquivalence a e).trans (SheafActionPresentation.trivialEquivalence a)

/-- Recovery preserves the entire quotient object and every target-preserving arrow. -/
theorem trivialEquivalence_inclusion :
    (trivialEquivalence (X := X) a e).functor ⋙
      ((SheafActionStackification.globallyTrivial a).prop (.mk (op X))).ι =
    quotient a e := rfl

variable {U : Sheaf J (Type (max u v))} {p : U ⟶ M}
  (D : SheafGroupoid.Chart (operations a e) p p)

/-- Independent arrow coordinates recover the original atlas presentation. -/
def toRefinement : D.Object X ⥤ SheafActionRefinement.Object a p X where
  obj m := ⟨m.map⟩
  map f := (D.toGroupoid ⋙ toPresentation a e).map f
  map_id m := (D.toGroupoid ⋙ toPresentation a e).map_id m
  map_comp f g := (D.toGroupoid ⋙ toPresentation a e).map_comp f g

def toRefinementFullyFaithful : (toRefinement (X := X) a e D).FullyFaithful where
  preimage := (D.fullyFaithful.comp (toPresentationFullyFaithful a e)).preimage
  map_preimage := (D.fullyFaithful.comp (toPresentationFullyFaithful a e)).map_preimage
  preimage_map := (D.fullyFaithful.comp (toPresentationFullyFaithful a e)).preimage_map

/-- No covering hypothesis is needed to recover a fixed atlas's arrows and objects. -/
def refinementEquivalence : D.Object X ≌ SheafActionRefinement.Object a p X := by
  letI := (toRefinementFullyFaithful (X := X) a e D).full
  letI := (toRefinementFullyFaithful (X := X) a e D).faithful
  letI : (toRefinement (X := X) a e D).EssSurj :=
    ⟨fun m => ⟨⟨m.map⟩, ⟨Iso.refl _⟩⟩⟩
  letI : (toRefinement (X := X) a e D).IsEquivalence := {}
  exact (toRefinement a e D).asEquivalence

theorem toRefinement_quotient :
    toRefinement (X := X) a e D ⋙ SheafActionRefinement.quotient a p =
      D.toGroupoid ⋙ quotient a e := rfl

theorem toRefinement_restriction (r : Y ⟶ X) :
    D.restriction r ⋙ toRefinement a e D =
      toRefinement a e D ⋙ SheafActionRefinement.restriction a p r := rfl

/-- The atlas map itself constructs the full arrow chart required by recovery. -/
def canonicalRefinementEquivalence (p : U ⟶ M) :
    (SheafGroupoid.Chart.canonical (operations a e) p p).Object X ≌
      SheafActionRefinement.Object a p X :=
  refinementEquivalence a e (SheafGroupoid.Chart.canonical (operations a e) p p)

theorem canonicalRefinementEquivalence_quotient (p : U ⟶ M) :
    (canonicalRefinementEquivalence (X := X) a e p).functor ⋙
      SheafActionRefinement.quotient a p =
    (SheafGroupoid.Chart.canonical (operations a e) p p).toGroupoid ⋙ quotient a e :=
  toRefinement_quotient a e _

theorem canonicalRefinementEquivalence_restriction (p : U ⟶ M) (r : Y ⟶ X) :
    (SheafGroupoid.Chart.canonical (operations a e) p p).restriction r ⋙
      (canonicalRefinementEquivalence a e p).functor =
    (canonicalRefinementEquivalence a e p).functor ⋙ SheafActionRefinement.restriction a p r :=
  toRefinement_restriction a e _ r

/-- Original action-and-atlas clients recover without supplying arrow coordinates or an isomorphism. -/
def actionRefinementEquivalence (p : U ⟶ M) :
    (SheafGroupoid.Chart.canonical (operations a (Iso.refl _)) p p).Object X ≌
      SheafActionRefinement.Object a p X :=
  canonicalRefinementEquivalence a (Iso.refl _) p

theorem actionRefinementEquivalence_quotient (p : U ⟶ M) :
    (actionRefinementEquivalence (X := X) a p).functor ⋙ SheafActionRefinement.quotient a p =
    (SheafGroupoid.Chart.canonical (operations a (Iso.refl _)) p p).toGroupoid ⋙
      quotient a (Iso.refl _) :=
  canonicalRefinementEquivalence_quotient a (Iso.refl _) p

theorem actionRefinementEquivalence_restriction (p : U ⟶ M) (r : Y ⟶ X) :
    (SheafGroupoid.Chart.canonical (operations a (Iso.refl _)) p p).restriction r ⋙
      (actionRefinementEquivalence a p).functor =
    (actionRefinementEquivalence a p).functor ⋙ SheafActionRefinement.restriction a p r :=
  canonicalRefinementEquivalence_restriction a (Iso.refl _) p r

section AtlasMap
variable {V : Sheaf J (Type (max u v))} {q : V ⟶ M}
  (E : SheafGroupoid.Chart (operations a e) q q)

/-- Recovery intertwines the original commuting-square atlas map. -/
theorem toRefinement_atlasMap (r : U ⟶ V) (comm : r ≫ q = p) :
    D.atlasMap (T := X) E r comm ⋙ toRefinement a e E =
      toRefinement a e D ⋙ SheafActionRefinement.map a q p r comm := by
  subst p
  apply CategoryTheory.Functor.ext
  case h_obj => intro m; rfl
  intro m n f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply SheafActionPresentation.Arrow.ext
  change SheafTorsor.labelInv
      (((E.toGroupoid).map ((D.atlasMap E r rfl).map f)).map ≫ e.hom ≫
        SheafGroupoidAction.label) =
    SheafTorsor.labelInv ((D.toGroupoid.map f).map ≫ e.hom ≫ SheafGroupoidAction.label)
  rw [D.atlasMap_recovery]

/-- An atlas refinement recovers the original label-preserving refinement functor. -/
theorem toRefinement_refine (r : U ⟶ V)
    (D : SheafGroupoid.Chart (operations a e) (r ≫ q) (r ≫ q)) :
    D.atlasMap (T := X) E r rfl ⋙ toRefinement a e E =
      toRefinement a e D ⋙ SheafActionRefinement.refine a q r :=
  toRefinement_atlasMap a e D E r rfl

/-- The old atlas-change client requires only its action and commuting square. -/
theorem actionRefinementEquivalence_map (r : U ⟶ V) (comm : r ≫ q = p) :
    (SheafGroupoid.Chart.canonical (operations a (Iso.refl _)) p p).atlasMap (T := X)
        (SheafGroupoid.Chart.canonical (operations a (Iso.refl _)) q q) r comm ⋙
        (actionRefinementEquivalence a q).functor =
      (actionRefinementEquivalence a p).functor ⋙ SheafActionRefinement.map a q p r comm :=
  toRefinement_atlasMap a (Iso.refl _) _ _ r comm

end AtlasMap

end SquareKit.SheafGroupoidCompletion

namespace SquareKit.SheafSiteComparison
open CategoryTheory Opposite
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
variable [F.IsContinuous J K] [F.IsCocontinuous J K]
variable {G : Sheaf K GrpCat.{u}} {M A X Y : Sheaf K (Type u)}
variable (a : SheafActionQuotient.Action G M)
  (e : A ≅ SheafGroupoidAction.arrows (G := G) (M := M))

/-- Restrict an actual-arrow presentation through its recovered action charts. -/
def groupoidPresentationFunctor :
    (SheafGroupoidCompletion.operations a e).Object X ⥤
      SheafActionPresentation.Object (action J K F a) (sheaf J K F X) :=
  SheafGroupoidCompletion.toPresentation a e ⋙ presentationFunctor J K F a

theorem groupoidPresentation_quotient :
    groupoidPresentationFunctor (X := X) J K F a e ⋙
      SheafActionPresentation.quotient (action J K F a) =
    SheafGroupoidCompletion.quotient a e ⋙ quotientFunctor J K F a := rfl

omit [F.IsCocontinuous J K] in
theorem groupoidPresentation_restriction (r : Y ⟶ X) :
    (SheafGroupoidCompletion.operations a e).restriction r ⋙
      groupoidPresentationFunctor J K F a e =
    groupoidPresentationFunctor J K F a e ⋙
      SheafActionPresentation.restriction (action J K F a) (map J K F r) := rfl

variable [F.Full] [F.Faithful] [F.IsDenseSubsite J K]

/-- The original dense-site equivalence applies with exactly its original hypotheses. -/
def groupoidQuotientComparison :
    groupoidPresentationFunctor (X := X) J K F a e ⋙
      SheafActionPresentation.quotient (action J K F a) ≅
    SheafGroupoidCompletion.quotient a e ⋙ (quotientEquivalence J K F a).functor :=
  Iso.refl _

end SquareKit.SheafSiteComparison
