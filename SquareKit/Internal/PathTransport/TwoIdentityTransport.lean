import SquareKit.Internal.PathTransport.StrictTwoCategory
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid

/-! Transport of identity fibers retains all fiber 2-cells as arrows of the
hom-groupoid. Endpoint comparison uses strict inverses of 1-arrows. -/
namespace SquareKit.Internal.PathTransport.TwoIdentityTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {A : Type u} [Bicategory.{w,v} A] [Bicategory.Strict A]
variable {B : Type u'} [Bicategory.{w',v'} B] [Bicategory.Strict B]

/-- Transport a path by the strict fiber functor and the two endpoint arrows. -/
noncomputable def homTransport (F : StrictPseudofunctor A B) {a a' : A} {b b' : B}
    (u : F.obj a ⟶ b) [IsIso u] (v : F.obj a' ⟶ b') : (a ⟶ a') ⥤ (b ⟶ b') :=
  F.mapFunctor a a' ⋙ postcomp _ v ⋙ precomp _ (inv u)

/-- The inverse mate of an endpoint cell. The input cell remains genuine
2-dimensional data; no equality of its boundary arrows is assumed. -/
noncomputable def inverseMate [Bicategory.IsLocallyGroupoid B]
    {a a' b : B} {u : a ⟶ b} {u' : a' ⟶ b} [IsIso u] [IsIso u']
    {h : a ⟶ a'} (ρ : u ⟶ h ≫ u') : inv u ≫ h ⟶ inv u' :=
  eqToHom (by simp [Category.assoc]) ≫
    (inv u ◁ inv ρ) ▷ inv u' ≫ eqToHom (by simp)

/-- An ordinary functor between hom-groupoids acts strictly on their locally
discrete embeddings. It preserves the hom-groupoid arrows, which are the
original fiber's genuine 2-cells. -/
def locallyDiscreteFunctor {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) :
    StrictPseudofunctor (LocallyDiscrete C) (LocallyDiscrete D) where
  __ := F.toPseudofunctor
  map_id x := by apply Discrete.ext; exact F.map_id x.as
  map_comp f g := by apply Discrete.ext; exact F.map_comp f.as g.as
  mapId_eq_eqToIso x := by apply Iso.ext; apply Subsingleton.elim
  mapComp_eq_eqToIso f g := by apply Iso.ext; apply Subsingleton.elim

/-- Strict higher naturality induces a natural transformation on the full
hom-categories, using its 2-cell equation as ordinary naturality. -/
def homNaturality {F G : StrictPseudofunctor A B} (η : StrictTwoTransformation.Trans F G)
    (a a' : A) : F.mapFunctor a a' ⋙ postcomp _ (η.app a') ⟶
      G.mapFunctor a a' ⋙ precomp _ (η.app a) where
  app p := eqToHom (η.naturality p)
  naturality _ _ α := η.naturality₂ α

/-- The endpoint-cell pasting gives an actual natural transformation between
identity transports, including naturality at every genuine fiber 2-cell. -/
noncomputable def homComparison [Bicategory.IsLocallyGroupoid B]
    {F G : StrictPseudofunctor A B} (η : StrictTwoTransformation.Trans F G)
    {a a' : A} {b b' : B} {u : F.obj a ⟶ b} {u' : G.obj a ⟶ b}
    [IsIso u] [IsIso u'] {v : F.obj a' ⟶ b'} {v' : G.obj a' ⟶ b'}
    (ρ : u ⟶ η.app a ≫ u') (σ : v ⟶ η.app a' ≫ v') :
    homTransport F u v ⟶ homTransport G u' v' :=
  CategoryTheory.Functor.whiskerRight
    (CategoryTheory.Functor.whiskerLeft (F.mapFunctor a a') ((postcomposing _ _ _).map σ) ≫
      CategoryTheory.Functor.whiskerLeft (F.mapFunctor a a')
        (associatorNatIsoLeft _ (η.app a') v').inv ≫
      CategoryTheory.Functor.whiskerRight (homNaturality η a a') (postcomp _ v') ≫
      CategoryTheory.Functor.whiskerLeft (G.mapFunctor a a')
        (associatorNatIsoMiddle (η.app a) v').hom)
    (precomp _ (inv u)) ≫
  CategoryTheory.Functor.whiskerLeft (G.mapFunctor a a' ⋙ postcomp _ v')
    (associatorNatIsoRight (inv u) (η.app a) b').inv ≫
  CategoryTheory.Functor.whiskerLeft (G.mapFunctor a a' ⋙ postcomp _ v')
    ((precomposing _ _ _).map (inverseMate ρ))

/-- A natural transformation of hom-groupoids is a strict higher
transformation between their locally discrete embeddings. -/
def locallyDiscreteTrans {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (η : F ⟶ G) :
    StrictTwoTransformation.Trans (locallyDiscreteFunctor F) (locallyDiscreteFunctor G) where
  app a := Discrete.mk (η.app a.as)
  naturality f := Discrete.ext (η.naturality f.as)
  naturality₂ _ := Subsingleton.elim _ _

theorem homComparison_id [Bicategory.IsLocallyGroupoid B]
    (F : StrictPseudofunctor A B) {a a' : A} {b b' : B}
    (u : F.obj a ⟶ b) [IsIso u] (v : F.obj a' ⟶ b') :
    homComparison (StrictTwoTransformation.Trans.id F)
      (eqToHom (Category.id_comp u).symm) (eqToHom (Category.id_comp v).symm) =
        𝟙 (homTransport F u v) := by
  ext p
  simp [homComparison, homNaturality, inverseMate, StrictTwoTransformation.Trans.id,
    Strict.associator_eqToIso, Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso]

/-- The locally discrete embedding preserves every ordinary category arrow
as a 1-arrow; only its next dimension is discrete. -/
def locallyDiscreteEmbedding : StrictPseudofunctor Cat StrictTwoCategory :=
  StrictPseudofunctor.mk'' {
    obj := fun C => ⟨LocallyDiscrete C⟩
    map := fun F => locallyDiscreteFunctor F.toFunctor
    map₂ := fun η => locallyDiscreteTrans η.toNatTrans
    map₂_id := fun F => by apply StrictTwoTransformation.Trans.ext; intro a; rfl
    map₂_comp := fun η θ => by apply StrictTwoTransformation.Trans.ext; intro a; rfl
    map_id := fun C => by
      apply StrictTwoTransformation.functor_ext
      dsimp only [locallyDiscreteFunctor, Functor.toPseudofunctor,
        pseudofunctorOfIsLocallyDiscrete, StrictPseudofunctor.id,
        StrictlyUnitaryPseudofunctor.id, Pseudofunctor.id, PrelaxFunctor.id]
      congr 2
      funext a b f g η
      exact Subsingleton.elim _ _
    map_comp := fun F G => StrictTwoTransformation.functor_ext rfl
    map₂_whisker_left := fun F G H η => by
      apply StrictTwoTransformation.Trans.ext; intro a
      repeat rw [StrictTwoTransformation.Trans.comp_app]
      repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
      change (show (LocallyDiscrete.mk (G.toFunctor.obj (F.toFunctor.obj a.as))) ⟶
        (LocallyDiscrete.mk (H.toFunctor.obj (F.toFunctor.obj a.as))) from
        Discrete.mk (η.toNatTrans.app (F.toFunctor.obj a.as))) =
        𝟙 _ ≫ (show _ ⟶ _ from Discrete.mk (η.toNatTrans.app (F.toFunctor.obj a.as))) ≫ 𝟙 _
      simp
    map₂_whisker_right := fun {a b c} {G H} η F => by
      apply StrictTwoTransformation.Trans.ext; intro a
      repeat rw [StrictTwoTransformation.Trans.comp_app]
      repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
      change (show (LocallyDiscrete.mk (F.toFunctor.obj (G.toFunctor.obj a.as))) ⟶
        (LocallyDiscrete.mk (F.toFunctor.obj (H.toFunctor.obj a.as))) from
        Discrete.mk (F.toFunctor.map (η.toNatTrans.app a.as))) =
        𝟙 _ ≫ (show _ ⟶ _ from Discrete.mk (F.toFunctor.map (η.toNatTrans.app a.as))) ≫ 𝟙 _
      simp
  }

end SquareKit.Internal.PathTransport.TwoIdentityTransport
