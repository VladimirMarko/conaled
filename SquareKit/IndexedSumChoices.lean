import SquareKit.IndexedSumBaseChange

/-! Changing the chosen left adjoint preserves selected introductions through
Mathlib's canonical adjoint comparison. A tagged representation exercises it. -/
noncomputable section
open CategoryTheory Limits ConcreteCategory
namespace SquareKit.AdjointComparison
universe u₁ u₂ v₁ v₂
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {L M : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (b : M ⊣ R)

/-- The selected introduction, transposed using either left adjoint, agrees. -/
theorem left_uncurry {X : C} {Y : D} (k : X ⟶ R.obj Y) :
    (a.leftAdjointUniq b).hom.app X ≫ (b.homEquiv X Y).symm k =
      (a.homEquiv X Y).symm k := by
  apply (a.homEquiv X Y).injective
  rw [a.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [← b.homEquiv_unit, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
end SquareKit.AdjointComparison

namespace SquareKit.IndexedSumBaseChange
universe u v
section ChoiceTransport
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {A B A' B' : C} {f : A ⟶ B} {g : B' ⟶ B} {f' : A' ⟶ B'} {g' : A' ⟶ A}
variable (h : IsPullback f' g' g f)
variable {L : Over B' ⥤ Over B} {L' : Over A' ⥤ Over A}
variable (a : L ⊣ Over.pullback g) (a' : L' ⊣ Over.pullback g')

/-- Base change for any other chosen sums, transported by canonical uniqueness. -/
def withSumChoices : Over.pullback f' ⋙ L' ≅ L ⋙ Over.pullback f :=
  Functor.isoWhiskerLeft (Over.pullback f')
    ((Over.mapPullbackAdj g').leftAdjointUniq a').symm ≪≫
  DependentBaseChange.leftComparison h ≪≫
  Functor.isoWhiskerRight ((Over.mapPullbackAdj g).leftAdjointUniq a) (Over.pullback f)

/-- Changing sums before or after base change gives the same selected map. -/
theorem choices_agree (X : Over B') :
    (((Over.mapPullbackAdj g').leftAdjointUniq a').hom.app ((Over.pullback f').obj X)) ≫
      (withSumChoices h a a').hom.app X =
    (DependentBaseChange.leftComparison h).hom.app X ≫
      (Over.pullback f).map (((Over.mapPullbackAdj g).leftAdjointUniq a).hom.app X) := by
  simp [withSumChoices]
end ChoiceTransport

variable {B : Type u}

/-- An alternative slice representation with an explicit, observationally irrelevant tag. -/
def tagged : Over B ⥤ Over B where
  obj X := Over.mk (↾fun p : PUnit × X.left => X.hom p.2)
  map k := Over.homMk (↾fun p => (p.1, k.left p.2)) (by ext p; exact congr_hom (Over.w k) p.2)
  map_id X := by ext p; rfl
  map_comp f g := by ext p; rfl

/-- Packing and unpacking the tag is a natural isomorphism of slice representations. -/
def tagging : 𝟭 (Over B) ≅ tagged :=
  NatIso.ofComponents (fun X => {
    hom := Over.homMk (↾fun x => (PUnit.unit, x)) (by rfl)
    inv := Over.homMk (↾fun p => p.2) (by rfl)
    hom_inv_id := by ext x; rfl
    inv_hom_id := by ext p; cases p with | mk t x => cases t; rfl }) (by
      intro X Y k
      ext x
      rfl)

variable {A : Type u} (g : A ⟶ B)

/-- The alternative sum functor has different carriers, but the same right adjoint. -/
def taggedSum : Over A ⥤ Over B := Over.map g ⋙ tagged

def sumTagging : Over.map g ≅ taggedSum g := Functor.isoWhiskerLeft (Over.map g) tagging

def taggedAdjunction : taggedSum g ⊣ Over.pullback g :=
  (Over.mapPullbackAdj g).ofNatIsoLeft (sumTagging g)

/-- The canonical adjoint-uniqueness comparison is the concrete tag insertion. -/
theorem canonical_tagging :
    (Over.mapPullbackAdj g).leftAdjointUniq (taggedAdjunction g) = sumTagging g := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply ((Over.mapPullbackAdj g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  change (taggedAdjunction g).unit.app X =
    (Over.mapPullbackAdj g).homEquiv _ _ ((sumTagging g).hom.app X)
  rw [Adjunction.homEquiv_unit]
  rfl

/-- A chosen value survives canonical comparison, including its dependent fiber. -/
theorem selected_tagging (X : Over A) (x : X.left) :
    (((Over.mapPullbackAdj g).leftAdjointUniq (taggedAdjunction g)).hom.app X).left x =
      (PUnit.unit, x) := by
  rw [canonical_tagging]
  rfl
end SquareKit.IndexedSumBaseChange
