import SquareKit.Internal.ClassifierSourceChange
import SquareKit.Internal.PartitionTransform

/-! Identity and composition comparisons for the source model functors. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {F : Type u₁} {B : Type u₂} {G : Type u₃} {H : Type u₄}
variable [Category.{v₁} F] [Category.{v₂} B] [Category.{v₃} G] [Category.{v₄} H]
variable [CartesianMonoidalCategory F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable [CartesianMonoidalCategory G] [HasPullbacks G] [FinitaryExtensive G]
variable [HasTerminal H] [HasBinaryProducts H] [HasPullbacks H] [FinitaryExtensive H]
variable (g : GeometricMorphism H G) (f : GeometricMorphism G F) (h : GeometricMorphism F B)
variable {U : B} (u : U ⟶ ⊤_ B) [Mono u]

/-- Source composition is compared on both carriers, including parameter normalization. -/
def sourceModelCompIso :
    sourceModelFunctor f h u ⋙ sourceModelFunctor g (f.comp h) u ≅
      sourceModelFunctor (g.comp f) h u :=
  NatIso.ofComponents (fun M => {
    hom := ⟨𝟙 _, 𝟙 _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    inv := ⟨𝟙 _, 𝟙 _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)

/-- Identity source substitution compares with the identity without changing either predicate carrier. -/
def sourceModelIdentityIso : sourceModelFunctor (identity F) h u ≅
    𝟭 (PartitionSection.Model (parameterPullback h u)) :=
  NatIso.ofComponents (fun M => {
    hom := ⟨𝟙 _, 𝟙 _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    inv := ⟨𝟙 _, 𝟙 _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄} {E : Type u₅}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D] [Category.{v₅} E]
variable [CartesianMonoidalCategory A] [HasPullbacks A] [FinitaryExtensive A]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable [CartesianMonoidalCategory C] [HasPullbacks C] [FinitaryExtensive C]
variable [CartesianMonoidalCategory D] [HasPullbacks D] [FinitaryExtensive D]
variable [CartesianMonoidalCategory E] [HasPullbacks E] [FinitaryExtensive E]
variable (f : GeometricMorphism B A) (g : GeometricMorphism C B) (k : GeometricMorphism D C)
variable (h : GeometricMorphism A E) {U : E} (u : U ⟶ ⊤_ E) [Mono u]

/-- The source composition comparisons satisfy the associativity diagram. -/
theorem sourceModel_associativity :
    whiskerRight (sourceModelCompIso g f h u).hom (sourceModelFunctor k (g.comp (f.comp h)) u) ≫
      (sourceModelCompIso k (g.comp f) h u).hom =
        (Functor.associator (sourceModelFunctor f h u) (sourceModelFunctor g (f.comp h) u)
          (sourceModelFunctor k (g.comp (f.comp h)) u)).hom ≫
          whiskerLeft (sourceModelFunctor f h u) (sourceModelCompIso k g (f.comp h) u).hom ≫
            (sourceModelCompIso (k.comp g) f h u).hom := by
  apply NatTrans.ext
  funext M
  apply Subsingleton.elim

/-- The right unit comparison is compatible with source composition. -/
theorem sourceModel_right_unit :
    (sourceModelCompIso (identity B) f h u).hom =
      whiskerLeft (sourceModelFunctor f h u) (sourceModelIdentityIso (f.comp h) u).hom ≫
        (Functor.rightUnitor (sourceModelFunctor f h u)).hom := by
  apply NatTrans.ext
  funext M
  apply Subsingleton.elim

/-- The left unit comparison is compatible with source composition. -/
theorem sourceModel_left_unit :
    (sourceModelCompIso f (identity A) h u).hom =
      whiskerRight (sourceModelIdentityIso h u).hom (sourceModelFunctor f h u) ≫
        (Functor.leftUnitor (sourceModelFunctor f h u)).hom := by
  apply NatTrans.ext
  funext M
  apply Subsingleton.elim
end SquareKit.Internal.GeometricMorphism
