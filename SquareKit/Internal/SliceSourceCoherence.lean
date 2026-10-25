import SquareKit.Internal.SliceSourceChange
import SquareKit.Internal.SliceRebase

/-! Source substitution coherence on the actual pseudo-slice categories. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {F : Type u₁} {B : Type u₂} {G : Type u₃} {H : Type u₄}
variable [Category.{v₁} F] [Category.{v₂} B] [Category.{v₃} G] [Category.{v₄} H]
variable [HasTerminal F] [HasTerminal G] [HasTerminal H]
variable [HasPullbacks F] [HasPullbacks G] [HasPullbacks H]
variable [CartesianMonoidalCategory B] [HasPullbacks B]
variable {h : GeometricMorphism F B} {a : B} [Closed a]
variable (f : GeometricMorphism G F) (g : GeometricMorphism H G)

/-- Associative source substitution compares the actual geometric lifts over the same composite. -/
def Lift.precompCompIso :
    (Lift.precompFunctor (h := h) (π := slice a) f ⋙ Lift.precompFunctor g) ⋙
      Lift.rebaseFunctor (h := g.comp (f.comp h)) (h' := (g.comp f).comp h)
        (Functor.associator h.inverseImage f.inverseImage g.inverseImage) ≅ Lift.precompFunctor (g.comp f) :=
  NatIso.ofComponents (fun k => {
    hom := Lift.homOfSection (by
      change (((k.precomp f).precomp g).rebase _).section = (k.precomp (g.comp f)).section
      rw [Lift.rebase_section]
      change _ ≫ 𝟙 _ = _
      rw [Category.comp_id, Lift.precomp_section, Lift.precomp_section, Lift.precomp_section, pullSection_comp])
    inv := Lift.homOfSection (by
      change (k.precomp (g.comp f)).section = (((k.precomp f).precomp g).rebase _).section
      rw [Lift.rebase_section]
      change _ = _ ≫ 𝟙 _
      rw [Category.comp_id, Lift.precomp_section, Lift.precomp_section, Lift.precomp_section, pullSection_comp])
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)

/-- Identity source substitution compares with the actual identity on lifts. -/
def Lift.precompIdentityIso :
    Lift.precompFunctor (h := h) (π := slice a) (identity F) ⋙
      Lift.rebaseFunctor (h := (identity F).comp h) (h' := h)
        (Functor.rightUnitor h.inverseImage) ≅ 𝟭 (Lift h (slice a)) :=
  NatIso.ofComponents (fun k => {
    hom := Lift.homOfSection (by
      change ((k.precomp (identity F)).rebase _).section = k.section
      rw [Lift.rebase_section]
      change _ ≫ 𝟙 _ = _
      rw [Category.comp_id, Lift.precomp_section, pullSection_identity])
    inv := Lift.homOfSection (by
      change k.section = ((k.precomp (identity F)).rebase _).section
      rw [Lift.rebase_section]
      change _ = _ ≫ 𝟙 _
      rw [Category.comp_id, Lift.precomp_section, pullSection_identity])
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)
end SquareKit.Internal.GeometricMorphism
