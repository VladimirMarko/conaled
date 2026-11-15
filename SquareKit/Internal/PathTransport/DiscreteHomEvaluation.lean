import SquareKit.Internal.PathTransport.CechMatchingComprehensionIdentityEvaluation

/-! A discrete evaluation is effective when its values recover a fully faithful hom map. -/
noncomputable section
namespace SquareKit.Internal.PathTransport
open CategoryTheory
universe u v w z
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{v} D]

def homEndpointEquiv {a b c d : D} (h : a = c) (k : b = d) : (a ⟶ b) ≃ (c ⟶ d) where
  toFun p := eqToHom h.symm ≫ p ≫ eqToHom k
  invFun p := eqToHom h ≫ p ≫ eqToHom k.symm
  left_inv p := by simp [Category.assoc]
  right_inv p := by simp [Category.assoc]

theorem discreteHomEvaluation_isEquivalence (R : C ⥤ D) [R.Full] [R.Faithful]
    (x y : C) {a b : D} (hx : R.obj x = a) (hy : R.obj y = b)
    {I : Type z} (e : I ≃ (a ⟶ b)) (F : Discrete (x ⟶ y) ⥤ Discrete I)
    (hF : ∀ p, e (F.obj (Discrete.mk p)).as = eqToHom hx.symm ≫ R.map p ≫ eqToHom hy) :
    F.IsEquivalence := by
  let k := ((Functor.FullyFaithful.ofFullyFaithful R).homEquiv (X := x) (Y := y)).trans
    ((homEndpointEquiv hx hy).trans e.symm)
  let J := Discrete.equivalence k
  have hi : J.functor ≅ F := Discrete.natIso fun p => eqToIso (by
    apply Discrete.ext
    apply e.injective
    exact (e.apply_symm_apply _).trans (hF p.as).symm)
  let : J.functor.IsEquivalence := J.isEquivalence_functor
  exact Functor.isEquivalence_of_iso hi

end SquareKit.Internal.PathTransport
