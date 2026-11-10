import SquareKit.Internal.PathTransport.ComparisonInterpretation
import SquareKit.GrothendieckEquivalence

/-! Conditional equivalence laws for the existing comparison operations. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

namespace Family
variable {Γ Δ : Context.{u}}

def FiberEquivalences (A : Family Γ) : Prop := ∀ γ, (A.map.app γ).IsEquivalence

theorem extend_equivalence (A : Family Γ) [Γ.map.IsEquivalence]
    (h : A.FiberEquivalences) : A.extend.map.IsEquivalence := by
  let (γ : Γ.left) := h γ
  let (γ : Γ.left) : ((whiskerRight A.map Grpd.forgetToCat).app γ).toFunctor.IsEquivalence := h γ
  exact (GrothendieckEquivalence.extendEquivalence Γ.map.asEquivalence
    (A.right ⋙ Grpd.forgetToCat) (whiskerRight A.map Grpd.forgetToCat)).isEquivalence_functor

private theorem post_eq_equivalence {C D E : Grpd.{u,u}} (F : C ⥤ D)
    (h : D = E) [F.IsEquivalence] : (F ⋙ eqToHom h).IsEquivalence := by
  cases h
  exact inferInstanceAs F.IsEquivalence

theorem reindex_equivalences (A : Family Γ) (h : A.FiberEquivalences)
    (σ : Substitution Δ Γ) : (A.reindex σ).FiberEquivalences := by
  intro δ
  let := h (σ.left.obj δ)
  change ((A.map.app (σ.left.obj δ)) ⋙
    (eqToHom (congrArg (· ⋙ A.right) σ.commutes)).app δ).IsEquivalence
  rw [eqToHom_app]
  exact post_eq_equivalence _ _

theorem identity_equivalences (A : Family Γ) (h : A.FiberEquivalences)
    (x y : Section A) : (A.identity x y).FiberEquivalences := by
  intro γ
  let := h γ
  let e := GrothendieckEquivalence.identityEquiv (A.map.app γ) (x.left.obj γ) (y.left.obj γ)
  have hi : ((identityMap A.map x.left y.left).app γ).IsEquivalence :=
    (Discrete.equivalence e).isEquivalence_functor
  let := hi
  dsimp only [identity, NatTrans.comp_app]
  rw [eqToHom_app]
  exact post_eq_equivalence _ _

end Family
end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
