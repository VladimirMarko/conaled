import SquareKit.Internal.Cubical.Filling
import SquareKit.Internal.Cubical.PartialPaths
import SquareKit.Internal.Cubical.Substitution

/-! Transport chosen filling through a family isomorphism, deriving its laws. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def OpenBox.map {Γ : Context.{u}} {A B : Family (total (interval Γ))} {φ : Cofibration Γ}
    (η : A ⟶ B) (b : OpenBox A φ) : OpenBox B φ where
  tube := b.tube.map η
  base := Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements η) b.base
  boundary x h := congrArg (η.app ((endpointSub Γ false).mapElements.obj x)) (b.boundary x h)

def Filling.transport {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) (F : Filling A) : Filling B where
  fill p φ b := Term.map (Functor.whiskerLeft p.mapElements e.hom)
    (F.fill p φ (b.map (Functor.whiskerLeft p.mapElements e.inv)))

theorem Filling.transport_lawful {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B)
    (F : Filling A) (hF : F.Lawful) : (F.transport e).Lawful where
  fills p φ b := by
    have h := hF.fills p φ (b.map (Functor.whiskerLeft p.mapElements e.inv))
    constructor
    · apply Term.ext
      intro x
      exact (congrArg (e.hom.app ((endpointSub _ false ≫ p).mapElements.obj x))
        (congrArg (fun t => t.val x) h.1)).trans
          (congrArg (fun f => f.app ((endpointSub _ false ≫ p).mapElements.obj x) (b.base.val x)) e.inv_hom_id)
    · intro x hx
      exact (congrArg (e.hom.app (p.mapElements.obj x)) (h.2 x hx)).trans
        (congrArg (fun f => f.app (p.mapElements.obj x) (b.tube.val x hx)) e.inv_hom_id)
  uniform p φ b σ := by
    exact congrArg (Term.map (Functor.whiskerLeft
      (liftSub (interval _) σ ≫ p).mapElements e.hom))
      (hF.uniform p φ (b.map (Functor.whiskerLeft p.mapElements e.inv)) σ)

end SquareKit.Cubical.Presheaf
