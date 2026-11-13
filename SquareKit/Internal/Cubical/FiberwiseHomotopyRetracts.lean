import SquareKit.Internal.Cubical.HomotopyRetracts
import SquareKit.Internal.Cubical.ContractibleTotals

/-! A fiberwise native homotopy induces a homotopy on dependent totals. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace FiberwiseHomotopyRetracts
variable {Γ : Context.{u}} {X : Family Γ} {A B : Family (total X)}

/-- Reassociate a generic total-space point without changing either component. -/
def totalPoint : total (sigma X B) ⟶ total B where
  app _ := TypeCat.ofHom (fun z => ⟨⟨z.1,z.2.1⟩,z.2.2⟩)
  naturality := by intros; rfl

variable (f : A ⟶ B) (g : B ⟶ A)
  (h : Term (homogeneousPath (Presheaf.reindex B (projection B))
    (Term.map (Functor.whiskerLeft (projection B).mapElements f)
      (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)))
    (generic B)))

/-- Lift the supplied fiberwise homotopy with constant base coordinate. -/
def totalHomotopy : Term (homogeneousPath
    (reindex (sigma X B) (projection (sigma X B)))
    (Term.map (Functor.whiskerLeft (projection (sigma X B)).mapElements (sigmaSecondMap X f))
      (Term.map (Functor.whiskerLeft (projection (sigma X B)).mapElements (sigmaSecondMap X g))
        (generic (sigma X B))))
    (generic (sigma X B))) := by
  let τ := totalPoint (X := X) (B := B)
  let p := Term.map (pathReindexIso
    (reindex (reindex B (projection B)) (projection (interval (total B))))
    (Term.map (Functor.whiskerLeft (projection B).mapElements f)
      (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)))
    (generic B) τ).hom (h.reindex τ)
  let q := ContractibleTotals.verticalPath (τ ≫ projection B) p
  exact pathLam (pathApp q) (pathApp_zero q) (pathApp_one q)

end FiberwiseHomotopyRetracts

/-- Contractibility passes along a fiberwise homotopy retract of dependent totals.
The total homotopy is constructed from the supplied fiberwise one. -/
noncomputable def HomotopyContractible.fiberwiseRetract
    {Γ : Context.{u}} {X : Family Γ} {A B : Family (total X)}
    (c : HomotopyContractible (sigma X A))
    (FX : Filling X) (hFX : FX.Lawful) (FB : Filling B) (hFB : FB.Lawful)
    (f : A ⟶ B) (g : B ⟶ A)
    (h : Term (homogeneousPath (Presheaf.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)))
      (generic B))) : HomotopyContractible (sigma X B) :=
  c.retract (sigmaFilling FX hFX FB) (sigmaFilling_lawful FX hFX FB hFB)
    (sigmaSecondMap X f) (sigmaSecondMap X g)
    (FiberwiseHomotopyRetracts.totalHomotopy f g h)

end SquareKit.Cubical.Presheaf
