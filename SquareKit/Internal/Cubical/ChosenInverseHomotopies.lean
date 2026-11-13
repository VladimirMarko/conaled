import SquareKit.Internal.Cubical.NativePathSingleton
import SquareKit.Internal.Cubical.HomotopyRetracts

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

private def sigmaFirstMap {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) :
    sigma A B ⟶ A where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := rfl

/-- A supplied right inverse of a genuine native equivalence also has a native
left-inverse homotopy. The supplied inverse and its right-inverse path are retained. -/
noncomputable def HomotopyEquivalence.chosenLeftInverse
    {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B} (E : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (g : B ⟶ A)
    (h : Term (homogeneousPath (Presheaf.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)))
      (generic B))) :
    Term (homogeneousPath (Presheaf.reindex A (projection A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements g)
        (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)))
      (generic A)) := by
  let σ := projection A
  let a := generic A
  let f' := Functor.whiskerLeft σ.mapElements f
  let g' := Functor.whiskerLeft σ.mapElements g
  let b := Term.map f' a
  let τ := pair σ b
  let q := Term.map (pathReindexIso
    (Presheaf.reindex (Presheaf.reindex B (projection B)) (projection (interval (total B))))
    (Term.map (Functor.whiskerLeft (projection B).mapElements f)
      (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)))
    (generic B) τ).hom (h.reindex τ)
  let c := NativePathSingleton.fiberAt (E.reindex σ) b
  let z₀ := homotopyFiberIntro f' b (Term.map g' b) q
  let z₁ := homotopyFiberIntro f' b a (homogeneousRefl b)
  let π := sigmaFirstMap (Presheaf.reindex A σ)
    (homogeneousPath (Presheaf.reindex (Presheaf.reindex B σ) (projection (Presheaf.reindex A σ)))
      (Term.map (Functor.whiskerLeft (projection (Presheaf.reindex A σ)).mapElements f')
        (generic (Presheaf.reindex A σ))) (b.reindex (projection (Presheaf.reindex A σ))))
  let p₀ := homogeneousPathMap π (c.pathTo z₀)
  let p₁ := homogeneousPathMap π (c.pathTo z₁)
  exact homogeneousConcat (F.reindex σ) (hF.reindex σ)
    (Term.map (NativePathSingleton.reverseIso _ _).hom p₀) p₁

end SquareKit.Cubical.Presheaf
