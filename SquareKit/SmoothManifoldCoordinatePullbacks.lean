import SquareKit.SmoothOpenCoordinatePullbacks
import SquareKit.SmoothManifoldPrincipalMaps

/-! Coordinate pullback squares for the actual realization of ordinary open
manifolds. All comparison maps are the existing principal-open isomorphisms. -/
noncomputable section
namespace SquareKit.ManifoldRealization.Coordinates
open CategoryTheory CategoryTheory.Limits EuclideanOpen SmoothAlgebra

/-- The actual manifold realization of an ordinary principal-open map. -/
abbrev realize {U V : Domain} (f : U ⟶ V) :=
  map (show ordinaryOpen U → ordinaryOpen V from fun x => (show EuclideanOpen.Map U V from f) x)
    (euclideanOpenMap_contMDiff f)

def ordinaryPowerIso (n : ℕ) : object n (ordinaryOpen (full n)) ≅ SmoothOpenSite.scalarPower n :=
  principalIso (full n) ≪≫ fullPowerIso n

theorem comparison {U V : Domain} (f : U ⟶ V) :
    realize f ≫ (principalIso V).hom = (principalIso U).hom ≫ embedding.map f :=
  principalIso_naturality f

/-- Transfer an established all-stage principal square, without a general
product-preservation assumption on manifold realization. -/
theorem realized_isPullback {P X Y Z : Domain} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback (embedding.map fst) (embedding.map snd) (embedding.map f) (embedding.map g)) :
    IsPullback (realize fst) (realize snd) (realize f) (realize g) :=
  h.of_iso' (principalIso P) (principalIso X) (principalIso Y) (principalIso Z)
    (comparison fst).symm (comparison snd).symm (comparison f).symm (comparison g).symm

theorem product_isPullback (n k : ℕ) :
    IsPullback (realize (EuclideanOpen.Coordinates.first n k))
      (realize (EuclideanOpen.Coordinates.last n k))
      (realize (EuclideanOpen.Coordinates.toPoint n)) (realize (EuclideanOpen.Coordinates.toPoint k)) :=
  realized_isPullback _ _ _ _ (EuclideanOpen.Coordinates.product_isPullback n k)

theorem zero_fiber_isPullback (n k : ℕ) :
    IsPullback (realize (EuclideanOpen.Coordinates.insertZero n k))
      (realize (EuclideanOpen.Coordinates.toPoint n))
      (realize (EuclideanOpen.Coordinates.last n k)) (realize (EuclideanOpen.Coordinates.zero k)) :=
  realized_isPullback _ _ _ _ (EuclideanOpen.Coordinates.zero_fiber_isPullback n k)

theorem restricted_zero_fiber_isPullback (n k : ℕ) (q : freeAlgebra (n+k)) :
    IsPullback (realize (inverseRestriction (EuclideanOpen.Coordinates.insertZero n k) q))
      (realize (subInclusion (full n) (inverseDefining (EuclideanOpen.Coordinates.insertZero n k) q) ≫
        EuclideanOpen.Coordinates.toPoint n))
      (realize (subInclusion (full (n+k)) q ≫ EuclideanOpen.Coordinates.last n k))
      (realize (EuclideanOpen.Coordinates.zero k)) :=
  realized_isPullback _ _ _ _ (EuclideanOpen.Coordinates.restricted_zero_fiber_isPullback n k q)

end SquareKit.ManifoldRealization.Coordinates
