import SquareKit.Internal.Cubical.DiscreteEquivalences
import SquareKit.Internal.Cubical.EquivalenceWitnessSubstitution
import SquareKit.Internal.Cubical.EquivalencePaths
import SquareKit.Internal.Cubical.NativeEquivalenceLine

/-! The inverse map selected by the supplied native fiber centers. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace HomotopyEquivalence
variable {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}

/-- No discreteness or universe admission is required by the center projection. -/
def selectedInverse (E : HomotopyEquivalence f) : B ⟶ A := E.discreteInverse

/-- The right recovery path is the path component of that very fiber center. -/
def selectedRight (E : HomotopyEquivalence f) :
    Term (homogeneousPath (Presheaf.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements E.selectedInverse) (generic B)))
      (generic B)) := genericFiberPath f (𝟙 (total B)) E.fibers.center

private def firstMap {Δ : Context.{u}} (C : Family Δ) (D : Family (total C)) : sigma C D ⟶ C where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := rfl

/-- Project the original fiber contraction at `(a,refl)`; neither an arbitrary
quasi-inverse nor triangle coherence is supplied. -/
def selectedLeft (E : HomotopyEquivalence f) :
    Term (homogeneousPath (Presheaf.reindex A (projection A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements E.selectedInverse)
        (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)))
      (generic A)) := by
  let τ := pair (projection A) (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
  let z := genericFiberIntro f τ (generic A)
    (homogeneousRefl (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)))
  exact homogeneousPathMap
    (firstMap (Presheaf.reindex A (τ ≫ projection B))
      (Presheaf.reindex (genericFiberPathFamily f) (liftSub (Presheaf.reindex A (projection B)) τ)))
    ((E.fibers.reindex τ).pathTo z)

/-- Every supplied right inverse is joined to the exact selected center map by
projection of the supplied fiber contraction. -/
def selectedComparison (E : HomotopyEquivalence f) (g : B ⟶ A)
    (h : Term (homogeneousPath (Presheaf.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)))
      (generic B))) :
    Term (homogeneousPath (Presheaf.reindex A (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements E.selectedInverse) (generic B))) :=
  homogeneousReverse (homogeneousPathMap
    (firstMap (Presheaf.reindex A (projection B)) (genericFiberPathFamily f))
    (E.fibers.pathTo (genericFiberIntro f (𝟙 (total B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)) h)))

namespace MapHomotopyFiberLine
open EquivalenceFamilies
variable (g : A ⟶ B)
  (H : Term (homogeneousPath (Presheaf.reindex B (projection A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements g) (generic A))))

abbrev baseSub : total (interval (total B)) ⟶ Γ :=
  projection (interval (total B)) ≫ projection B

def movingMap : Presheaf.reindex A (baseSub (B := B)) ⟶
    Presheaf.reindex B (baseSub (B := B)) :=
  EquivalenceFamilies.decodeMap (Term.map (piReindex A (Presheaf.reindex B (projection A)) baseSub)
    ((EquivalencePaths.mapLine f g H).reindex (liftSub (interval Γ) (projection B))))

abbrev line := homotopyFiber (movingMap g H) ((generic B).reindex (projection (interval (total B))))

def fiberReindexIso {Ξ Ω : Context.{u}} {C D : Family Ξ} (k : C ⟶ D) (b : Term D)
    (σ : Ω ⟶ Ξ) : Presheaf.reindex (homotopyFiber k b) σ ≅
      homotopyFiber (Functor.whiskerLeft σ.mapElements k) (b.reindex σ) :=
  sigmaSecondIso _ (pathReindexIso
    (Presheaf.reindex (Presheaf.reindex D (projection C)) (projection (interval (total C))))
    (Term.map (Functor.whiskerLeft (projection C).mapElements k) (generic C))
    (b.reindex (projection C)) (liftSub C σ))

theorem movingMap_zero :
    Functor.whiskerLeft (endpointSub (total B) false).mapElements (movingMap g H) =
      Functor.whiskerLeft (projection B).mapElements f := by
  ext x a
  exact congrArg (fun t => (t.val ((projection B).mapElements.obj x)).val (𝟙 _) a)
    (EquivalencePaths.mapLine_zero f g H)

theorem movingMap_one :
    Functor.whiskerLeft (endpointSub (total B) true).mapElements (movingMap g H) =
      Functor.whiskerLeft (projection B).mapElements g := by
  ext x a
  exact congrArg (fun t => (t.val ((projection B).mapElements.obj x)).val (𝟙 _) a)
    (EquivalencePaths.mapLine_one f g H)

def start : Presheaf.reindex (line g H) (endpointSub (total B) false) ≅
    homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B) :=
  fiberReindexIso (movingMap g H) _ (endpointSub (total B) false) ≪≫
    eqToIso (congrArg (fun k => homotopyFiber k (generic B)) (movingMap_zero g H))

def finish : Presheaf.reindex (line g H) (endpointSub (total B) true) ≅
    homotopyFiber (Functor.whiskerLeft (projection B).mapElements g) (generic B) :=
  fiberReindexIso (movingMap g H) _ (endpointSub (total B) true) ≪≫
    eqToIso (congrArg (fun k => homotopyFiber k (generic B)) (movingMap_one g H))

variable (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful)
noncomputable def filling : Filling (line g H) :=
  homotopyFiberFilling (movingMap g H) _ (FA.reindex baseSub) (hFA.reindex _)
    (FB.reindex baseSub) (hFB.reindex _)
theorem filling_lawful : (filling g H FA hFA FB hFB).Lawful :=
  homotopyFiberFilling_lawful _ _ _ _ _ _
noncomputable def map := (start g H).inv ≫ IntervalTransport.map (filling g H FA hFA FB hFB) ≫
  (finish g H).hom
noncomputable def equivalence : HomotopyEquivalence (map g H FA hFA FB hFB) :=
  (IntervalTransport.equivalence (filling g H FA hFA FB hFB)
    (filling_lawful g H FA hFA FB hFB)).conjugateIso (start g H).symm (finish g H)
end MapHomotopyFiberLine

/-- Transfer the supplied contraction along the filled family of native fibers. -/
noncomputable def ofMapHomotopy (g : A ⟶ B)
    (H : Term (homogeneousPath (Presheaf.reindex B (projection A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements g) (generic A))))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful)
    (E : HomotopyEquivalence f) : HomotopyEquivalence g where
  fibers := E.fibers.retract (genericFiberFilling g FA hFA FB hFB)
    (genericFiberFilling_lawful g FA hFA FB hFB)
    (MapHomotopyFiberLine.map g H FA hFA FB hFB)
    (MapHomotopyFiberLine.equivalence g H FA hFA FB hFB).selectedInverse
    (MapHomotopyFiberLine.equivalence g H FA hFA FB hFB).selectedRight

/-- The inverse selected by the original fiber centers has genuine contractible
fibers. The auxiliary Glue transport is used only to construct that witness. -/
noncomputable def selectedInverseEquivalence (E : HomotopyEquivalence f)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    HomotopyEquivalence E.selectedInverse :=
  (NativeEquivalenceLine.auxiliaryEquivalence f E FA hFA FB hFB).ofMapHomotopy
    E.selectedInverse
    (E.selectedComparison (NativeEquivalenceLine.auxiliary f E FA hFA FB hFB)
      (NativeEquivalenceLine.auxiliaryRight f E FA hFA FB hFB))
    FB hFB FA hFA

end HomotopyEquivalence
end SquareKit.Cubical.Presheaf
