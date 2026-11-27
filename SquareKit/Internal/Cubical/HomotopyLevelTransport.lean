import SquareKit.Internal.Cubical.PropositionExtension
import SquareKit.Internal.Cubical.SelectedInverse

/-! Native homotopy-level closure retains complete equivalence witnesses.
The path comparison is derived from contractible based totals. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.HomotopyLevels
open CategoryTheory EquivalenceFamilies
universe u

/-- Complete witnesses form a native proposition, including at generic inhabited substitutions. -/
noncomputable def isEquivIsProp {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    Term (isProp (isEquiv f)) := by
  apply lam
  apply lam
  let W := isEquiv f
  let σ := projection (reindex W (projection W)) ≫ projection W
  let x := (generic W).reindex (projection (reindex W (projection W)))
  let y := generic (reindex W (projection W))
  exact pathOfContractible
    (EquivalencePaths.substitutedWitnessContractible f FA hFA FB hFB σ x)
    ((isEquivFilling f FA hFA FB hFB).reindex σ)
    ((isEquivFilling_lawful f FA hFA FB hFB).reindex σ) x y

namespace BasedPathMap
variable {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term A)
abbrev source := homogeneousPath (reindex A (projection A)) (generic A) (b.reindex (projection A))
abbrev target := homogeneousPath (reindex B (projection A))
  (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
  ((Term.map f b).reindex (projection A))
def map : source b ⟶ target f b :=
  pathMap (Functor.whiskerLeft (projection A).mapElements f) (generic A) (b.reindex (projection A))

/-- Both based totals are actual homotopy fibers, so the path map is an equivalence. -/
noncomputable def equivalence (E : HomotopyEquivalence f)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    HomotopyEquivalence (map f b) :=
  HomotopyEquivalence.ofContractibleTotals (map f b) FA hFA
    (pathFilling (FA.reindex (projection (interval _) ≫ projection A)) (hFA.reindex _) _ _)
    (pathFilling_lawful (FA.reindex (projection (interval _) ≫ projection A)) (hFA.reindex _) _ _)
    (pathFilling (FB.reindex (projection (interval _) ≫ projection A)) (hFB.reindex _) _ _)
    (pathFilling_lawful (FB.reindex (projection (interval _) ≫ projection A)) (hFB.reindex _) _ _)
    (NativePathSingleton.fiberAt (HomotopyEquivalence.ofIso (Iso.refl A)) b)
    (NativePathSingleton.fiberAt E (Term.map f b))
end BasedPathMap

/-- A genuine native equivalence induces equivalences on native path families. -/
noncomputable def pathMapEquivalence {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (E : HomotopyEquivalence f)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful)
    (a b : Term A) : HomotopyEquivalence (pathMap f a b) := by
  let σ := pair (𝟙 Γ) a
  let JA := homogeneousReindexIso (reindex A (projection A)) (generic A)
    (b.reindex (projection A)) σ
  let JB := homogeneousReindexIso (reindex B (projection A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    ((Term.map f b).reindex (projection A)) σ
  have h : JA.inv ≫ Functor.whiskerLeft σ.mapElements (BasedPathMap.map f b) ≫ JB.hom =
      pathMap f a b := by
    ext x p
    apply Subtype.ext
    apply PiElement.ext
    intro y g r
    exact congrArg (f.app y) (piInverseValue_map (A := interval (total A))
      (B := reindex (reindex A (projection A)) (projection (interval (total A))))
      σ p.val g r)
  rw [← h]
  exact ((BasedPathMap.equivalence f b E FA hFA FB hFB).reindex σ).conjugateIso JA.symm JB

/-- Reflect native proposition data through the selected inverse and its full left recovery. -/
noncomputable def sourceIsProp {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (E : HomotopyEquivalence f) (pB : Term (isProp B))
    (FA : Filling A) (hFA : FA.Lawful) : Term (isProp A) := by
  apply lam
  apply lam
  let σ := projection (reindex A (projection A)) ≫ projection A
  let x := (generic A).reindex (projection (reindex A (projection A)))
  let y := generic (reindex A (projection A))
  let f' := Functor.whiskerLeft σ.mapElements f
  let E' := E.reindex σ
  let cB := contractible (reindexProp pB σ) (Term.map f' x)
  let cA := cB.retract (FA.reindex σ) (hFA.reindex σ)
    E'.selectedInverse f' E'.selectedLeft
  exact pathOfContractible cA (FA.reindex σ) (hFA.reindex σ) x y

/-- Sethood reflects through a genuine homotopy equivalence, without a strict family iso. -/
noncomputable def sourceIsSet {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (E : HomotopyEquivalence f) (sB : Term (isSet B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    Term (isSet A) := by
  apply lam
  apply lam
  let σ := projection (reindex A (projection A)) ≫ projection A
  let x := (generic A).reindex (projection (reindex A (projection A)))
  let y := generic (reindex A (projection A))
  let f' := Functor.whiskerLeft σ.mapElements f
  exact sourceIsProp (pathMap f' x y)
    (pathMapEquivalence f' (E.reindex σ) (FA.reindex σ) (hFA.reindex σ)
      (FB.reindex σ) (hFB.reindex σ) x y)
    (pathIsPropAt (reindexSet sB σ) (Term.map f' x) (Term.map f' y))
    (pathFilling (FA.reindex (projection (interval _) ≫ σ)) (hFA.reindex _) x y)
    (pathFilling_lawful (FA.reindex (projection (interval _) ≫ σ)) (hFA.reindex _) x y)

/-- Sethood also transports forward along the same complete equivalence. -/
noncomputable def targetIsSet {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (E : HomotopyEquivalence f) (sA : Term (isSet A))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    Term (isSet B) :=
  sourceIsSet E.selectedInverse (E.selectedInverseEquivalence FA hFA FB hFB)
    sA FB hFB FA hFA

/-- A dependent proposition extension of a native set is a native set. -/
noncomputable def sigmaIsSet {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (sA : Term (isSet A)) (pB : Term (isProp B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    Term (isSet (sigma A B)) := by
  apply lam
  apply lam
  let M := sigma A B
  let σ := projection (reindex M (projection M)) ≫ projection M
  let x := (generic M).reindex (projection (reindex M (projection M)))
  let y := generic (reindex M (projection M))
  let B' := reindex B (liftSub A σ)
  let FM := sigmaFilling FA hFA FB
  have hFM := sigmaFilling_lawful FA hFA FB hFB
  exact sourceIsProp (pathMap (PropositionExtension.first B') x y)
    (PropositionExtension.pathEquivalence B' x y (reindexProp pB (liftSub A σ))
      (FA.reindex σ) (hFA.reindex σ) (FB.reindex (liftSub A σ)) (hFB.reindex _))
    (pathIsPropAt (reindexSet sA σ) (sigmaFst (B := B') x) (sigmaFst (B := B') y))
    (pathFilling (FM.reindex (projection (interval _) ≫ σ)) (hFM.reindex _) x y)
    (pathFilling_lawful (FM.reindex (projection (interval _) ≫ σ)) (hFM.reindex _) x y)

/-- The entire equivalence family is a set, including its chosen contractible-fiber witnesses. -/
noncomputable def equivIsSet {Γ : Context.{u}} {A B : Family Γ}
    (sB : Term (isSet B)) (FA : Filling A) (hFA : FA.Lawful)
    (FB : Filling B) (hFB : FB.Lawful) : Term (isSet (equiv A B)) :=
  sigmaIsSet (piIsSet (reindexSet sB (projection A)) FA hFA
    (FB.reindex (projection A)) (hFB.reindex _))
    (isEquivIsProp (universalMap A B)
      (FA.reindex (projection (maps A B))) (hFA.reindex _)
      (FB.reindex (projection (maps A B))) (hFB.reindex _))
    (mapsFilling FA hFA FB) (mapsFilling_lawful FA hFA FB hFB)
    (isEquivFilling (universalMap A B)
      (FA.reindex (projection (maps A B))) (hFA.reindex _)
      (FB.reindex (projection (maps A B))) (hFB.reindex _))
    (isEquivFilling_lawful (universalMap A B)
      (FA.reindex (projection (maps A B))) (hFA.reindex _)
      (FB.reindex (projection (maps A B))) (hFB.reindex _))

end SquareKit.Cubical.Presheaf.HomotopyLevels
