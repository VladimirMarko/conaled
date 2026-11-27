import SquareKit.Internal.Cubical.CartesianPropositionExtension
import SquareKit.Internal.Cubical.CartesianNativeStructurePreservation

/-! Native homotopy-level closure retains complete equivalence witnesses.
The path comparison is derived from contractible based totals. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.HomotopyLevels
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
  let x := Term.reindex (generic W) (projection (reindex W (projection W)))
  let y := generic (reindex W (projection W))
  exact pathOfContractible
    (EquivalencePaths.substitutedWitnessContractible f FA hFA FB hFB σ x)
    ((isEquivFilling f FA hFA FB hFB).reindex σ)
    ((isEquivFilling_lawful f FA hFA FB hFB).reindex σ) x y

namespace BasedPathMap
variable {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term A)
abbrev source := homogeneousPath (reindex A (projection A)) (generic A) (Term.reindex b (projection A))
abbrev target := homogeneousPath (reindex B (projection A))
  (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
  (Term.reindex (Term.map f b) (projection A))
def map : source b ⟶ target f b :=
  pathMap (Functor.whiskerLeft (projection A).mapElements f) (generic A) (Term.reindex b (projection A))

/-- Both based totals are actual homotopy fibers, so the path map is an equivalence. -/
noncomputable def equivalence (E : HomotopyEquivalence f)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    HomotopyEquivalence (map f b) :=
  HomotopyEquivalence.ofContractibleTotals (map f b) FA hFA
    (pathFilling (FA.reindex (projection (interval _) ≫ projection A)) (hFA.reindex _) _ _)
    (pathFilling_lawful (FA.reindex (projection (interval _) ≫ projection A)) (hFA.reindex _) _ _)
    (pathFilling (FB.reindex (projection (interval _) ≫ projection A)) (hFB.reindex _) _ _)
    (pathFilling_lawful (FB.reindex (projection (interval _) ≫ projection A)) (hFB.reindex _) _ _)
    (HomotopyEquivalence.fiberAt (HomotopyEquivalence.ofIso (Iso.refl A) FA hFA) b)
    (HomotopyEquivalence.fiberAt E (Term.map f b))
end BasedPathMap

/-- A genuine native equivalence induces equivalences on native path families. -/
noncomputable def pathMapEquivalence {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (E : HomotopyEquivalence f)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful)
    (a b : Term A) : HomotopyEquivalence (pathMap f a b) := by
  let σ := pair (𝟙 Γ) a
  let JA := homogeneousReindexIso (reindex A (projection A)) (generic A)
    (Term.reindex b (projection A)) σ
  let JB := homogeneousReindexIso (reindex B (projection A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.reindex (Term.map f b) (projection A)) σ
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
  let x := Term.reindex (generic A) (projection (reindex A (projection A)))
  let y := generic (reindex A (projection A))
  let f' := Functor.whiskerLeft σ.mapElements f
  let E' := E.reindex σ
  let cB := contractible (reindexProp pB σ) (Term.map f' x)
  let cA := cB.retract (FA.reindex σ) (hFA.reindex σ)
    E'.selectedInverse f'
      (E'.chosenLeftInverse (FA.reindex σ) (hFA.reindex σ) E'.selectedInverse
        (Homotopy.fiberPath (Functor.whiskerLeft (projection (reindex B σ)).mapElements f')
          (generic (reindex B σ)) E'.fibers.center))
  exact pathOfContractible cA (FA.reindex σ) (hFA.reindex σ) x y

/-- Sethood reflects through a genuine homotopy equivalence, without a strict family iso. -/
noncomputable def sourceIsSet {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (E : HomotopyEquivalence f) (sB : Term (isSet B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    Term (isSet A) := by
  apply lam
  apply lam
  let σ := projection (reindex A (projection A)) ≫ projection A
  let x := Term.reindex (generic A) (projection (reindex A (projection A)))
  let y := generic (reindex A (projection A))
  let f' := Functor.whiskerLeft σ.mapElements f
  exact sourceIsProp (pathMap f' x y)
    (pathMapEquivalence f' (E.reindex σ) (FA.reindex σ) (hFA.reindex σ)
      (FB.reindex σ) (hFB.reindex σ) x y)
    (pathIsPropAt (reindexSet sB σ) (Term.map f' x) (Term.map f' y))
    (pathFilling (FA.reindex (projection (interval _) ≫ σ)) (hFA.reindex _) x y)
    (pathFilling_lawful (FA.reindex (projection (interval _) ≫ σ)) (hFA.reindex _) x y)

/-- Carry proposition data through the supplied complete equivalence. -/
noncomputable def targetIsProp {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (E : HomotopyEquivalence f) (pA : Term (isProp A))
    (FB : Filling B) (hFB : FB.Lawful) : Term (isProp B) := by
  apply lam
  apply lam
  let σ := projection (reindex B (projection B)) ≫ projection B
  let x := Term.reindex (generic B) (projection (reindex B (projection B)))
  let y := generic (reindex B (projection B))
  let E' := E.reindex σ
  let cA := contractible (reindexProp pA σ) (Term.map E'.selectedInverse x)
  let cB := targetContractible E' cA (FB.reindex σ) (hFB.reindex σ)
  exact pathOfContractible cB (FB.reindex σ) (hFB.reindex σ) x y

/-- Transport proposition data for paths along two supplied endpoint paths. -/
noncomputable def changeEndpointsProp {Γ : Context.{u}} {B : Family Γ}
    (FB : Filling B) (hFB : FB.Lawful) {a a' b b' : Term B}
    (p : Term (homogeneousPath B a a')) (q : Term (homogeneousPath B b b'))
    (h : Term (isProp (homogeneousPath B a b))) :
    Term (isProp (homogeneousPath B a' b')) := by
  let L := homogeneousPath (reindex B (projection (interval Γ))) (pathApp p) (pathApp q)
  let F := pathFilling (FB.reindex (projection (interval _) ≫ projection (interval Γ)))
    (hFB.reindex _) (pathApp p) (pathApp q)
  have hF := pathFilling_lawful (FB.reindex (projection (interval _) ≫ projection (interval Γ)))
    (hFB.reindex _) (pathApp p) (pathApp q)
  let J₀ : reindex L (endpointSub Γ false) ≅ homogeneousPath B a b :=
    homogeneousReindexIso _ (pathApp p) (pathApp q) (endpointSub Γ false) ≪≫
      eqToIso (congrArg₂ (homogeneousPath B) (pathApp_zero p) (pathApp_zero q))
  let J₁ : reindex L (endpointSub Γ true) ≅ homogeneousPath B a' b' :=
    homogeneousReindexIso _ (pathApp p) (pathApp q) (endpointSub Γ true) ≪≫
      eqToIso (congrArg₂ (homogeneousPath B) (pathApp_one p) (pathApp_one q))
  let start := Term.map (isPropReindexIso L (endpointSub Γ false)).inv (mapProp J₀.symm h)
  let finish := Term.map (IntervalTransport.map (isPropFilling F hF)
    (endpoint Γ false) (endpoint Γ true)) start
  exact mapProp J₁ (Term.map (isPropReindexIso L (endpointSub Γ true)).hom finish)

/-- Sethood transports forward using both selected endpoint recovery paths. -/
noncomputable def targetIsSet {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (E : HomotopyEquivalence f) (sA : Term (isSet A))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    Term (isSet B) := by
  apply lam
  apply lam
  let σ := projection (reindex B (projection B)) ≫ projection B
  let b := Term.reindex (generic B) (projection (reindex B (projection B)))
  let c := generic (reindex B (projection B))
  let f' := Functor.whiskerLeft σ.mapElements f
  let E' := E.reindex σ
  let x := Term.map E'.selectedInverse b
  let y := Term.map E'.selectedInverse c
  let p := Homotopy.fiberPath f' b (E'.fiberAt b).center
  let q := Homotopy.fiberPath f' c (E'.fiberAt c).center
  let K := pathFilling (FB.reindex (projection (interval _) ≫ σ)) (hFB.reindex _)
    (Term.map f' x) (Term.map f' y)
  have hK := pathFilling_lawful (FB.reindex (projection (interval _) ≫ σ)) (hFB.reindex _)
    (Term.map f' x) (Term.map f' y)
  exact changeEndpointsProp (FB.reindex σ) (hFB.reindex σ) p q
    (targetIsProp (pathMap f' x y)
      (pathMapEquivalence f' E' (FA.reindex σ) (hFA.reindex σ)
        (FB.reindex σ) (hFB.reindex σ) x y)
      (pathIsPropAt (reindexSet sA σ) x y) K hK)

/-- A dependent proposition extension of a native set is a native set. -/
noncomputable def sigmaIsSet {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (sA : Term (isSet A)) (pB : Term (isProp B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    Term (isSet (sigma A B)) := by
  apply lam
  apply lam
  let M := sigma A B
  let σ := projection (reindex M (projection M)) ≫ projection M
  let x := Term.reindex (generic M) (projection (reindex M (projection M)))
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
    (piFilling FA hFA (FB.reindex (projection A))) (piFilling_lawful FA hFA (FB.reindex (projection A)) (hFB.reindex _))
    (isEquivFilling (universalMap A B)
      (FA.reindex (projection (maps A B))) (hFA.reindex _)
      (FB.reindex (projection (maps A B))) (hFB.reindex _))
    (isEquivFilling_lawful (universalMap A B)
      (FA.reindex (projection (maps A B))) (hFA.reindex _)
      (FB.reindex (projection (maps A B))) (hFB.reindex _))

end SquareKit.Cubical.Cartesian.HomotopyLevels
