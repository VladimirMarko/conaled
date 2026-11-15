import SquareKit.Internal.Cubical.EquivalenceFamilies
import SquareKit.Internal.Cubical.HomotopyRetracts

/-! Native map homotopies lift to paths retaining chosen equivalence witnesses. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
open EquivalenceFamilies
universe u

namespace EquivalencePaths

namespace PiContractibility
variable {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
  (c : HomotopyContractible B) (F : Filling B) (hF : F.Lawful)
  {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Cofibration Δ)
  (s : PartialSection (reindex (pi A B) σ) φ)

noncomputable def body : Term (reindex B (liftSub A σ)) :=
  (c.reindex (liftSub A σ)).extend (F.reindex (liftSub A σ))
    ((s.map (piReindex A B σ)).app)

noncomputable def extend : Term (reindex (pi A B) σ) :=
  Term.map (piReindexIso A B σ).inv (lam (body c F σ φ s))

include hF in
theorem boundary (x : Δ.Elements) (hx : φ.full x) :
    (extend c F σ φ s).val x = s.val x hx := by
  let i := piReindexIso A B σ
  let p := s.map i.hom
  have h : (lam (body c F σ φ s)).val x = p.val x hx := by
    apply PiElement.ext
    intro y g v
    have hb := (c.reindex (liftSub A σ)).extend_boundary (F.reindex (liftSub A σ))
      (hF.reindex _) p.app (extendObj (reindex A σ) y v) (φ.full_natural g hx)
    have hp := congrArg (fun k => k.val (𝟙 y) v) (p.property g hx)
    refine hb.trans ?_
    change (p.val x hx).val (g ≫ 𝟙 y) v =
      (p.val y (φ.full_natural g hx)).val (𝟙 y) v at hp
    change (p.val y (φ.full_natural g hx)).val (𝟙 y) v = (p.val x hx).val g v
    simpa only [Category.comp_id] using hp.symm
  exact (congrArg (i.inv.app x) h).trans
    (congrArg (fun m => m.app x (s.val x hx)) i.hom_inv_id)

end PiContractibility

private noncomputable def piContractible {Γ : Context.{u}} {A : Family Γ}
    {B : Family (total A)} (c : HomotopyContractible B) (F : Filling B) (hF : F.Lawful) :
    HomotopyContractible (pi A B) :=
  HomotopyContractible.ofExtensions (PiContractibility.extend c F)
    (PiContractibility.boundary c F hF)

/-- An inhabited substituted equivalence-witness family is contractible with
its full native contraction data, even when the original map is not invertible globally. -/
noncomputable def substitutedWitnessContractible {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (σ : Δ ⟶ Γ) (w : Term (reindex (isEquiv f) σ)) :
    HomotopyContractible (reindex (isEquiv f) σ) := by
  let C := homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)
  let τ := liftSub B σ
  let i := genericFiberReindexIso f σ
  let c := ((isEquivReindexSections f σ).symm w).fibers.transport i.symm
  let K := (genericFiberFilling f F hF G hG).reindex τ
  have hK : K.Lawful := (genericFiberFilling_lawful f F hF G hG).reindex τ
  let q := contrReindexIso C τ
  let d := (contrContractible c K hK).transport q.symm
  let L := (contrFilling (genericFiberFilling f F hF G hG)
    (genericFiberFilling_lawful f F hF G hG)).reindex τ
  have hL : L.Lawful := (contrFilling_lawful _ (genericFiberFilling_lawful f F hF G hG)).reindex τ
  exact (piContractible d L hL).transport (piReindexIso B (contr C) σ).symm

variable {Γ : Context.{u}} {A B : Family Γ} (f g : A ⟶ B)
  (H : Term (homogeneousPath (reindex B (projection A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements g) (generic A))))

/-- Abstract the supplied pointwise native homotopy over all generalized arguments. -/
def mapLine : Term (reindex (maps A B) (projection (interval Γ))) where
  val x := {
    val := fun {y} k a => (pathApp H).val
      (extendObj (interval (total A)) (extendObj A y a) ((interval Γ).map k x.val.2))
    naturality := by
      intro y z k l a
      let q := extendHom A l a
      have hr : (interval (total A)).map q ((interval Γ).map k x.val.2) =
          (interval Γ).map (k ≫ l) x.val.2 :=
        (congrArg (fun m => m x.val.2) ((interval Γ).map_comp k l)).symm
      exact (pathApp H).property (extendAlong (interval (total A)) q hr) }
  property {x y} h := by
    apply PiElement.ext
    intro z k a
    let l := (projection (interval Γ)).mapElements.map h
    have hr : (interval Γ).map (l ≫ k) x.val.2 = (interval Γ).map k y.val.2 :=
      (congrArg (fun m => m x.val.2) ((interval Γ).map_comp l k)).trans
        (congrArg ((interval Γ).map k) ((generic (interval Γ)).property h))
    exact congrArg (fun r : (interval Γ).obj z =>
      (show B.obj z from (pathApp H).val
        (extendObj (interval (total A)) (extendObj A z a) r))) hr

theorem mapLine_zero : (mapLine f g H).reindex (endpointSub Γ false) = encodeMap f := by
  apply Term.ext
  intro x
  apply PiElement.ext
  intro y k a
  have hr := (endpoint Γ false).property k
  exact (congrArg (fun r : (interval Γ).obj y =>
    (show B.obj y from (pathApp H).val
      (extendObj (interval (total A)) (extendObj A y a) r))) hr).trans
    (congrArg (fun t => t.val (extendObj A y a)) (pathApp_zero H))

theorem mapLine_one : (mapLine f g H).reindex (endpointSub Γ true) = encodeMap g := by
  apply Term.ext
  intro x
  apply PiElement.ext
  intro y k a
  have hr := (endpoint Γ true).property k
  exact (congrArg (fun r : (interval Γ).obj y =>
    (show B.obj y from (pathApp H).val
      (extendObj (interval (total A)) (extendObj A y a) r))) hr).trans
    (congrArg (fun t => t.val (extendObj A y a)) (pathApp_one H))

/-- Function extensionality here is a construction from the supplied native homotopy. -/
def mapPath : Term (homogeneousPath (maps A B) (encodeMap f) (encodeMap g)) :=
  pathLam (mapLine f g H) (mapLine_zero f g H) (mapLine_one f g H)


abbrev witnessFamily := isEquiv (universalMap A B)
def witnessSub : total (interval Γ) ⟶ total (maps A B) :=
  pair (projection (interval Γ)) (mapLine f g H)
abbrev witnessLine := reindex (witnessFamily (A := A) (B := B)) (witnessSub f g H)

theorem witnessSub_zero : endpointSub Γ false ≫ witnessSub f g H = pair (A := maps A B) (𝟙 Γ) (encodeMap f) := by
  ext I γ
  exact congrArg (fun a => (⟨γ,a⟩ : (total (maps A B)).obj I))
    (congrArg (fun t => t.val (Γ.elementsMk I γ)) (mapLine_zero f g H))

theorem witnessSub_one : endpointSub Γ true ≫ witnessSub f g H = pair (A := maps A B) (𝟙 Γ) (encodeMap g) := by
  ext I γ
  exact congrArg (fun a => (⟨γ,a⟩ : (total (maps A B)).obj I))
    (congrArg (fun t => t.val (Γ.elementsMk I γ)) (mapLine_one f g H))

def startIso : reindex (witnessLine f g H) (endpointSub Γ false) ≅
    reindex (witnessFamily (A := A) (B := B)) (pair (𝟙 Γ) (encodeMap f)) :=
  eqToIso (congrArg (reindex (witnessFamily (A := A) (B := B))) (witnessSub_zero f g H))

def finishIso : reindex (witnessLine f g H) (endpointSub Γ true) ≅
    reindex (witnessFamily (A := A) (B := B)) (pair (𝟙 Γ) (encodeMap g)) :=
  eqToIso (congrArg (reindex (witnessFamily (A := A) (B := B))) (witnessSub_one f g H))

noncomputable def chosenWitness (e : HomotopyEquivalence f) :
    Term (reindex (witnessFamily (A := A) (B := B)) (pair (𝟙 Γ) (encodeMap f))) :=
  sigmaSnd (B := witnessFamily (A := A) (B := B)) ((equivSections A B) ⟨f,e⟩)

variable (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
  (Ef : HomotopyEquivalence f) (Eg : HomotopyEquivalence g)

noncomputable def universalFilling : Filling (witnessFamily (A := A) (B := B)) :=
  isEquivFilling (universalMap A B) (F.reindex (projection (maps A B))) (hF.reindex _)
    (G.reindex (projection (maps A B))) (hG.reindex _)

theorem universalFilling_lawful : (universalFilling F hF G hG).Lawful :=
  isEquivFilling_lawful _ _ (hF.reindex _) _ (hG.reindex _)

noncomputable def lineFilling : Filling (witnessLine f g H) :=
  (universalFilling F hF G hG).reindex (witnessSub f g H)

theorem lineFilling_lawful : (lineFilling f g H F hF G hG).Lawful :=
  (universalFilling_lawful F hF G hG).reindex _

noncomputable def initialWitness : Term (reindex (witnessLine f g H) (endpointSub Γ false)) :=
  Term.map (startIso f g H).inv (chosenWitness f Ef)

noncomputable def finalWitness : Term (reindex (witnessLine f g H) (endpointSub Γ true)) :=
  Term.map (finishIso f g H).inv (chosenWitness g Eg)

noncomputable def transportedWitness : Term (reindex (witnessLine f g H) (endpointSub Γ true)) :=
  Term.map (IntervalTransport.map (lineFilling f g H F hF G hG)) (initialWitness f g H Ef)

noncomputable def observedWitness :
    Term (reindex (witnessFamily (A := A) (B := B)) (pair (𝟙 Γ) (encodeMap g))) :=
  Term.map (finishIso f g H).hom (transportedWitness f g H F hF G hG Ef)

noncomputable def endpointComparison : Term (homogeneousPath
    (reindex (witnessFamily (A := A) (B := B)) (pair (𝟙 Γ) (encodeMap g)))
    (observedWitness f g H F hF G hG Ef) (chosenWitness g Eg)) := by
  let c := substitutedWitnessContractible (universalMap A B)
    (F.reindex (projection (maps A B))) (hF.reindex _)
    (G.reindex (projection (maps A B))) (hG.reindex _)
    (pair (𝟙 Γ) (encodeMap g)) (observedWitness f g H F hF G hG Ef)
  exact homogeneousConcat ((universalFilling F hF G hG).reindex (pair (𝟙 Γ) (encodeMap g)))
    ((universalFilling_lawful F hF G hG).reindex _)
    (homogeneousReverse (c.pathTo (observedWitness f g H F hF G hG Ef)))
    (c.pathTo (chosenWitness g Eg))

noncomputable def nativeEndpointComparison : Term (homogeneousPath
    (reindex (witnessLine f g H) (endpointSub Γ true))
    (transportedWitness f g H F hF G hG Ef) (finalWitness f g H Eg)) := by
  let p := homogeneousPathMap (finishIso f g H).inv
    (endpointComparison f g H F hF G hG Ef Eg)
  exact pathLam (pathApp p)
    ((pathApp_zero p).trans (Term.map_iso_roundtrip (finishIso f g H)
      (transportedWitness f g H F hF G hG Ef))) (pathApp_one p)

noncomputable def witnessSection : Term (witnessLine f g H) :=
  IntervalTransport.adjustedPath (lineFilling f g H F hF G hG)
    (lineFilling_lawful f g H F hF G hG) (initialWitness f g H Ef) (finalWitness f g H Eg)
    (nativeEndpointComparison f g H F hF G hG Ef Eg)

theorem witnessSection_zero :
    (witnessSection f g H F hF G hG Ef Eg).reindex (endpointSub Γ false) = initialWitness f g H Ef :=
  IntervalTransport.adjustedPath_zero _ (lineFilling_lawful f g H F hF G hG) _ _ _

theorem witnessSection_one :
    (witnessSection f g H F hF G hG Ef Eg).reindex (endpointSub Γ true) = finalWitness f g H Eg :=
  IntervalTransport.adjustedPath_one _ (lineFilling_lawful f g H F hF G hG) _ _ _

noncomputable def equivalenceLine : Term (reindex (equiv A B) (projection (interval Γ))) :=
  sigmaIntro (B := reindex (witnessFamily (A := A) (B := B)) (liftSub (maps A B) (projection (interval Γ))))
    (mapLine f g H) (witnessSection f g H F hF G hG Ef Eg)

private theorem eqToIso_inv_value_heq {Ξ : Context.{u}} {C D : Family Ξ}
    (h : C = D) (t : Term D) (x : Ξ.Elements) :
    HEq ((Term.map (eqToIso h).inv t).val x) (t.val x) := by
  cases h
  rfl

theorem equivalenceLine_zero :
    (equivalenceLine f g H F hF G hG Ef Eg).reindex (endpointSub Γ false) =
      (equivSections A B) ⟨f,Ef⟩ := by
  apply Term.ext
  intro x
  apply Sigma.ext (congrArg (fun t => t.val x) (mapLine_zero f g H))
  exact (heq_of_eq (congrArg (fun t => t.val x)
    (witnessSection_zero f g H F hF G hG Ef Eg))).trans
    (eqToIso_inv_value_heq _ (chosenWitness f Ef) x)

theorem equivalenceLine_one :
    (equivalenceLine f g H F hF G hG Ef Eg).reindex (endpointSub Γ true) =
      (equivSections A B) ⟨g,Eg⟩ := by
  apply Term.ext
  intro x
  apply Sigma.ext (congrArg (fun t => t.val x) (mapLine_one f g H))
  exact (heq_of_eq (congrArg (fun t => t.val x)
    (witnessSection_one f g H F hF G hG Ef Eg))).trans
    (eqToIso_inv_value_heq _ (chosenWitness g Eg) x)

/-- A native map homotopy yields a path between the full supplied equivalences,
including their selected generic-fiber contractions. -/
noncomputable def ofHomotopy : Term (homogeneousPath (equiv A B)
    ((equivSections A B) ⟨f,Ef⟩) ((equivSections A B) ⟨g,Eg⟩)) :=
  pathLam (equivalenceLine f g H F hF G hG Ef Eg)
    (equivalenceLine_zero f g H F hF G hG Ef Eg)
    (equivalenceLine_one f g H F hF G hG Ef Eg)


end EquivalencePaths
end SquareKit.Cubical.Presheaf
