import SquareKit.Internal.Cubical.HomotopyEquivalences
import SquareKit.Internal.Cubical.SumFilling
import SquareKit.Internal.Cubical.PathFillingSubstitution
import SquareKit.Internal.Cubical.FillingTransportLaws

/-! Extension from contraction and constructed filling. The extension operation
is derived from these inputs rather than added to equivalence data. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace HomotopyContractible
variable {Γ : Context.{u}} {A : Family Γ} (c : HomotopyContractible A)

def extensionTube {φ : Cofibration Γ} (a : PartialSection A φ) :
    PartialSection (Presheaf.reindex A (projection (interval Γ)))
      (φ.reindex (projection (interval Γ))) where
  val x h :=
    let y := (projection (interval Γ)).mapElements.obj x
    (pathApp c.contraction).val
      (extendObj (interval (total A)) (extendObj A y (a.val y h)) x.val.2)
  property {x y} f h := by
    let q := (projection (interval Γ)).mapElements.map f
    let g := extendAlong A q (a.property q h)
    let k := extendAlong (interval (total A)) g
      (show (interval (total A)).map g x.val.2 = y.val.2 from
        (generic (interval Γ)).property f)
    exact (pathApp c.contraction).property k

theorem extensionTube_zero {φ : Cofibration Γ} (a : PartialSection A φ)
    (x : Γ.Elements) (h : φ.full x) :
    (c.extensionTube a).val ((endpointSub Γ false).mapElements.obj x) h = c.center.val x := by
  exact congrArg (fun t => t.val (extendObj A x (a.val x h)))
    (pathApp_zero c.contraction)

theorem extensionTube_one {φ : Cofibration Γ} (a : PartialSection A φ)
    (x : Γ.Elements) (h : φ.full x) :
    (c.extensionTube a).val ((endpointSub Γ true).mapElements.obj x) h = a.val x h := by
  exact congrArg (fun t => t.val (extendObj A x (a.val x h)))
    (pathApp_one c.contraction)

def extensionBox {φ : Cofibration Γ} (a : PartialSection A φ) :
    OpenBox (Presheaf.reindex A (projection (interval Γ))) φ where
  tube := c.extensionTube a
  base := c.center
  boundary := c.extensionTube_zero a

def extend (F : Filling A) {φ : Cofibration Γ} (a : PartialSection A φ) : Term A :=
  F.comp (projection (interval Γ)) φ (c.extensionBox a)

theorem extend_boundary (F : Filling A) (hF : F.Lawful)
    {φ : Cofibration Γ} (a : PartialSection A φ) (x : Γ.Elements) (h : φ.full x) :
    (c.extend F a).val x = a.val x h :=
  (Filling.comp_boundary hF (projection (interval Γ)) φ (c.extensionBox a) x h).trans
    (c.extensionTube_one a x h)

theorem extensionTube_reindex {Δ : Context.{u}} {φ : Cofibration Γ}
    (a : PartialSection A φ) (σ : Δ ⟶ Γ) :
    (c.reindex σ).extensionTube (a.reindex σ) =
      (c.extensionTube a).reindex (liftSub (interval Γ) σ) := rfl

theorem extensionBox_reindex {Δ : Context.{u}} {φ : Cofibration Γ}
    (a : PartialSection A φ) (σ : Δ ⟶ Γ) :
    (c.reindex σ).extensionBox (a.reindex σ) = (c.extensionBox a).reindex σ := rfl

theorem extend_reindex (F : Filling A) (hF : F.Lawful)
    {Δ : Context.{u}} {φ : Cofibration Γ} (a : PartialSection A φ) (σ : Δ ⟶ Γ) :
    (c.reindex σ).extend (F.reindex σ) (a.reindex σ) = (c.extend F a).reindex σ :=
  Filling.comp_reindex hF (projection (interval Γ)) φ (c.extensionBox a) σ

theorem extensionTube_transport {B : Family Γ} (e : A ≅ B) {φ : Cofibration Γ}
    (a : PartialSection A φ) :
    (c.transport e).extensionTube (a.map e.hom) =
      (c.extensionTube a).map (Functor.whiskerLeft (projection (interval Γ)).mapElements e.hom) := by
  apply PartialSection.ext
  intro x hx
  let y := (projection (interval Γ)).mapElements.obj x
  have h : e.inv.app y (e.hom.app y (a.val y hx)) = a.val y hx :=
    congrArg (fun η => η.app y (a.val y hx)) e.hom_inv_id
  exact congrArg (fun z => e.hom.app y ((pathApp c.contraction).val
    (extendObj (interval (total A)) (extendObj A y z) x.val.2))) h

theorem extensionBox_transport {B : Family Γ} (e : A ≅ B) {φ : Cofibration Γ}
    (a : PartialSection A φ) :
    (c.transport e).extensionBox (a.map e.hom) =
      (c.extensionBox a).map (Functor.whiskerLeft (projection (interval Γ)).mapElements e.hom) := by
  apply OpenBox.ext
  · exact c.extensionTube_transport e a
  · rfl

theorem extend_transport {B : Family Γ} (e : A ≅ B) (F : Filling A)
    {φ : Cofibration Γ} (a : PartialSection A φ) :
    (c.transport e).extend (F.transport e) (a.map e.hom) = Term.map e.hom (c.extend F a) := by
  let i := Functor.isoWhiskerLeft (projection (interval Γ)).mapElements e
  have hb : ((c.transport e).extensionBox (a.map e.hom)).map i.inv = c.extensionBox a :=
    (congrArg (fun b => b.map i.inv) (c.extensionBox_transport e a)).trans
      (OpenBox.map_iso_roundtrip i.symm (c.extensionBox a))
  exact congrArg (fun b => Term.map e.hom (F.comp (projection (interval Γ)) φ b)) hb

theorem transport_reindex {B : Family Γ} (e : A ≅ B) {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    (c.transport e).reindex σ = (c.reindex σ).transport (Functor.isoWhiskerLeft σ.mapElements e) := rfl

end HomotopyContractible
private theorem familyMap_value_heq {Γ : Context.{u}} {A B : Family Γ} (e : A ⟶ B)
    {x y : Γ.Elements} (h : x = y) {a : A.obj x} {b : A.obj y} (hab : HEq a b) :
    HEq (e.app x a) (e.app y b) := by
  cases h
  cases hab
  rfl

theorem sigmaSecondMap_box_snd {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {B C : Family (total A)} (e : B ⟶ C) {φ : Cofibration Γ}
    (b : OpenBox (sigma A B) φ) (a : Term A) (ha : b.sigmaFst.Fills a) :
    OpenBox.sigmaSnd (B := C) (b.map (sigmaSecondMap A e)) a ha =
      (b.sigmaSnd a ha).map (Functor.whiskerLeft (pair (𝟙 _) a).mapElements e) := by
  apply OpenBox.ext
  · apply PartialSection.ext
    intro x hx
    have hl := PartialSection.sigmaSnd_val (B := C)
      (b.tube.map (sigmaSecondMap A e)) a ha.2 x hx
    have hr := familyMap_value_heq e (congrArg (extendObj A x) (ha.2 x hx))
      (PartialSection.sigmaSnd_val b.tube a ha.2 x hx)
    exact eq_of_heq (hl.trans hr.symm)
  · apply Term.ext
    intro x
    let σ := endpointSub Γ false
    have hl := Term.sigmaSndOver_val (B := Presheaf.reindex C (liftSub A σ))
      (Term.map (Functor.whiskerLeft σ.mapElements (sigmaSecondMap A e)) b.base)
      (a.reindex σ) ha.1 x
    have hr := familyMap_value_heq e
      (congrArg (extendObj A (σ.mapElements.obj x)) (congrArg (fun t => t.val x) ha.1))
      (Term.sigmaSndOver_val (B := Presheaf.reindex B (liftSub A σ))
        b.base (a.reindex σ) ha.1 x)
    exact eq_of_heq (hl.trans hr.symm)

theorem sigmaFilling_transport_second {Γ : Context.{u}} {A : Family Γ}
    {B C : Family (total A)} (e : B ≅ C) (F : Filling A) (hF : F.Lawful) (G : Filling B) :
    (sigmaFilling F hF G).transport (sigmaSecondIso A e) = sigmaFilling F hF (G.transport e) := by
  apply Filling.ext
  intro Δ p φ b
  let first := OpenBox.sigmaFst (B := Presheaf.reindex C (liftSub A p)) b
  let a := F.fill p φ first
  have ha : first.Fills a := hF.fills p φ first
  let i := Functor.isoWhiskerLeft (liftSub A p).mapElements e
  have hs := sigmaSecondMap_box_snd i.inv b a ha
  exact congrArg (fun c => sigmaIntro (B := Presheaf.reindex C (liftSub A p)) a
    (Term.map (Functor.whiskerLeft (pair p a).mapElements e.hom) (G.fill (pair p a) φ c))) hs

/-- Homotopy-fiber filling is assembled from native sum and path providers. -/
noncomputable def homotopyFiberFilling {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (b : Term B) (F : Filling A) (hF : F.Lawful)
    (G : Filling B) (hG : G.Lawful) : Filling (homotopyFiber f b) :=
  sigmaFilling F hF
    (pathFilling (G.reindex (projection (interval (total A)) ≫ projection A))
      (hG.reindex _) (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
      (b.reindex (projection A)))

theorem homotopyFiberFilling_lawful {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (b : Term B) (F : Filling A) (hF : F.Lawful)
    (G : Filling B) (hG : G.Lawful) : (homotopyFiberFilling f b F hF G hG).Lawful :=
  sigmaFilling_lawful F hF _ (pathFilling_lawful _ (hG.reindex _) _ _)

noncomputable def genericFiberFilling {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) :
    Filling (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)) :=
  homotopyFiberFilling _ (generic B) (F.reindex (projection B)) (hF.reindex _)
    (G.reindex (projection B)) (hG.reindex _)

theorem genericFiberFilling_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) (σ : Δ ⟶ Γ) :
    ((genericFiberFilling f F hF G hG).reindex (liftSub B σ)).transport (genericFiberReindexIso f σ) =
    genericFiberFilling (Functor.whiskerLeft σ.mapElements f)
      (F.reindex σ) (hF.reindex _) (G.reindex σ) (hG.reindex _) := by
  let τ := liftSub B σ
  let A₀ := Presheaf.reindex A (projection B)
  let ρ := liftSub A₀ τ
  let a₀ := Term.map (Functor.whiskerLeft (projection A₀).mapElements
    (Functor.whiskerLeft (projection B).mapElements f)) (generic A₀)
  let a₁ := (generic B).reindex (projection A₀)
  let R := G.reindex (projection (interval (total A₀)) ≫ projection A₀ ≫ projection B)
  have hR : R.Lawful := hG.reindex _
  have hfirst := sigmaFilling_transport_second
    (pathReindexIso (Presheaf.reindex B
      (projection (interval (total A₀)) ≫ projection A₀ ≫ projection B)) a₀ a₁ ρ) (F.reindex (τ ≫ projection B)) (hF.reindex _)
    ((pathFilling R hR a₀ a₁).reindex ρ)
  exact hfirst.trans (congrArg (sigmaFilling (F.reindex (τ ≫ projection B)) (hF.reindex _))
    (pathFilling_reindex_iso R hR a₀ a₁ ρ))

theorem genericFiberFilling_lawful {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) :
    (genericFiberFilling f F hF G hG).Lawful :=
  homotopyFiberFilling_lawful _ _ _ (hF.reindex _) _ (hG.reindex _)

/-- Extension for a genuine equivalence at the generic target, with no assumed
homotopy-fiber filling or extension field. -/
noncomputable def HomotopyEquivalence.extend {Γ : Context.{u}} {A B : Family Γ}
    {f : A ⟶ B} (e : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    {φ : Cofibration (total B)}
    (a : PartialSection
      (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)) φ) :=
  e.fibers.extend
    (homotopyFiberFilling _ (generic B) (F.reindex (projection B)) (hF.reindex _)
      (G.reindex (projection B)) (hG.reindex _)) a

theorem HomotopyEquivalence.extend_boundary {Γ : Context.{u}} {A B : Family Γ}
    {f : A ⟶ B} (e : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    {φ : Cofibration (total B)}
    (a : PartialSection
      (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)) φ)
    (x : (total B).Elements) (h : φ.full x) :
    (e.extend F hF G hG a).val x = a.val x h :=
  e.fibers.extend_boundary _ (homotopyFiberFilling_lawful _ _ _ (hF.reindex _) _ (hG.reindex _)) a x h

theorem HomotopyEquivalence.extend_input_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    {f : A ⟶ B} (E : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) (σ : Δ ⟶ Γ)
    {φ : Cofibration (total B)}
    (a : PartialSection (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f)
      (generic B)) φ) :
    (E.reindex σ).extend (F.reindex σ) (hF.reindex _) (G.reindex σ) (hG.reindex _)
      ((a.reindex (liftSub B σ)).map (genericFiberReindexIso f σ).hom) =
    Term.map (genericFiberReindexIso f σ).hom ((E.extend F hF G hG a).reindex (liftSub B σ)) := by
  let τ := liftSub B σ
  let i := genericFiberReindexIso f σ
  let H := genericFiberFilling f F hF G hG
  let c := E.fibers.reindex τ
  have hf := genericFiberFilling_reindex f F hF G hG σ
  exact (congrArg (fun K => (c.transport i).extend K ((a.reindex τ).map i.hom)) hf).symm.trans
    ((c.extend_transport i (H.reindex τ) (a.reindex τ)).trans
      (congrArg (Term.map i.hom)
        (E.fibers.extend_reindex H (genericFiberFilling_lawful f F hF G hG) a τ)))

/-- Fiber extension along an arbitrary target section uses reindexing of the
constructed generic-target fiber filler. -/
noncomputable def HomotopyEquivalence.extendAlong {Γ Δ : Context.{u}} {A B : Family Γ}
    {f : A ⟶ B} (e : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (σ : Δ ⟶ total B) {φ : Cofibration Δ}
    (a : PartialSection (Presheaf.reindex
      (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)) σ) φ) :=
  (e.fibers.reindex σ).extend
    ((homotopyFiberFilling _ (generic B) (F.reindex (projection B)) (hF.reindex _)
      (G.reindex (projection B)) (hG.reindex _)).reindex σ) a

theorem HomotopyEquivalence.extendAlong_boundary {Γ Δ : Context.{u}} {A B : Family Γ}
    {f : A ⟶ B} (e : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (σ : Δ ⟶ total B) {φ : Cofibration Δ}
    (a : PartialSection (Presheaf.reindex
      (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)) σ) φ)
    (x : Δ.Elements) (hx : φ.full x) :
    (e.extendAlong F hF G hG σ a).val x = a.val x hx :=
  (e.fibers.reindex σ).extend_boundary _
    ((homotopyFiberFilling_lawful _ _ _ (hF.reindex _) _ (hG.reindex _)).reindex σ) a x hx

theorem HomotopyEquivalence.extendAlong_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    {f : A ⟶ B} (e : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (σ : Δ ⟶ total B) {φ : Cofibration Δ}
    (a : PartialSection (Presheaf.reindex
      (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)) σ) φ)
    (τ : Θ ⟶ Δ) :
    e.extendAlong F hF G hG (τ ≫ σ) (a.reindex τ) =
      (e.extendAlong F hF G hG σ a).reindex τ :=
  (e.fibers.reindex σ).extend_reindex _
    ((homotopyFiberFilling_lawful _ _ _ (hF.reindex _) _ (hG.reindex _)).reindex σ) a τ

theorem HomotopyEquivalence.extendAlong_input_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    {f : A ⟶ B} (E : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) (σ : Δ ⟶ Γ)
    (ρ : Θ ⟶ total (Presheaf.reindex B σ)) {φ : Cofibration Θ}
    (a : PartialSection (Presheaf.reindex
      (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B))
      (ρ ≫ liftSub B σ)) φ) :
    (E.reindex σ).extendAlong (F.reindex σ) (hF.reindex _) (G.reindex σ) (hG.reindex _) ρ
      (a.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom)) =
    Term.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom)
      (E.extendAlong F hF G hG (ρ ≫ liftSub B σ) a) := by
  let τ := liftSub B σ
  let i := Functor.isoWhiskerLeft ρ.mapElements (genericFiberReindexIso f σ)
  let H := (genericFiberFilling f F hF G hG).reindex (ρ ≫ τ)
  let c := E.fibers.reindex (ρ ≫ τ)
  have hf := congrArg (fun K => K.reindex ρ) (genericFiberFilling_reindex f F hF G hG σ)
  exact (congrArg (fun K => (c.transport i).extend K (a.map i.hom)) hf).symm.trans
    (c.extend_transport i H a)

/-- A partial domain section lying exactly over the target gives reflexive fiber data. -/
def genericFiberPartialIntro {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B) {φ : Cofibration Δ}
    (a : PartialSection (Presheaf.reindex A (σ ≫ projection B)) φ)
    (h : a.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) =
      PartialSection.ofTerm φ ((generic B).reindex σ)) :
    PartialSection (Presheaf.reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f)
      (generic B)) σ) φ :=
  PartialSection.ofRestricted (genericFiberIntro f (restrictInclusion φ ≫ σ) a.toRestricted
    (pathLam
      ((Term.map (Functor.whiskerLeft (restrictInclusion φ ≫ σ ≫ projection B).mapElements f)
        a.toRestricted).reindex (projection (interval (restrictContext φ)))) rfl
      (congrArg PartialSection.toRestricted h)))

/-- The domain component retains the prescribed partial section literally. -/
theorem genericFiberPartialIntro_fst {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B) {φ : Cofibration Δ}
    (a : PartialSection (Presheaf.reindex A (σ ≫ projection B)) φ)
    (h : a.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) =
      PartialSection.ofTerm φ ((generic B).reindex σ)) (x : Δ.Elements) (hx : φ.full x) :
    ((genericFiberPartialIntro f σ a h).val x hx).1 = a.val x hx := rfl

/-- Reflexive partial fiber data is constant along every generalized path coordinate. -/
theorem genericFiberPartialIntro_path {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B) {φ : Cofibration Δ}
    (a : PartialSection (Presheaf.reindex A (σ ≫ projection B)) φ)
    (h : a.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) =
      PartialSection.ofTerm φ ((generic B).reindex σ)) (x : Δ.Elements) (hx : φ.full x)
    {y : (total (Presheaf.reindex A (projection B))).Elements}
    (g : extendObj (Presheaf.reindex A (projection B)) (σ.mapElements.obj x) (a.val x hx) ⟶ y)
    (r : (interval (total (Presheaf.reindex A (projection B)))).obj y) :
    ((genericFiberPartialIntro f σ a h).val x hx).2.val.val g r = y.val.1.2 := by
  let τ := pair (A := Presheaf.reindex A (projection B)) (restrictInclusion φ ≫ σ) a.toRestricted
  let z := (restrictContext φ).elementsMk x.obj ⟨x.val,hx⟩
  obtain ⟨⟨y',g'⟩,hg⟩ := (substitutionArrowEquiv τ z).surjective ⟨y,g⟩
  change (⟨τ.mapElements.obj y',τ.mapElements.map g'⟩ : Σ y, τ.mapElements.obj z ⟶ y) = ⟨y,g⟩ at hg
  cases hg
  change piInverseValue τ _ (τ.mapElements.map g') r = _
  exact (piInverseValue_map τ _ g' r).trans
    (congrArg (fun s => s.val ((restrictInclusion φ).mapElements.obj y') y'.val.property) h)

theorem genericFiberPartialIntro_input_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) (ρ : Θ ⟶ total (Presheaf.reindex B σ)) {φ : Cofibration Θ}
    (a : PartialSection (Presheaf.reindex A (ρ ≫ liftSub B σ ≫ projection B)) φ)
    (h : a.map (Functor.whiskerLeft (ρ ≫ liftSub B σ ≫ projection B).mapElements f) =
      PartialSection.ofTerm φ ((generic B).reindex (ρ ≫ liftSub B σ))) :
    genericFiberPartialIntro (Functor.whiskerLeft σ.mapElements f) ρ a h =
      (genericFiberPartialIntro f (ρ ≫ liftSub B σ) a h).map
        (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom) := by
  apply PartialSection.ext
  intro x hx
  apply congrArg (Sigma.mk (a.val x hx))
  apply Subtype.ext
  apply PiElement.ext
  intro y g r
  exact (genericFiberPartialIntro_path (Functor.whiskerLeft σ.mapElements f) ρ a h x hx g r).trans
    (genericFiberPartialIntro_path f (ρ ≫ liftSub B σ) a h x hx
      ((liftSub (Presheaf.reindex A (projection B)) (liftSub B σ)).mapElements.map g) r).symm

theorem genericFiberPath_input_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) (ρ : Θ ⟶ total (Presheaf.reindex B σ))
    (z : Term (Presheaf.reindex
      (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B))
      (ρ ≫ liftSub B σ))) :
    genericFiberPath (Functor.whiskerLeft σ.mapElements f) ρ
      (Term.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom) z) =
    genericFiberPath f (ρ ≫ liftSub B σ) z := rfl

/-- The reversed extension path is constant on the supplied reflexive boundary. -/
theorem HomotopyEquivalence.extendAlong_path_boundary {Γ Δ : Context.{u}} {A B : Family Γ}
    {f : A ⟶ B} (E : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (σ : Δ ⟶ total B) {φ : Cofibration Δ}
    (a : PartialSection (Presheaf.reindex A (σ ≫ projection B)) φ)
    (h : a.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) =
      PartialSection.ofTerm φ ((generic B).reindex σ)) (x : Δ.Elements) (hx : φ.full x)
    (r : (interval Δ).obj x) :
    (pathApp (homogeneousReverse (genericFiberPath f σ
      (E.extendAlong F hF G hG σ (genericFiberPartialIntro f σ a h))))).val
        (extendObj (interval Δ) x r) = ((generic B).reindex σ).val x := by
  let r' := ULift.up (Cube.comp r.down Cube.reversal)
  have hb := E.extendAlong_boundary F hF G hG σ (genericFiberPartialIntro f σ a h) x hx
  change ((E.extendAlong F hF G hG σ (genericFiberPartialIntro f σ a h)).val x).2.val.val
    (𝟙 _) r' = _
  exact (congrArg (fun z => (show B.obj ((σ ≫ projection B).mapElements.obj x) from
    z.2.val.val (𝟙 _) r')) hb).trans
    (genericFiberPartialIntro_path f σ a h x hx (𝟙 _) r')

theorem genericFiberPartialIntro_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B) {φ : Cofibration Δ}
    (a : PartialSection (Presheaf.reindex A (σ ≫ projection B)) φ)
    (h : a.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) =
      PartialSection.ofTerm φ ((generic B).reindex σ)) (τ : Θ ⟶ Δ) :
    genericFiberPartialIntro f (τ ≫ σ) (a.reindex τ) (congrArg (fun s => s.reindex τ) h) =
      (genericFiberPartialIntro f σ a h).reindex τ := by
  apply PartialSection.ext
  intro x hx
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Subtype.ext
  apply PiElement.ext
  intro y g r
  exact (genericFiberPartialIntro_path f (τ ≫ σ) (a.reindex τ)
    (congrArg (fun s => s.reindex τ) h) x hx g r).trans
      (genericFiberPartialIntro_path f σ a h (τ.mapElements.obj x) hx g r).symm

theorem genericFiberReverse_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (σ : Δ ⟶ total B)
    (z : Term (Presheaf.reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f)
      (generic B)) σ)) (τ : Θ ⟶ Δ) :
    pathApp (homogeneousReverse (genericFiberPath f (τ ≫ σ) (z.reindex τ))) =
      (pathApp (homogeneousReverse (genericFiberPath f σ z))).reindex (liftSub (interval Δ) τ) := rfl


/-- Extension of every partial section supplies a native center and contraction. -/
noncomputable def HomotopyContractible.ofExtensions {Γ : Context.{u}} {A : Family Γ}
    (extend : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Cofibration Δ),
      PartialSection (Presheaf.reindex A σ) φ → Term (Presheaf.reindex A σ))
    (boundary : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Cofibration Δ)
      (a : PartialSection (Presheaf.reindex A σ) φ) (x : Δ.Elements) (hx : φ.full x),
      (extend σ φ a).val x = a.val x hx) : HomotopyContractible A := by
  let empty : PartialSection (Presheaf.reindex A (𝟙 Γ)) (Cofibration.bot Γ) :=
    ⟨fun _ h => (Bool.false_ne_true h).elim, fun _ h => (Bool.false_ne_true h).elim⟩
  let c : Term A := extend (𝟙 Γ) (Cofibration.bot Γ) empty
  let π := projection A
  let p := projection (interval (total A)) ≫ π
  let φ := (intervalFace (total A) false).join (intervalFace (total A) true)
  let b := endpointBoundary (Presheaf.reindex A p) (c.reindex π) (generic A)
  let s := extend p φ b
  have h₀ : s.reindex (endpointSub (total A) false) = c.reindex π := by
    apply Term.ext
    intro x
    let y := (endpointSub (total A) false).mapElements.obj x
    have hy : (intervalFace (total A) false).full y :=
      (Cofibration.full_endpoint (generic (interval (total A))) false y).mpr rfl
    have hu : φ.full y := (Cofibration.full_join _ _ y).mpr (Or.inl hy)
    exact (boundary p φ b y hu).trans (eq_of_heq
      ((heq_of_eq (endpointBoundary_zero _ _ _ y hu hy)).trans
        (endpointSection_val (Presheaf.reindex A p) false (c.reindex π) y hy)))
  have h₁ : s.reindex (endpointSub (total A) true) = generic A := by
    apply Term.ext
    intro x
    let y := (endpointSub (total A) true).mapElements.obj x
    have hy : (intervalFace (total A) true).full y :=
      (Cofibration.full_endpoint (generic (interval (total A))) true y).mpr rfl
    have hu : φ.full y := (Cofibration.full_join _ _ y).mpr (Or.inr hy)
    exact (boundary p φ b y hu).trans (eq_of_heq
      ((heq_of_eq (endpointBoundary_one _ _ _ y hu hy)).trans
        (endpointSection_val (Presheaf.reindex A p) true (generic A) y hy)))
  exact ⟨c,pathLam s h₀ h₁⟩


@[ext] theorem HomotopyContractible.ext {Γ : Context.{u}} {A : Family Γ}
    {c d : HomotopyContractible A} (hc : c.center = d.center) (hp : HEq c.contraction d.contraction) : c = d := by
  cases c
  cases d
  cases hc
  cases hp
  rfl

/-- A contextual extension operation gives a substitution-coherent chosen contraction. -/
theorem HomotopyContractible.ofExtensions_reindex {Γ Ξ : Context.{u}} {A : Family Γ}
    (extend : ∀ {Δ : Context.{u}} (ρ : Δ ⟶ Γ) (φ : Cofibration Δ),
      PartialSection (Presheaf.reindex A ρ) φ → Term (Presheaf.reindex A ρ))
    (boundary : ∀ {Δ : Context.{u}} (ρ : Δ ⟶ Γ) (φ : Cofibration Δ)
      (a : PartialSection (Presheaf.reindex A ρ) φ) (x : Δ.Elements) (hx : φ.full x),
      (extend ρ φ a).val x = a.val x hx)
    (uniform : ∀ {Δ Θ : Context.{u}} (ρ : Δ ⟶ Γ) (φ : Cofibration Δ)
      (a : PartialSection (Presheaf.reindex A ρ) φ) (τ : Θ ⟶ Δ),
      extend (τ ≫ ρ) (φ.reindex τ) (a.reindex τ) = (extend ρ φ a).reindex τ)
    (σ : Ξ ⟶ Γ) :
    (ofExtensions extend boundary).reindex σ =
      ofExtensions (A := Presheaf.reindex A σ) (fun ρ φ a => extend (ρ ≫ σ) φ a)
        (fun ρ φ a x hx => boundary (ρ ≫ σ) φ a x hx) := by
  let c := ofExtensions extend boundary
  let d := ofExtensions (A := Presheaf.reindex A σ) (fun ρ φ a => extend (ρ ≫ σ) φ a)
    (fun ρ φ a x hx => boundary (ρ ≫ σ) φ a x hx)
  let empty : PartialSection (Presheaf.reindex A (𝟙 Γ)) (Cofibration.bot Γ) :=
    ⟨fun _ h => (Bool.false_ne_true h).elim, fun _ h => (Bool.false_ne_true h).elim⟩
  have hc : c.center.reindex σ = d.center := (uniform (𝟙 Γ) (Cofibration.bot Γ) empty σ).symm
  apply HomotopyContractible.ext hc
  apply pathTerm_hext
  let τ := liftSub A σ
  let p := projection (interval (total A)) ≫ projection A
  let φ := (intervalFace (total A) false).join (intervalFace (total A) true)
  let b := endpointBoundary (Presheaf.reindex A p) (c.center.reindex (projection A)) (generic A)
  have hb := endpointBoundary_reindex (Presheaf.reindex A p) (c.center.reindex (projection A)) (generic A) τ
  have hd := congrArg (fun a : Term (Presheaf.reindex A σ) =>
    endpointBoundary (Presheaf.reindex A (projection (interval (total (Presheaf.reindex A σ))) ≫
      projection (Presheaf.reindex A σ) ≫ σ)) (a.reindex (projection (Presheaf.reindex A σ)))
      (generic (Presheaf.reindex A σ))) hc
  exact (uniform p φ b (liftSub (interval (total A)) τ)).symm.trans
    (congrArg (extend (projection (interval (total (Presheaf.reindex A σ))) ≫
      projection (Presheaf.reindex A σ) ≫ σ)
      ((intervalFace (total (Presheaf.reindex A σ)) false).join
        (intervalFace (total (Presheaf.reindex A σ)) true))) (hb.trans hd))

private theorem homogeneousBoundary_map {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (a₀ a₁ : Term A) :
    (endpointBoundary (Presheaf.reindex A (projection (interval Γ))) a₀ a₁).map
      (Functor.whiskerLeft (projection (interval Γ)).mapElements f) =
    endpointBoundary (Presheaf.reindex B (projection (interval Γ))) (Term.map f a₀) (Term.map f a₁) := by
  apply PartialSection.ext
  intro x hx
  rcases (Cofibration.full_join _ _ x).mp hx with h₀ | h₁
  · have hs := eq_of_heq ((heq_of_eq (endpointBoundary_zero (Presheaf.reindex A (projection (interval Γ))) a₀ a₁ x hx h₀)).trans
      (endpointSection_val (Presheaf.reindex A (projection (interval Γ))) false a₀ x h₀))
    have ht := eq_of_heq ((heq_of_eq (endpointBoundary_zero (Presheaf.reindex B (projection (interval Γ))) (Term.map f a₀) (Term.map f a₁) x hx h₀)).trans
      (endpointSection_val (Presheaf.reindex B (projection (interval Γ))) false (Term.map f a₀) x h₀))
    exact (congrArg (f.app ((projection (interval Γ)).mapElements.obj x)) hs).trans ht.symm
  · have hs := eq_of_heq ((heq_of_eq (endpointBoundary_one (Presheaf.reindex A (projection (interval Γ))) a₀ a₁ x hx h₁)).trans
      (endpointSection_val (Presheaf.reindex A (projection (interval Γ))) true a₁ x h₁))
    have ht := eq_of_heq ((heq_of_eq (endpointBoundary_one (Presheaf.reindex B (projection (interval Γ))) (Term.map f a₀) (Term.map f a₁) x hx h₁)).trans
      (endpointSection_val (Presheaf.reindex B (projection (interval Γ))) true (Term.map f a₁) x h₁))
    exact (congrArg (f.app ((projection (interval Γ)).mapElements.obj x)) hs).trans ht.symm

/-- Extension-preserving isomorphisms preserve the center and entire chosen contraction. -/
theorem HomotopyContractible.ofExtensions_iso {Γ : Context.{u}} {A B : Family Γ}
    (extendA : ∀ {Δ : Context.{u}} (ρ : Δ ⟶ Γ) (φ : Cofibration Δ),
      PartialSection (Presheaf.reindex A ρ) φ → Term (Presheaf.reindex A ρ))
    (boundaryA : ∀ {Δ : Context.{u}} (ρ : Δ ⟶ Γ) (φ : Cofibration Δ)
      (a : PartialSection (Presheaf.reindex A ρ) φ) (x : Δ.Elements) (hx : φ.full x),
      (extendA ρ φ a).val x = a.val x hx)
    (uniformA : ∀ {Δ Θ : Context.{u}} (ρ : Δ ⟶ Γ) (φ : Cofibration Δ)
      (a : PartialSection (Presheaf.reindex A ρ) φ) (τ : Θ ⟶ Δ),
      extendA (τ ≫ ρ) (φ.reindex τ) (a.reindex τ) = (extendA ρ φ a).reindex τ)
    (extendB : ∀ {Δ : Context.{u}} (ρ : Δ ⟶ Γ) (φ : Cofibration Δ),
      PartialSection (Presheaf.reindex B ρ) φ → Term (Presheaf.reindex B ρ))
    (boundaryB : ∀ {Δ : Context.{u}} (ρ : Δ ⟶ Γ) (φ : Cofibration Δ)
      (a : PartialSection (Presheaf.reindex B ρ) φ) (x : Δ.Elements) (hx : φ.full x),
      (extendB ρ φ a).val x = a.val x hx)
    (e : A ≅ B)
    (compat : ∀ {Δ : Context.{u}} (ρ : Δ ⟶ Γ) (φ : Cofibration Δ)
      (a : PartialSection (Presheaf.reindex A ρ) φ),
      Term.map (Functor.whiskerLeft ρ.mapElements e.hom) (extendA ρ φ a) =
        extendB ρ φ (a.map (Functor.whiskerLeft ρ.mapElements e.hom))) :
    (ofExtensions extendA boundaryA).transport e = ofExtensions extendB boundaryB := by
  let c := ofExtensions extendA boundaryA
  let d := ofExtensions extendB boundaryB
  let emptyA : PartialSection A (Cofibration.bot Γ) :=
    ⟨fun _ h => (Bool.false_ne_true h).elim, fun _ h => (Bool.false_ne_true h).elim⟩
  let emptyB : PartialSection B (Cofibration.bot Γ) :=
    ⟨fun _ h => (Bool.false_ne_true h).elim, fun _ h => (Bool.false_ne_true h).elim⟩
  have he : emptyA.map e.hom = emptyB := by
    apply PartialSection.ext
    intro x hx
    exact (Bool.false_ne_true hx).elim
  have hc : Term.map e.hom c.center = d.center :=
    (compat (𝟙 Γ) (Cofibration.bot Γ) emptyA).trans
      (congrArg (extendB (𝟙 Γ) (Cofibration.bot Γ)) he)
  apply HomotopyContractible.ext hc
  apply pathTerm_hext
  let k := pair (projection B) (Term.map (Functor.whiskerLeft (projection B).mapElements e.inv) (generic B))
  let α := liftSub (interval (total A)) k
  let p := projection (interval (total A)) ≫ projection A
  let q := projection (interval (total B)) ≫ projection B
  let φ := (intervalFace (total A) false).join (intervalFace (total A) true)
  let ψ := (intervalFace (total B) false).join (intervalFace (total B) true)
  let b := endpointBoundary (Presheaf.reindex A p) (c.center.reindex (projection A)) (generic A)
  have hb : (b.reindex α).map (Functor.whiskerLeft q.mapElements e.hom) =
      endpointBoundary (Presheaf.reindex B q) (d.center.reindex (projection B)) (generic B) := by
    have hbr := endpointBoundary_reindex (Presheaf.reindex A p) (c.center.reindex (projection A)) (generic A) k
    have hbm := homogeneousBoundary_map (Functor.whiskerLeft (projection B).mapElements e.hom)
      (c.center.reindex (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements e.inv) (generic B))
    exact (congrArg (fun s => s.map (Functor.whiskerLeft q.mapElements e.hom)) hbr).trans
      (hbm.trans (congrArg₂ (endpointBoundary (Presheaf.reindex B q))
        (congrArg (fun t => t.reindex (projection B)) hc)
        (Term.map_iso_roundtrip (Functor.isoWhiskerLeft (projection B).mapElements e).symm (generic B))))
  exact (congrArg (Term.map (Functor.whiskerLeft q.mapElements e.hom)) (uniformA p φ b α).symm).trans
    ((compat q ψ (b.reindex α)).trans (congrArg (extendB q ψ) hb))

end SquareKit.Cubical.Presheaf
