import SquareKit.Internal.Cubical.EquivalenceExtension
import SquareKit.Internal.Cubical.PartialFunctions
import SquareKit.Internal.Cubical.FunctionFilling

/-! Internal families retaining the chosen native contractibility witnesses. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace EquivalenceFamilies

/-- The native paths from a generic proposed center to a second generic element. -/
abbrev contractionPaths {Γ : Context.{u}} (A : Family Γ) :=
  homogeneousPath
    (reindex (reindex A (projection A)) (projection (reindex A (projection A))))
    ((generic A).reindex (projection (reindex A (projection A))))
    (generic (reindex A (projection A)))

/-- A contraction with a specified generic center. -/
def contractions {Γ : Context.{u}} (A : Family Γ) : Family (total A) :=
  pi (reindex A (projection A)) (contractionPaths A)

/-- Internal contractibility includes both the center and all native paths. -/
def contr {Γ : Context.{u}} (A : Family Γ) : Family Γ := sigma A (contractions A)

/-- Reindex homogeneous paths with their specified endpoint sections. -/
def homogeneousReindexIso {Γ Δ : Context.{u}} (A : Family Γ) (a b : Term A)
    (σ : Δ ⟶ Γ) : reindex (homogeneousPath A a b) σ ≅
      homogeneousPath (reindex A σ) (a.reindex σ) (b.reindex σ) :=
  pathReindexIso (reindex A (projection (interval Γ))) a b σ

/-- Substituting a center recovers the path family in external contractibility. -/
def contractionPathsAt {Γ : Context.{u}} (A : Family Γ) (c : Term A) :
    reindex (contractionPaths A)
      (liftSub (reindex A (projection A)) (pair (𝟙 Γ) c)) ≅
    homogeneousPath (reindex A (projection A)) (c.reindex (projection A)) (generic A) := by
  let τ : total A ⟶ total (reindex A (projection A)) :=
    liftSub (reindex A (projection A)) (pair (𝟙 Γ) c)
  let C := reindex
    (reindex (reindex A (projection A)) (projection (reindex A (projection A)))) τ
  let a := ((generic A).reindex (projection (reindex A (projection A)))).reindex τ
  let b := (generic (reindex A (projection A))).reindex τ
  let j : homogeneousPath C a b ≅
      homogeneousPath (reindex A (projection A)) (c.reindex (projection A)) (generic A) := {
    hom := {
      app := fun _ => TypeCat.ofHom (fun p => ⟨{
        val := fun f r => p.val.val f r
        naturality := fun f g r => p.val.naturality f g r }, fun f => p.property f⟩)
      naturality := fun _ _ _ => rfl }
    inv := {
      app := fun _ => TypeCat.ofHom (fun p => ⟨{
        val := fun f r => p.val.val f r
        naturality := fun f g r => p.val.naturality f g r }, fun f => p.property f⟩)
      naturality := fun _ _ _ => rfl }
    hom_inv_id := by
      ext x p
      apply Subtype.ext
      apply PiElement.ext
      intro y f r
      rfl
    inv_hom_id := by
      ext x p
      apply Subtype.ext
      apply PiElement.ext
      intro y f r
      rfl }
  exact (homogeneousReindexIso
    (reindex (reindex A (projection A)) (projection (reindex A (projection A))))
    ((generic A).reindex (projection (reindex A (projection A))))
    (generic (reindex A (projection A))) τ) ≪≫ j

/-- Map a product's values without changing its generalized arguments. -/
def piSecondMap {Γ : Context.{u}} (A : Family Γ) {B C : Family (total A)}
    (e : B ⟶ C) : pi A B ⟶ pi A C where
  app _x := TypeCat.ofHom (fun p => {
    val := fun {_} f a => e.app _ (p.val f a)
    naturality := fun f g a =>
      (e.naturality_apply (extendHom A g a) (p.val f a)).symm.trans
        (congrArg (e.app _) (p.naturality f g a)) })
  naturality _ _ _ := rfl

def piSecondIso {Γ : Context.{u}} (A : Family Γ) {B C : Family (total A)}
    (e : B ≅ C) : pi A B ≅ pi A C where
  hom := piSecondMap A e.hom
  inv := piSecondMap A e.inv
  hom_inv_id := by
    ext x p
    apply PiElement.ext
    intro y f a
    exact congrArg (fun m => m.app (extendObj A y a) (p.val f a)) e.hom_inv_id
  inv_hom_id := by
    ext x p
    apply PiElement.ext
    intro y f a
    exact congrArg (fun m => m.app (extendObj A y a) (p.val f a)) e.inv_hom_id

/-- Contractions at a specified center are native functions into its path family. -/
def contractionsAtIso {Γ : Context.{u}} (A : Family Γ) (c : Term A) :
    reindex (contractions A) (pair (𝟙 Γ) c) ≅
      pi A (homogeneousPath (reindex A (projection A)) (c.reindex (projection A)) (generic A)) :=
  piReindexIso (reindex A (projection A)) (contractionPaths A) (pair (𝟙 Γ) c) ≪≫
    piSecondIso A (contractionPathsAt A c)

/-- Encode all of an external contraction, not merely its center. -/
noncomputable def encodeContr {Γ : Context.{u}} {A : Family Γ}
    (c : HomotopyContractible A) : Term (contr A) :=
  sigmaIntro c.center (Term.map (contractionsAtIso A c.center).inv (lam c.contraction))

/-- Decode an internal section into its chosen center and native contraction. -/
def decodeContr {Γ : Context.{u}} {A : Family Γ}
    (s : Term (contr A)) : HomotopyContractible A where
  center := sigmaFst s
  contraction := app (Term.map (contractionsAtIso A (sigmaFst s)).hom (sigmaSnd s))

@[simp] theorem decode_encodeContr {Γ : Context.{u}} {A : Family Γ}
    (c : HomotopyContractible A) : decodeContr (encodeContr c) = c := by
  let e := contractionsAtIso A c.center
  have h := Term.map_iso_roundtrip e.symm (lam c.contraction)
  have hp : (decodeContr (encodeContr c)).contraction = c.contraction := congrArg app h
  exact congrArg (HomotopyContractible.mk c.center) hp

@[simp] theorem encode_decodeContr {Γ : Context.{u}} {A : Family Γ}
    (s : Term (contr A)) : encodeContr (decodeContr s) = s := by
  let e := contractionsAtIso A (sigmaFst s)
  have hp : Term.map e.inv (lam (app (Term.map e.hom (sigmaSnd s)))) = sigmaSnd s :=
    (congrArg (Term.map e.inv) (lam_app (Term.map e.hom (sigmaSnd s)))).trans
      (Term.map_iso_roundtrip e (sigmaSnd s))
  exact (congrArg (sigmaIntro (sigmaFst s)) hp).trans (sigma_eta s)

/-- Sections represent the complete external contraction data faithfully. -/
noncomputable def contrSections {Γ : Context.{u}} (A : Family Γ) :
    HomotopyContractible A ≃ Term (contr A) where
  toFun := encodeContr
  invFun := decodeContr
  left_inv := decode_encodeContr
  right_inv := encode_decodeContr

/-- The native contraction representation commutes with substitution. -/
def contrReindexIso {Γ Δ : Context.{u}} (A : Family Γ) (σ : Δ ⟶ Γ) :
    reindex (contr A) σ ≅ contr (reindex A σ) :=
  sigmaSecondIso _
    (piReindexIso (reindex A (projection A)) (contractionPaths A) (liftSub A σ) ≪≫
      piSecondIso _ (pathReindexIso
        (reindex (reindex (reindex A (projection A)) (projection (reindex A (projection A))))
          (projection (interval (total (reindex A (projection A))))))
        ((generic A).reindex (projection (reindex A (projection A))))
        (generic (reindex A (projection A)))
        (liftSub (reindex A (projection A)) (liftSub A σ))))

theorem decodeContr_reindex {Γ Δ : Context.{u}} (A : Family Γ)
    (s : Term (contr A)) (σ : Δ ⟶ Γ) :
    decodeContr (Term.map (contrReindexIso A σ).hom (s.reindex σ)) =
      (decodeContr s).reindex σ := by
  have h : (decodeContr (Term.map (contrReindexIso A σ).hom (s.reindex σ))).contraction =
      ((decodeContr s).reindex σ).contraction := by
    apply Term.ext
    intro x
    apply Subtype.ext
    apply PiElement.ext
    intro y f a
    dsimp only [decodeContr, contrReindexIso, contractionsAtIso, contractionPathsAt, homogeneousReindexIso,
      HomotopyContractible.reindex, Term.map, Term.reindex, app, sigmaSnd,
      sigmaSecondIso, sigmaSecondMap, piSecondIso, piSecondMap, piReindexIso,
      piReindex, pathReindexIso, pathReindex, Iso.trans_hom]
    rfl
  exact congrArg (HomotopyContractible.mk ((sigmaFst s).reindex σ)) h

theorem encodeContr_reindex {Γ Δ : Context.{u}} {A : Family Γ}
    (c : HomotopyContractible A) (σ : Δ ⟶ Γ) :
    Term.map (contrReindexIso A σ).hom ((encodeContr c).reindex σ) =
      encodeContr (c.reindex σ) := by
  apply (contrSections (reindex A σ)).symm.injective
  change decodeContr _ = decodeContr _
  rw [decodeContr_reindex, decode_encodeContr, decode_encodeContr]

/-- Internal equivalence witnesses for a fixed family morphism. -/
def isEquiv {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) : Family Γ :=
  pi B (contr (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f)
    (generic B)))

noncomputable def encodeIsEquiv {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (e : HomotopyEquivalence f) : Term (isEquiv f) := lam (encodeContr e.fibers)

def decodeIsEquiv {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (s : Term (isEquiv f)) : HomotopyEquivalence f where
  fibers := decodeContr (app s)

@[simp] theorem decode_encodeIsEquiv {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (e : HomotopyEquivalence f) : decodeIsEquiv (encodeIsEquiv e) = e := by
  cases e
  simp only [decodeIsEquiv, encodeIsEquiv, app_lam, decode_encodeContr]

@[simp] theorem encode_decodeIsEquiv {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (s : Term (isEquiv f)) : encodeIsEquiv (decodeIsEquiv s) = s := by
  simp only [encodeIsEquiv, decodeIsEquiv, encode_decodeContr]
  exact lam_app s

noncomputable def isEquivSections {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) :
    HomotopyEquivalence f ≃ Term (isEquiv f) where
  toFun := encodeIsEquiv
  invFun := decodeIsEquiv
  left_inv := decode_encodeIsEquiv
  right_inv := encode_decodeIsEquiv

/-- The native family of maps, with all generalized arguments retained. -/
def maps {Γ : Context.{u}} (A B : Family Γ) : Family Γ :=
  pi A (reindex B (projection A))

def encodeMap {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) : Term (maps A B) :=
  lam (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))

def decodeMap {Γ : Context.{u}} {A B : Family Γ} (s : Term (maps A B)) : A ⟶ B where
  app x := TypeCat.ofHom (fun a => (app s).val (extendObj A x a))
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro a
    exact ((app s).property (extendHom A f a)).symm

@[simp] theorem decode_encodeMap {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) : decodeMap (encodeMap f) = f := rfl

@[simp] theorem encode_decodeMap {Γ : Context.{u}} {A B : Family Γ}
    (s : Term (maps A B)) : encodeMap (decodeMap s) = s := lam_app s

/-- Evaluate the generic map in its comprehension context. -/
def universalMap {Γ : Context.{u}} (A B : Family Γ) :
    reindex A (projection (maps A B)) ⟶ reindex B (projection (maps A B)) :=
  decodeMap (Term.map (piReindex A (reindex B (projection A))
    (projection (maps A B))) (generic (maps A B)))

/-- A map together with its internal native equivalence witnesses. -/
def equiv {Γ : Context.{u}} (A B : Family Γ) : Family Γ :=
  sigma (maps A B) (isEquiv (universalMap A B))

namespace ContractiblePaths
variable {Γ : Context.{u}} {A : Family Γ} (c : HomotopyContractible A)
  (F : Filling A) (hF : F.Lawful)
  {a b : Term A} {φ : Cofibration Γ}
  (s : PartialSection (homogeneousPath A a b) φ)

noncomputable def line : Term (reindex A (projection (interval Γ))) :=
  (c.reindex (projection (interval Γ))).extend (F.reindex (projection (interval Γ)))
    s.pathBoundary

include hF

theorem line_zero : (line c F s).reindex (endpointSub Γ false) = a := by
  apply Term.ext
  intro x
  let y := (endpointSub Γ false).mapElements.obj x
  have hy : (intervalFace Γ false).full y :=
    (Cofibration.full_endpoint (generic (interval Γ)) false y).mpr rfl
  have hp := pathBoundaryFace_endpoint φ false x
  exact ((c.reindex (projection (interval Γ))).extend_boundary
    (F.reindex (projection (interval Γ))) (hF.reindex _) s.pathBoundary y hp).trans
    (eq_of_heq (s.pathBoundary_zero y hp hy))

theorem line_one : (line c F s).reindex (endpointSub Γ true) = b := by
  apply Term.ext
  intro x
  let y := (endpointSub Γ true).mapElements.obj x
  have hy : (intervalFace Γ true).full y :=
    (Cofibration.full_endpoint (generic (interval Γ)) true y).mpr rfl
  have hp := pathBoundaryFace_endpoint φ true x
  exact ((c.reindex (projection (interval Γ))).extend_boundary
    (F.reindex (projection (interval Γ))) (hF.reindex _) s.pathBoundary y hp).trans
    (eq_of_heq (s.pathBoundary_one y hp hy))

noncomputable def extend : Term (homogeneousPath A a b) :=
  pathLam (line c F s) (line_zero c F hF s) (line_one c F hF s)

theorem extend_boundary (x : Γ.Elements) (hx : φ.full x) :
    (extend c F hF s).val x = s.val x hx := by
  apply Subtype.ext
  apply PiElement.ext
  intro y f r
  let z := extendObj (interval Γ) y r
  have hy : φ.full y := φ.full_natural f hx
  have hz : (pathBoundaryFace φ).full z := (Cofibration.full_join _ _ z).mpr (Or.inl hy)
  have h := (c.reindex (projection (interval Γ))).extend_boundary
    (F.reindex (projection (interval Γ))) (hF.reindex _) s.pathBoundary z hz
  have hs := congrArg (fun p => p.val.val (𝟙 y) r) (s.property f hx)
  refine (h.trans (s.pathBoundary_old z hz hy)).trans ?_
  change (s.val x hx).val.val (f ≫ 𝟙 y) r =
    (s.val y (φ.full_natural f hx)).val.val (𝟙 y) r at hs
  change (s.val y hy).val.val (𝟙 y) r = (s.val x hx).val.val f r
  simpa only [Category.comp_id] using hs.symm

end ContractiblePaths

namespace ContractibilityExtension
variable {Γ : Context.{u}} {A : Family Γ} (c : HomotopyContractible A)
  (F : Filling A) (hF : F.Lawful) {φ : Cofibration Γ}
  (s : PartialSection (contr A) φ)

noncomputable def center : Term A := c.extend F s.sigmaFst

include hF

theorem center_boundary (x : Γ.Elements) (hx : φ.full x) :
    (center c F s).val x = (s.val x hx).1 := c.extend_boundary F hF s.sigmaFst x hx

noncomputable def partialContraction :
    PartialSection (homogeneousPath (reindex A (projection A))
      ((center c F s).reindex (projection A)) (generic A)) (φ.reindex (projection A)) :=
  ((s.sigmaSnd (center c F s) (center_boundary c F hF s)).map
    (contractionsAtIso A (center c F s)).hom).app

noncomputable def witness : HomotopyContractible A where
  center := center c F s
  contraction := ContractiblePaths.extend (c.reindex (projection A)) (F.reindex (projection A))
    (hF.reindex _) (partialContraction c F hF s)

noncomputable def extend : Term (contr A) := encodeContr (witness c F hF s)
theorem extend_boundary (x : Γ.Elements) (hx : φ.full x) :
    (extend c F hF s).val x = s.val x hx := by
  let a := center c F s
  let ha := center_boundary c F hF s
  let e := contractionsAtIso A a
  let p := (s.sigmaSnd a ha).map e.hom
  let t := (witness c F hF s).contraction
  have ht (z : (total A).Elements) (hz : (φ.reindex (projection A)).full z) :
      t.val z = p.app.val z hz :=
    ContractiblePaths.extend_boundary (c.reindex (projection A))
      (F.reindex (projection A)) (hF.reindex _) (partialContraction c F hF s) z hz
  have hl : (lam t).val x = p.val x hx := by
    apply PiElement.ext
    intro y f v
    have h := congrArg (fun k => k.val (𝟙 y) v) (p.property f hx)
    refine (ht (extendObj A y v) (φ.full_natural f hx)).trans ?_
    change (p.val x hx).val (f ≫ 𝟙 y) v =
      (p.val y (φ.full_natural f hx)).val (𝟙 y) v at h
    change (p.val y (φ.full_natural f hx)).val (𝟙 y) v = (p.val x hx).val f v
    simpa only [Category.comp_id] using h.symm
  apply Sigma.ext (ha x hx)
  have hsecond : e.inv.app x ((lam t).val x) =
      (s.sigmaSnd a ha).val x hx :=
    (congrArg (e.inv.app x) hl).trans
      (congrArg (fun m => m.app x ((s.sigmaSnd a ha).val x hx)) e.hom_inv_id)
  exact (heq_of_eq hsecond).trans (s.sigmaSnd_val a ha x hx)

end ContractibilityExtension

/-- Extend internal contractibility witnesses after an arbitrary substitution. -/
noncomputable def contrExtend {Γ Δ : Context.{u}} {A : Family Γ}
    (c : HomotopyContractible A) (F : Filling A) (hF : F.Lawful)
    (σ : Δ ⟶ Γ) (φ : Cofibration Δ) (s : PartialSection (reindex (contr A) σ) φ) :
    Term (reindex (contr A) σ) :=
  Term.map (contrReindexIso A σ).inv
    (ContractibilityExtension.extend (c.reindex σ) (F.reindex σ) (hF.reindex σ)
      (s.map (contrReindexIso A σ).hom))

theorem contrExtend_boundary {Γ Δ : Context.{u}} {A : Family Γ}
    (c : HomotopyContractible A) (F : Filling A) (hF : F.Lawful)
    (σ : Δ ⟶ Γ) (φ : Cofibration Δ) (s : PartialSection (reindex (contr A) σ) φ)
    (x : Δ.Elements) (hx : φ.full x) : (contrExtend c F hF σ φ s).val x = s.val x hx :=
  (congrArg ((contrReindexIso A σ).inv.app x)
    (ContractibilityExtension.extend_boundary (c.reindex σ) (F.reindex σ) (hF.reindex σ)
      (s.map (contrReindexIso A σ).hom) x hx)).trans
    (congrArg (fun m => m.app x (s.val x hx)) (contrReindexIso A σ).hom_inv_id)

/-- An inhabited native contractibility family is itself contractible. -/
noncomputable def contrContractible {Γ : Context.{u}} {A : Family Γ}
    (c : HomotopyContractible A) (F : Filling A) (hF : F.Lawful) :
    HomotopyContractible (contr A) :=
  HomotopyContractible.ofExtensions (contrExtend c F hF) (contrExtend_boundary c F hF)

namespace IsEquivExtension
variable {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
  (e : HomotopyEquivalence f) (F : Filling A) (hF : F.Lawful)
  (G : Filling B) (hG : G.Lawful)
  {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Cofibration Δ)
  (s : PartialSection (reindex (isEquiv f) σ) φ)

abbrev fiber := homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)

noncomputable def extendedBody : Term (reindex (contr (fiber (f := f))) (liftSub B σ)) :=
  contrExtend e.fibers (genericFiberFilling f F hF G hG)
    (genericFiberFilling_lawful f F hF G hG) (liftSub B σ)
    (φ.reindex (projection (reindex B σ)))
    ((s.map (piReindex B (contr (fiber (f := f))) σ)).app)

noncomputable def extend : Term (reindex (isEquiv f) σ) :=
  Term.map (piReindexIso B (contr (fiber (f := f))) σ).inv
    (lam (extendedBody e F hF G hG σ φ s))

theorem extend_boundary (x : Δ.Elements) (hx : φ.full x) :
    (extend e F hF G hG σ φ s).val x = s.val x hx := by
  let i := piReindexIso B (contr (fiber (f := f))) σ
  let p := s.map i.hom
  have h : (lam (extendedBody e F hF G hG σ φ s)).val x = p.val x hx := by
    apply PiElement.ext
    intro y g v
    have hb := contrExtend_boundary e.fibers (genericFiberFilling f F hF G hG)
      (genericFiberFilling_lawful f F hF G hG) (liftSub B σ)
      (φ.reindex (projection (reindex B σ))) p.app
      (extendObj (reindex B σ) y v) (φ.full_natural g hx)
    have hp := congrArg (fun k => k.val (𝟙 y) v) (p.property g hx)
    refine hb.trans ?_
    change (p.val x hx).val (g ≫ 𝟙 y) v =
      (p.val y (φ.full_natural g hx)).val (𝟙 y) v at hp
    change (p.val y (φ.full_natural g hx)).val (𝟙 y) v = (p.val x hx).val g v
    simpa only [Category.comp_id] using hp.symm
  exact (congrArg (i.inv.app x) h).trans
    (congrArg (fun m => m.app x (s.val x hx)) i.hom_inv_id)
end IsEquivExtension

/-- Native equivalence witnesses form a contractible family whenever inhabited. -/
noncomputable def isEquivContractible {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (e : HomotopyEquivalence f) (F : Filling A) (hF : F.Lawful)
    (G : Filling B) (hG : G.Lawful) : HomotopyContractible (isEquiv f) :=
  HomotopyContractible.ofExtensions (IsEquivExtension.extend e F hF G hG)
    (IsEquivExtension.extend_boundary e F hF G hG)

/-- Isomorphism transport preserves the entire chosen contraction in a roundtrip. -/
theorem contrTransport_roundtrip {Γ : Context.{u}} {A B : Family Γ}
    (e : A ≅ B) (c : HomotopyContractible A) : (c.transport e).transport e.symm = c := by
  apply HomotopyContractible.ext
  · exact Term.map_iso_roundtrip e c.center
  · apply pathTerm_hext
    apply Term.ext
    intro x
    let y := (projection (interval (total A)) ≫ projection A).mapElements.obj x
    let z : A.obj y := x.val.1.2
    let r := x.val.2
    have hi (a : A.obj y) : e.inv.app y (e.hom.app y a) = a :=
      congrArg (fun m => m.app y a) e.hom_inv_id
    change e.inv.app y (e.hom.app y ((pathApp c.contraction).val
      (extendObj (interval (total A)) (extendObj A y (e.inv.app y (e.hom.app y z))) r))) =
      (pathApp c.contraction).val x
    let k : A.obj y → A.obj y := fun v => (pathApp c.contraction).val
      (extendObj (interval (total A)) (extendObj A y v) r)
    have hpoint : k (e.inv.app y (e.hom.app y z)) = k z := congrArg k (hi z)
    exact (hi _).trans hpoint


noncomputable def contrTransport {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) :
    HomotopyContractible A ≃ HomotopyContractible B where
  toFun c := c.transport e
  invFun c := c.transport e.symm
  left_inv := contrTransport_roundtrip e
  right_inv := contrTransport_roundtrip e.symm

/-- Reindexed equivalence sections retain the contraction before fiber presentation changes. -/
noncomputable def reindexedIsEquivSections {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) :
    HomotopyContractible (reindex
      (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)) (liftSub B σ)) ≃
      Term (reindex (isEquiv f) σ) := by
  let C := homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)
  let q := contrReindexIso C (liftSub B σ)
  let p := piReindexIso B (contr C) σ
  let sectionIso {E H : Family Δ} (i : E ≅ H) : Term E ≃ Term H := {
    toFun := Term.map i.hom
    invFun := Term.map i.inv
    left_inv := Term.map_iso_roundtrip i
    right_inv := Term.map_iso_roundtrip i.symm }
  let sectionIso' {E H : Family (total (reindex B σ))} (i : E ≅ H) : Term E ≃ Term H := {
    toFun := Term.map i.hom
    invFun := Term.map i.inv
    left_inv := Term.map_iso_roundtrip i
    right_inv := Term.map_iso_roundtrip i.symm }
  let abstraction : Term (reindex (contr C) (liftSub B σ)) ≃
      Term (pi (reindex B σ) (reindex (contr C) (liftSub B σ))) := {
    toFun := lam
    invFun := app
    left_inv := app_lam
    right_inv := lam_app }
  exact (contrSections _).trans ((sectionIso' q).symm.trans
    (abstraction.trans (sectionIso p).symm))

noncomputable def isEquivReindexSections {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) :
    HomotopyEquivalence (Functor.whiskerLeft σ.mapElements f) ≃ Term (reindex (isEquiv f) σ) := by
  let fibers : HomotopyEquivalence (Functor.whiskerLeft σ.mapElements f) ≃
      HomotopyContractible (homotopyFiber
        (Functor.whiskerLeft (projection (reindex B σ)).mapElements
          (Functor.whiskerLeft σ.mapElements f)) (generic (reindex B σ))) := {
    toFun := HomotopyEquivalence.fibers
    invFun := HomotopyEquivalence.mk
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact fibers.trans ((contrTransport (genericFiberReindexIso f σ).symm).trans
    (reindexedIsEquivSections f σ))

def mapSections {Γ : Context.{u}} (A B : Family Γ) : (A ⟶ B) ≃ Term (maps A B) where
  toFun := encodeMap
  invFun := decodeMap
  left_inv := decode_encodeMap
  right_inv := encode_decodeMap

def sigmaSections {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) :
    (Σ a : Term A, Term (reindex B (pair (𝟙 Γ) a))) ≃ Term (sigma A B) where
  toFun s := sigmaIntro s.1 s.2
  invFun s := ⟨sigmaFst s, sigmaSnd s⟩
  left_inv := fun _ => rfl
  right_inv := sigma_eta

/-- Internal equivalence sections preserve the map and all chosen fiber contractions. -/
noncomputable def equivSections {Γ : Context.{u}} (A B : Family Γ) :
    (Σ f : A ⟶ B, HomotopyEquivalence f) ≃ Term (equiv A B) :=
  (Equiv.sigmaCongr (mapSections A B) (fun f =>
    isEquivReindexSections (universalMap A B) (pair (𝟙 Γ) (encodeMap f)))).trans
    (sigmaSections (maps A B) (isEquiv (universalMap A B)))

noncomputable def contractAt {Γ : Context.{u}} {A : Family Γ}
    (c : Term A)
    (extend : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Cofibration Δ),
      PartialSection (Presheaf.reindex A σ) φ → Term (Presheaf.reindex A σ))
    (boundary : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Cofibration Δ)
      (a : PartialSection (Presheaf.reindex A σ) φ) (x : Δ.Elements) (hx : φ.full x),
      (extend σ φ a).val x = a.val x hx) : HomotopyContractible A := by
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


/-- Any two sections of the native equivalence-witness family are joined by a native path. -/
noncomputable def isEquivPath {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (a b : Term (isEquiv f)) : Term (homogeneousPath (isEquiv f) a b) :=
  (contractAt a (IsEquivExtension.extend (decodeIsEquiv a) F hF G hG)
    (IsEquivExtension.extend_boundary (decodeIsEquiv a) F hF G hG)).pathTo b

noncomputable def contractionPathsFilling {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : Filling (contractionPaths A) :=
  pathFilling (F.reindex (projection (interval (total (reindex A (projection A)))) ≫
    projection (reindex A (projection A)) ≫ projection A)) (hF.reindex _)
    ((generic A).reindex (projection (reindex A (projection A))))
    (generic (reindex A (projection A)))

theorem contractionPathsFilling_lawful {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : (contractionPathsFilling F hF).Lawful :=
  pathFilling_lawful _ (hF.reindex _) _ _

noncomputable def contractionsFilling {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : Filling (contractions A) :=
  piFilling (F.reindex (projection A)) (hF.reindex _) (contractionPathsFilling F hF)

theorem contractionsFilling_lawful {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : (contractionsFilling F hF).Lawful :=
  piFilling_lawful _ (hF.reindex _) _ (contractionPathsFilling_lawful F hF)

noncomputable def contrFilling {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : Filling (contr A) :=
  sigmaFilling F hF (contractionsFilling F hF)

theorem contrFilling_lawful {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : (contrFilling F hF).Lawful :=
  sigmaFilling_lawful F hF _ (contractionsFilling_lawful F hF)

noncomputable def isEquivFilling {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) : Filling (isEquiv f) :=
  piFilling G hG (contrFilling (genericFiberFilling f F hF G hG)
    (genericFiberFilling_lawful f F hF G hG))

theorem isEquivFilling_lawful {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) :
    (isEquivFilling f F hF G hG).Lawful :=
  piFilling_lawful G hG _ (contrFilling_lawful _ (genericFiberFilling_lawful f F hF G hG))

noncomputable def mapsFilling {Γ : Context.{u}} {A B : Family Γ}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) : Filling (maps A B) :=
  piFilling F hF (G.reindex (projection A))

theorem mapsFilling_lawful {Γ : Context.{u}} {A B : Family Γ}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) :
    (mapsFilling F hF G).Lawful := piFilling_lawful F hF _ (hG.reindex _)

noncomputable def equivFilling {Γ : Context.{u}} {A B : Family Γ}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) : Filling (equiv A B) :=
  sigmaFilling (mapsFilling F hF G) (mapsFilling_lawful F hF G hG)
    (isEquivFilling (universalMap A B)
      (F.reindex (projection (maps A B))) (hF.reindex _)
      (G.reindex (projection (maps A B))) (hG.reindex _))

theorem equivFilling_lawful {Γ : Context.{u}} {A B : Family Γ}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) :
    (equivFilling F hF G hG).Lawful :=
  sigmaFilling_lawful _ (mapsFilling_lawful F hF G hG) _
    (isEquivFilling_lawful _ _ (hF.reindex _) _ (hG.reindex _))

/-- The reindexed section bridge agrees with native equivalence substitution, retaining choices. -/
theorem isEquivReindexSections_reindex {Γ Δ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (e : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    isEquivReindexSections f σ (e.reindex σ) = (encodeIsEquiv e).reindex σ := by
  let C := homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)
  let τ := liftSub B σ
  let q := contrReindexIso C τ
  let p := piReindexIso B (contr C) σ
  let i := genericFiberReindexIso f σ
  have hc := contrTransport_roundtrip i (e.fibers.reindex τ)
  have hq : Term.map q.inv (encodeContr (e.fibers.reindex τ)) = (encodeContr e.fibers).reindex τ :=
    (congrArg (Term.map q.inv) (encodeContr_reindex e.fibers τ).symm).trans
      (Term.map_iso_roundtrip q ((encodeContr e.fibers).reindex τ))
  have hp : Term.map p.hom ((encodeIsEquiv e).reindex σ) =
      lam ((encodeContr e.fibers).reindex τ) := lam_reindex (encodeContr e.fibers) σ
  exact (congrArg (fun c => Term.map p.inv (lam (Term.map q.inv (encodeContr c)))) hc).trans
    ((congrArg (fun t => Term.map p.inv (lam t)) hq).trans
      ((congrArg (Term.map p.inv) hp.symm).trans
        (Term.map_iso_roundtrip p ((encodeIsEquiv e).reindex σ))))

/-- Reindexing of the native map family retains every generalized argument. -/
noncomputable def mapReindexSections {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ) :
    (reindex A σ ⟶ reindex B σ) ≃ Term (reindex (maps A B) σ) :=
  (mapSections (reindex A σ) (reindex B σ)).trans {
    toFun := Term.map (piReindexIso A (reindex B (projection A)) σ).inv
    invFun := Term.map (piReindexIso A (reindex B (projection A)) σ).hom
    left_inv := Term.map_iso_roundtrip (piReindexIso A (reindex B (projection A)) σ).symm
    right_inv := Term.map_iso_roundtrip (piReindexIso A (reindex B (projection A)) σ) }

/-- Evaluate the generic map after a substituted, encoded family morphism. -/
theorem universalMap_reindex_encoded {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (f : reindex A σ ⟶ reindex B σ) :
    Functor.whiskerLeft (pair σ (mapReindexSections A B σ f)).mapElements (universalMap A B) = f := by
  let p := piReindexIso A (reindex B (projection A)) σ
  have h := Term.map_iso_roundtrip p.symm (encodeMap f)
  exact congrArg (@decodeMap Δ (reindex A σ) (reindex B σ)) h

/-- Full equivalence sections after substitution preserve the map and chosen fiber contractions. -/
noncomputable def equivReindexSections {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ) :
    (Σ f : reindex A σ ⟶ reindex B σ, HomotopyEquivalence f) ≃
      Term (reindex (equiv A B) σ) := by
  let mapsEq := mapReindexSections A B σ
  let fiberEq (f : reindex A σ ⟶ reindex B σ) : HomotopyEquivalence f ≃
      Term (reindex (isEquiv (universalMap A B)) (pair σ (mapsEq f))) :=
    (Equiv.cast (congrArg HomotopyEquivalence (universalMap_reindex_encoded A B σ f).symm)).trans
      (isEquivReindexSections (universalMap A B) (pair σ (mapsEq f)))
  exact (Equiv.sigmaCongr mapsEq fiberEq).trans
    (sigmaSections (reindex (maps A B) σ)
      (reindex (isEquiv (universalMap A B)) (liftSub (maps A B) σ)))

end EquivalenceFamilies
end SquareKit.Cubical.Presheaf
