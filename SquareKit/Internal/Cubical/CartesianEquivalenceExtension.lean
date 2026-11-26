import SquareKit.Internal.Cubical.CartesianHomotopyEquivalences
import SquareKit.Internal.Cubical.CartesianPiFilling

/-! Uniform extension in actual Cartesian homotopy fibers. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

namespace Homotopy
noncomputable def fiberFilling {Γ : Context.{u}} {A B : Family Γ}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (f : A ⟶ B) (b : Term B) : Filling (fiber f b) :=
  sigmaFilling F hF
    (pathFilling (G.reindex (projection (interval (total A)) ≫ projection A))
      (hG.reindex _) _ _)

theorem fiberFilling_lawful {Γ : Context.{u}} {A B : Family Γ}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (f : A ⟶ B) (b : Term B) : (fiberFilling F hF G hG f b).Lawful :=
  sigmaFilling_lawful F hF _ (pathFilling_lawful _ (hG.reindex _) _ _)
end Homotopy

namespace HomotopyEquivalence
variable {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}

def fiberAt (e : HomotopyEquivalence f) (b : Term B) : Contractible (Homotopy.fiber f b) :=
  Contractible.map (Homotopy.fiberReindexIso
    (Functor.whiskerLeft (projection B).mapElements f) (generic B) (pair (𝟙 Γ) b))
    (e.fibers.reindex (pair (𝟙 Γ) b))

noncomputable def extend (e : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (b : Term B) {φ : Subcontext Γ} (t : PartialSection (Homotopy.fiber f b) φ) :
    Term (Homotopy.fiber f b) :=
  (e.fiberAt b).extend (Homotopy.fiberFilling F hF G hG f b) t

theorem extend_boundary (e : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (b : Term B) {φ : Subcontext Γ} (t : PartialSection (Homotopy.fiber f b) φ)
    (x : Γ.Elements) (hx : φ.Holds x) : (e.extend F hF G hG b t).val x = t.val x hx :=
  Contractible.extend_boundary _ _ (Homotopy.fiberFilling_lawful F hF G hG f b) t x hx

noncomputable def extendAlong {Δ : Context.{u}} (e : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (σ : Δ ⟶ total B) {φ : Subcontext Δ}
    (a : PartialSection (Cartesian.reindex (Homotopy.genericFiber f) σ) φ) :=
  (e.fibers.reindex σ).extend
    ((Homotopy.fiberFilling (F.reindex (projection B)) (hF.reindex _)
      (G.reindex (projection B)) (hG.reindex _) _ (generic B)).reindex σ) a

theorem extendAlong_boundary {Δ : Context.{u}} (e : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (σ : Δ ⟶ total B) {φ : Subcontext Δ}
    (a : PartialSection (Cartesian.reindex (Homotopy.genericFiber f) σ) φ)
    (x : Δ.Elements) (hx : φ.Holds x) : (e.extendAlong F hF G hG σ a).val x = a.val x hx :=
  (e.fibers.reindex σ).extend_boundary _
    ((Homotopy.fiberFilling_lawful _ (hF.reindex _) _ (hG.reindex _) _ _).reindex σ) a x hx

theorem extendAlong_reindex {Δ Θ : Context.{u}} (e : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (σ : Δ ⟶ total B) {φ : Subcontext Δ}
    (a : PartialSection (Cartesian.reindex (Homotopy.genericFiber f) σ) φ) (τ : Θ ⟶ Δ) :
    e.extendAlong F hF G hG (τ ≫ σ) (a.reindex τ) =
      Term.reindex (e.extendAlong F hF G hG σ a) τ :=
  (e.fibers.reindex σ).extend_reindex _
    ((Homotopy.fiberFilling_lawful _ (hF.reindex _) _ (hG.reindex _) _ _).reindex σ) a τ

end HomotopyEquivalence



theorem pathFilling_reindex_family {Γ Δ E : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term (reindex B (endpointSub Γ false))) (a₁ : Term (reindex B (endpointSub Γ true)))
    (σ : E ⟶ Γ) (p : total (interval Δ) ⟶ E) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (path B a₀ a₁) (p ≫ σ)) φ r) :
    (pathFilling (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _) ((Term.reindex a₀ σ)) ((Term.reindex a₁ σ))).fill p φ r
      (b.map (Functor.whiskerLeft p.mapElements (pathReindex B a₀ a₁ σ))) =
      Term.map (Functor.whiskerLeft p.mapElements (pathReindex B a₀ a₁ σ))
        ((pathFilling F hF a₀ a₁).fill (p ≫ σ) φ r b) := by
  apply Term.map_injective_of_iso (pathReindexIso (reindex B (liftSub (interval Γ) σ))
    ((Term.reindex a₀ σ)) ((Term.reindex a₁ σ)) p)
  change Term.map (pathReindex (reindex B (liftSub (interval Γ) σ)) ((Term.reindex a₀ σ)) ((Term.reindex a₁ σ)) p) _ = _
  change Term.map _ (pathFillingResult p φ r _ _ _) = _
  let b' := b.map (Functor.whiskerLeft p.mapElements (pathReindex B a₀ a₁ σ))
  have hn := pathFillingResult_normalize p φ r b'
    ((F.reindex (liftSub (interval Γ) σ)).fill (pathFillingContext p) (pathBoundaryFace φ) (Term.reindex r (projection (interval Δ))) (pathFillingBox p φ r b'))
    ((hF.reindex (liftSub (interval Γ) σ)).fills (pathFillingContext p) (pathBoundaryFace φ) (Term.reindex r (projection (interval Δ))) (pathFillingBox p φ r b'))
  exact hn.trans (pathFillingResult_normalize (p ≫ σ) φ r b
    (F.fill (pathFillingContext (p ≫ σ)) (pathBoundaryFace φ) (Term.reindex r (projection (interval Δ))) (pathFillingBox (p ≫ σ) φ r b))
    (hF.fills _ _ _ _)).symm


theorem pathFilling_reindex_iso {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term (reindex B (endpointSub Γ false))) (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) :
    ((pathFilling F hF a₀ a₁).reindex σ).transport (pathReindexIso B a₀ a₁ σ) =
      pathFilling (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _) (Term.reindex a₀ σ) (Term.reindex a₁ σ) := by
  apply Filling.ext
  intro Θ p φ r b
  let e := Functor.isoWhiskerLeft p.mapElements (pathReindexIso B a₀ a₁ σ)
  have h := pathFilling_reindex_family F hF a₀ a₁ σ p φ r (b.map e.inv)
  have hb := OpenBox.map_iso_roundtrip e b
  exact h.symm.trans (congrArg (fun z =>
    (pathFilling (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _) (Term.reindex a₀ σ) (Term.reindex a₁ σ)).fill p φ r z) hb)

namespace EquivalenceFamilies

/-- The native paths from a generic proposed center to a second generic element. -/
abbrev contractionPaths {Γ : Context.{u}} (A : Family Γ) :=
  homogeneousPath
    (reindex (reindex A (projection A)) (projection (reindex A (projection A))))
    ((Term.reindex (generic A) (projection (reindex A (projection A)))))
    (generic (reindex A (projection A)))

/-- A contraction with a specified generic center. -/
def contractions {Γ : Context.{u}} (A : Family Γ) : Family (total A) :=
  pi (reindex A (projection A)) (contractionPaths A)

/-- Internal contractibility includes both the center and all native paths. -/
def contr {Γ : Context.{u}} (A : Family Γ) : Family Γ := sigma A (contractions A)

/-- Reindex homogeneous paths with their specified endpoint sections. -/
def homogeneousReindexIso {Γ Δ : Context.{u}} (A : Family Γ) (a b : Term A)
    (σ : Δ ⟶ Γ) : reindex (homogeneousPath A a b) σ ≅
      homogeneousPath (reindex A σ) ((Term.reindex a σ)) (Term.reindex b σ) :=
  pathReindexIso (reindex A (projection (interval Γ))) a b σ

/-- Substituting a center recovers the path family in external contractibility. -/
def contractionPathsAt {Γ : Context.{u}} (A : Family Γ) (c : Term A) :
    reindex (contractionPaths A)
      (liftSub (reindex A (projection A)) (pair (𝟙 Γ) c)) ≅
    homogeneousPath (reindex A (projection A)) (Term.reindex c (projection A)) (generic A) := by
  let τ : total A ⟶ total (reindex A (projection A)) :=
    liftSub (reindex A (projection A)) (pair (𝟙 Γ) c)
  let C := reindex
    (reindex (reindex A (projection A)) (projection (reindex A (projection A)))) τ
  let a := (Term.reindex ((Term.reindex (generic A) (projection (reindex A (projection A))))) τ)
  let b := (Term.reindex (generic (reindex A (projection A))) τ)
  let j : homogeneousPath C a b ≅
      homogeneousPath (reindex A (projection A)) (Term.reindex c (projection A)) (generic A) := {
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
    ((Term.reindex (generic A) (projection (reindex A (projection A)))))
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
      pi A (homogeneousPath (reindex A (projection A)) (Term.reindex c (projection A)) (generic A)) :=
  piReindexIso (reindex A (projection A)) (contractionPaths A) (pair (𝟙 Γ) c) ≪≫
    piSecondIso A (contractionPathsAt A c)


noncomputable def encodeContr {Γ : Context.{u}} {A : Family Γ}
    (c : Contractible A) : Term (contr A) :=
  sigmaIntro c.center (Term.map (contractionsAtIso A c.center).inv (lam c.toContraction))

def decodeContr {Γ : Context.{u}} {A : Family Γ}
    (s : Term (contr A)) : Contractible A :=
  Contractible.ofContraction (sigmaFst s)
    (app (Term.map (contractionsAtIso A (sigmaFst s)).hom (sigmaSnd s)))

@[simp] theorem decode_encodeContr {Γ : Context.{u}} {A : Family Γ}
    (c : Contractible A) : decodeContr (encodeContr c) = c := by
  let e := contractionsAtIso A c.center
  have hp : app (Term.map e.hom (Term.map e.inv (lam c.toContraction))) = c.toContraction :=
    (congrArg app (Term.map_iso_roundtrip e.symm (lam c.toContraction))).trans (app_lam _)
  exact (congrArg (Contractible.ofContraction c.center) hp).trans c.of_toContraction

@[simp] theorem encode_decodeContr {Γ : Context.{u}} {A : Family Γ}
    (s : Term (contr A)) : encodeContr (decodeContr s) = s := by
  let e := contractionsAtIso A (sigmaFst s)
  have hp : Term.map e.inv (lam (app (Term.map e.hom (sigmaSnd s)))) = sigmaSnd s :=
    (congrArg (Term.map e.inv) (lam_app (Term.map e.hom (sigmaSnd s)))).trans
      (Term.map_iso_roundtrip e (sigmaSnd s))
  have ht := Contractible.to_ofContraction (sigmaFst s) (app (Term.map e.hom (sigmaSnd s)))
  exact (congrArg (fun z => sigmaIntro (sigmaFst s) (Term.map e.inv (lam z))) ht).trans
    ((congrArg (sigmaIntro (sigmaFst s)) hp).trans (sigma_eta s))

noncomputable def contrSections {Γ : Context.{u}} (A : Family Γ) :
    Contractible A ≃ Term (contr A) where
  toFun := encodeContr
  invFun := decodeContr
  left_inv := decode_encodeContr
  right_inv := encode_decodeContr

def contrReindexIso {Γ Δ : Context.{u}} (A : Family Γ) (σ : Δ ⟶ Γ) :
    reindex (contr A) σ ≅ contr (reindex A σ) :=
  Homotopy.sigmaSecondIso _
    (piReindexIso (reindex A (projection A)) (contractionPaths A) (liftSub A σ) ≪≫
      piSecondIso _ (pathReindexIso
        (reindex (reindex (reindex A (projection A)) (projection (reindex A (projection A))))
          (projection (interval (total (reindex A (projection A))))))
        ((Term.reindex (generic A) (projection (reindex A (projection A)))))
        (generic (reindex A (projection A)))
        (liftSub (reindex A (projection A)) (liftSub A σ))))

def isEquiv {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) : Family Γ :=
  pi B (contr (Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f)
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



theorem contrTransport_roundtrip {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B)
    (c : Contractible A) : Contractible.map e.symm (Contractible.map e c) = c := by
  refine Contractible.ext (Term.map_iso_roundtrip e c.center) ?_
  intro x a y f r
  change e.inv.app y (e.hom.app y ((c.contraction x (e.inv.app x (e.hom.app x a))).val.val f r)) = _
  exact (e.hom_inv_id_app_apply y _).trans
    (congrArg (fun a => (c.contraction x a).val.val f r) (e.hom_inv_id_app_apply x a))

noncomputable def contrTransport {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) :
    Contractible A ≃ Contractible B where
  toFun := Contractible.map e
  invFun := Contractible.map e.symm
  left_inv := contrTransport_roundtrip e
  right_inv := contrTransport_roundtrip e.symm

noncomputable def reindexedIsEquivSections {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) :
    Contractible (reindex
      (Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)) (liftSub B σ)) ≃
      Term (reindex (isEquiv f) σ) := by
  let C := Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)
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
      Contractible (Homotopy.fiber
        (Functor.whiskerLeft (projection (reindex B σ)).mapElements
          (Functor.whiskerLeft σ.mapElements f)) (generic (reindex B σ))) := {
    toFun := HomotopyEquivalence.fibers
    invFun := HomotopyEquivalence.mk
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact fibers.trans ((contrTransport (Homotopy.fiberReindexIso (Functor.whiskerLeft (projection B).mapElements f) (generic B) (liftSub B σ)).symm).trans
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



noncomputable def contrFilling {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : Filling (contr A) :=
  sigmaFilling F hF (piFilling (F.reindex (projection A)) (hF.reindex _)
    (pathFilling (F.reindex (projection (interval (total (reindex A (projection A)))) ≫
      projection (reindex A (projection A)) ≫ projection A)) (hF.reindex _) _ _))

theorem contrFilling_lawful {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) : (contrFilling F hF).Lawful :=
  sigmaFilling_lawful F hF _ (piFilling_lawful _ (hF.reindex _) _
    (pathFilling_lawful _ (hF.reindex _) _ _))

noncomputable def isEquivFilling {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) : Filling (isEquiv f) :=
  piFilling G hG (contrFilling
    (Homotopy.fiberFilling (F.reindex (projection B)) (hF.reindex _)
      (G.reindex (projection B)) (hG.reindex _) _ (generic B))
    (Homotopy.fiberFilling_lawful _ (hF.reindex _) _ (hG.reindex _) _ _))

theorem isEquivFilling_lawful {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) :
    (isEquivFilling f F hF G hG).Lawful :=
  piFilling_lawful G hG _ (contrFilling_lawful _
    (Homotopy.fiberFilling_lawful _ (hF.reindex _) _ (hG.reindex _) _ _))

noncomputable def equivFilling {Γ : Context.{u}} {A B : Family Γ}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) : Filling (equiv A B) :=
  sigmaFilling (piFilling F hF (G.reindex (projection A)))
    (piFilling_lawful F hF _ (hG.reindex _))
    (isEquivFilling (universalMap A B) (F.reindex (projection (maps A B))) (hF.reindex _)
      (G.reindex (projection (maps A B))) (hG.reindex _))

theorem equivFilling_lawful {Γ : Context.{u}} {A B : Family Γ}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) : (equivFilling F hF G hG).Lawful :=
  sigmaFilling_lawful _ (piFilling_lawful F hF _ (hG.reindex _)) _
    (isEquivFilling_lawful _ _ (hF.reindex _) _ (hG.reindex _))

end EquivalenceFamilies

namespace Contractible
variable {Γ : Context.{u}} {A : Family Γ} (c : Contractible A)
theorem extensionTube_transport {B : Family Γ} (e : A ≅ B) {φ : Subcontext Γ}
    (a : PartialSection A φ) :
    (Contractible.map e c).extensionTube (a.map e.hom) =
      (c.extensionTube a).map (Functor.whiskerLeft (projection (interval Γ)).mapElements e.hom) := by
  apply PartialSection.ext
  intro x hx
  let y := (projection (interval Γ)).mapElements.obj x
  exact congrArg (fun z => e.hom.app y ((c.contraction y z).val.val (𝟙 _) x.val.2))
    (e.hom_inv_id_app_apply y (a.val y hx))

theorem extensionBox_transport {B : Family Γ} (e : A ≅ B) {φ : Subcontext Γ}
    (a : PartialSection A φ) :
    (Contractible.map e c).extensionBox (a.map e.hom) =
      (c.extensionBox a).map (Functor.whiskerLeft (projection (interval Γ)).mapElements e.hom) := by
  apply OpenBox.ext
  · exact c.extensionTube_transport e a
  · rfl

theorem extend_transport {B : Family Γ} (e : A ≅ B) (F : Filling A)
    {φ : Subcontext Γ} (a : PartialSection A φ) :
    (Contractible.map e c).extend (F.transport e) (a.map e.hom) = Term.map e.hom (c.extend F a) := by
  let i := Functor.isoWhiskerLeft (projection (interval Γ)).mapElements e
  have hb : ((Contractible.map e c).extensionBox (a.map e.hom)).map i.inv = c.extensionBox a :=
    (congrArg (fun b => b.map i.inv) (c.extensionBox_transport e a)).trans
      (OpenBox.map_iso_roundtrip i.symm (c.extensionBox a))
  exact congrArg (fun b => Term.map e.hom
    (F.comp (projection (interval Γ)) φ (endpoint Γ false) (endpoint Γ true) b)) hb
end Contractible
private theorem familyMap_value_heq {Γ : Context.{u}} {A B : Family Γ} (e : A ⟶ B)
    {x y : Γ.Elements} (h : x = y) {a : A.obj x} {b : A.obj y} (hab : HEq a b) :
    HEq (e.app x a) (e.app y b) := by
  cases h
  cases hab
  rfl

theorem sigmaSecondMap_box_snd {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {B C : Family (total A)} (e : B ≅ C) {φ : Subcontext Γ}
    (r : Term (interval Γ)) (b : OpenBox (sigma A B) φ r) (a : Term A) (ha : b.sigmaFst.Fills a) :
    OpenBox.sigmaSnd (B := C) (b.map ((Homotopy.sigmaSecondIso A e).hom)) a ha =
      (b.sigmaSnd a ha).map (Functor.whiskerLeft (pair (𝟙 _) a).mapElements e.hom) := by
  apply OpenBox.ext
  · apply PartialSection.ext
    intro x hx
    have hl := PartialSection.sigmaSnd_val (B := C)
      (b.tube.map ((Homotopy.sigmaSecondIso A e).hom)) a ha.2 x hx
    have hr := familyMap_value_heq e.hom (congrArg (extendObj A x) (ha.2 x hx))
      (PartialSection.sigmaSnd_val b.tube a ha.2 x hx)
    exact eq_of_heq (hl.trans hr.symm)
  · apply Term.ext
    intro x
    let σ := graph r
    have hl := Term.sigmaSndOver_val (B := Cartesian.reindex C (liftSub A σ))
      (Term.map (Functor.whiskerLeft σ.mapElements ((Homotopy.sigmaSecondIso A e).hom)) b.base)
      (Term.reindex a σ) ha.1 x
    have hr := familyMap_value_heq e.hom
      (congrArg (extendObj A (σ.mapElements.obj x)) (congrArg (fun t => t.val x) ha.1))
      (Term.sigmaSndOver_val (B := Cartesian.reindex B (liftSub A σ))
        b.base (Term.reindex a σ) ha.1 x)
    exact eq_of_heq (hl.trans hr.symm)

theorem sigmaFilling_transport_second {Γ : Context.{u}} {A : Family Γ}
    {B C : Family (total A)} (e : B ≅ C) (F : Filling A) (hF : F.Lawful) (G : Filling B) :
    (sigmaFilling F hF G).transport (Homotopy.sigmaSecondIso A e) = sigmaFilling F hF (G.transport e) := by
  apply Filling.ext
  intro Δ p φ r b
  let first := OpenBox.sigmaFst (B := Cartesian.reindex C (liftSub A p)) b
  let a := F.fill p φ r first
  have ha : first.Fills a := hF.fills p φ r first
  let i := Functor.isoWhiskerLeft (liftSub A p).mapElements e
  have hs := sigmaSecondMap_box_snd i.symm r b a ha
  exact congrArg (fun c => sigmaIntro (B := Cartesian.reindex C (liftSub A p)) a
    (Term.map (Functor.whiskerLeft (pair p a).mapElements e.hom) (G.fill (pair p a) φ r c))) hs



def genericFiberReindexIso {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (σ : Δ ⟶ Γ) :
    reindex (Homotopy.genericFiber f) (liftSub B σ) ≅
      Homotopy.genericFiber (Functor.whiskerLeft σ.mapElements f) :=
  Homotopy.fiberReindexIso (Functor.whiskerLeft (projection B).mapElements f) (generic B) (liftSub B σ)

noncomputable def genericFiberFilling {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) :
    Filling (Homotopy.genericFiber f) :=
  Homotopy.fiberFilling (F.reindex (projection B)) (hF.reindex _)
    (G.reindex (projection B)) (hG.reindex _) _ (generic B)

theorem genericFiberFilling_lawful {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) :
    (genericFiberFilling f F hF G hG).Lawful :=
  Homotopy.fiberFilling_lawful _ (hF.reindex _) _ (hG.reindex _) _ _

set_option maxHeartbeats 1600000 in
theorem genericFiberFilling_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) (σ : Δ ⟶ Γ) :
    ((genericFiberFilling f F hF G hG).reindex (liftSub B σ)).transport (genericFiberReindexIso f σ) =
    genericFiberFilling (Functor.whiskerLeft σ.mapElements f)
      (F.reindex σ) (hF.reindex _) (G.reindex σ) (hG.reindex _) := by
  let τ := liftSub B σ
  let A₀ := Cartesian.reindex A (projection B)
  let ρ := liftSub A₀ τ
  let a₀ := Term.map (Functor.whiskerLeft (projection A₀).mapElements
    (Functor.whiskerLeft (projection B).mapElements f)) (generic A₀)
  let a₁ := Term.reindex (generic B) (projection A₀)
  let R := G.reindex (projection (interval (total A₀)) ≫ projection A₀ ≫ projection B)
  have hR : R.Lawful := hG.reindex _
  have hfirst := sigmaFilling_transport_second
    (pathReindexIso (Cartesian.reindex B
      (projection (interval (total A₀)) ≫ projection A₀ ≫ projection B)) a₀ a₁ ρ) (F.reindex (τ ≫ projection B)) (hF.reindex _)
    ((pathFilling R hR a₀ a₁).reindex ρ)
  exact hfirst.trans (congrArg (sigmaFilling (F.reindex (τ ≫ projection B)) (hF.reindex _))
    (pathFilling_reindex_iso R hR a₀ a₁ ρ))

theorem HomotopyEquivalence.extendAlong_input_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    {f : A ⟶ B} (E : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) (σ : Δ ⟶ Γ)
    (ρ : Θ ⟶ total (Cartesian.reindex B σ)) {φ : Subcontext Θ}
    (a : PartialSection (Cartesian.reindex
      (Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f) (generic B))
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
  exact (congrArg (fun K => (Contractible.map i c).extend K (a.map i.hom)) hf).symm.trans
    (c.extend_transport i H a)



noncomputable def Contractible.ofExtensions {Γ : Context.{u}} {A : Family Γ}
    (extend : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ),
      PartialSection (Cartesian.reindex A σ) φ → Term (Cartesian.reindex A σ))
    (boundary : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
      (a : PartialSection (Cartesian.reindex A σ) φ) (x : Δ.Elements) (hx : φ.Holds x),
      (extend σ φ a).val x = a.val x hx) : Contractible A := by
  let empty : PartialSection (Cartesian.reindex A (𝟙 Γ)) ((Subcontext.bot (Γ := Γ))) :=
    ⟨fun _ h => h.elim, fun _ h => h.elim⟩
  let c : Term A := extend (𝟙 Γ) ((Subcontext.bot (Γ := Γ))) empty
  let π := projection A
  let p := projection (interval (total A)) ≫ π
  let φ := (intervalFace (total A) false).join (intervalFace (total A) true)
  let b := endpointBoundary (Cartesian.reindex A p) (Term.reindex c π) (generic A)
  let s := extend p φ b
  have h₀ : Term.reindex s (endpointSub (total A) false) = Term.reindex c π := by
    apply Term.ext
    intro x
    let y := (endpointSub (total A) false).mapElements.obj x
    have hy : (intervalFace (total A) false).Holds y :=
      rfl
    have hu : φ.Holds y := (Subcontext.full_join _ _ y).mpr (Or.inl hy)
    exact (boundary p φ b y hu).trans (eq_of_heq
      ((heq_of_eq (endpointBoundary_zero _ _ _ y hu hy)).trans
        (endpointSection_val (Cartesian.reindex A p) false (Term.reindex c π) y hy)))
  have h₁ : Term.reindex s (endpointSub (total A) true) = generic A := by
    apply Term.ext
    intro x
    let y := (endpointSub (total A) true).mapElements.obj x
    have hy : (intervalFace (total A) true).Holds y :=
      rfl
    have hu : φ.Holds y := (Subcontext.full_join _ _ y).mpr (Or.inr hy)
    exact (boundary p φ b y hu).trans (eq_of_heq
      ((heq_of_eq (endpointBoundary_one _ _ _ y hu hy)).trans
        (endpointSection_val (Cartesian.reindex A p) true (generic A) y hy)))
  exact Contractible.ofContraction c (pathLam s h₀ h₁)



namespace EquivalenceFamilies
namespace ContractiblePaths
variable {Γ : Context.{u}} {A : Family Γ} (c : Contractible A)
  (F : Filling A) (hF : F.Lawful)
  {a b : Term A} {φ : Subcontext Γ}
  (s : PartialSection (homogeneousPath A a b) φ)

noncomputable def line : Term (reindex A (projection (interval Γ))) :=
  (c.reindex (projection (interval Γ))).extend (F.reindex (projection (interval Γ)))
    s.pathBoundary

include hF

theorem line_zero : Term.reindex (line c F s) (endpointSub Γ false) = a := by
  apply Term.ext
  intro x
  let y := (endpointSub Γ false).mapElements.obj x
  have hy : (intervalFace Γ false).Holds y :=
    rfl
  have hp := pathBoundaryFace_endpoint φ false x
  exact ((c.reindex (projection (interval Γ))).extend_boundary
    (F.reindex (projection (interval Γ))) (hF.reindex _) s.pathBoundary y hp).trans
    (eq_of_heq (s.pathBoundary_zero y hp hy))

theorem line_one : Term.reindex (line c F s) (endpointSub Γ true) = b := by
  apply Term.ext
  intro x
  let y := (endpointSub Γ true).mapElements.obj x
  have hy : (intervalFace Γ true).Holds y :=
    rfl
  have hp := pathBoundaryFace_endpoint φ true x
  exact ((c.reindex (projection (interval Γ))).extend_boundary
    (F.reindex (projection (interval Γ))) (hF.reindex _) s.pathBoundary y hp).trans
    (eq_of_heq (s.pathBoundary_one y hp hy))

noncomputable def extend : Term (homogeneousPath A a b) :=
  pathLam (line c F s) (line_zero c F hF s) (line_one c F hF s)

theorem extend_boundary (x : Γ.Elements) (hx : φ.Holds x) :
    (extend c F hF s).val x = s.val x hx := by
  apply Subtype.ext
  apply PiElement.ext
  intro y f r
  let z := extendObj (interval Γ) y r
  have hy : φ.Holds y := φ.natural f hx
  have hz : (pathBoundaryFace φ).Holds z := (Subcontext.full_join _ _ z).mpr (Or.inl hy)
  have h := (c.reindex (projection (interval Γ))).extend_boundary
    (F.reindex (projection (interval Γ))) (hF.reindex _) s.pathBoundary z hz
  have hs := congrArg (fun p => p.val.val (𝟙 y) r) (s.natural f hx)
  refine (h.trans (s.pathBoundary_old z hz hy)).trans ?_
  change (s.val x hx).val.val (f ≫ 𝟙 y) r =
    (s.val y (φ.natural f hx)).val.val (𝟙 y) r at hs
  change (s.val y hy).val.val (𝟙 y) r = (s.val x hx).val.val f r
  simpa only [Category.comp_id] using hs.symm

end ContractiblePaths

namespace ContractibilityExtension
variable {Γ : Context.{u}} {A : Family Γ} (c : Contractible A)
  (F : Filling A) (hF : F.Lawful) {φ : Subcontext Γ}
  (s : PartialSection (contr A) φ)

noncomputable def center : Term A := c.extend F s.sigmaFst

include hF

theorem center_boundary (x : Γ.Elements) (hx : φ.Holds x) :
    (center c F s).val x = (s.val x hx).1 := c.extend_boundary F hF s.sigmaFst x hx

noncomputable def partialContraction :
    PartialSection (homogeneousPath (reindex A (projection A))
      (Term.reindex (center c F s) (projection A)) (generic A)) (φ.reindex (projection A)) :=
  ((s.sigmaSnd (center c F s) (center_boundary c F hF s)).map
    (contractionsAtIso A (center c F s)).hom).app

noncomputable def witness : Contractible A :=
  Contractible.ofContraction (center c F s) (ContractiblePaths.extend (c.reindex (projection A)) (F.reindex (projection A))
    (hF.reindex _) (partialContraction c F hF s))

noncomputable def extend : Term (contr A) := encodeContr (witness c F hF s)
theorem extend_boundary (x : Γ.Elements) (hx : φ.Holds x) :
    (extend c F hF s).val x = s.val x hx := by
  let a := center c F s
  let ha := center_boundary c F hF s
  let e := contractionsAtIso A a
  let p := (s.sigmaSnd a ha).map e.hom
  let t := (ContractiblePaths.extend (c.reindex (projection A)) (F.reindex (projection A)) (hF.reindex _) (partialContraction c F hF s))
  have ht (z : (total A).Elements) (hz : (φ.reindex (projection A)).Holds z) :
      t.val z = p.app.val z hz :=
    ContractiblePaths.extend_boundary (c.reindex (projection A))
      (F.reindex (projection A)) (hF.reindex _) (partialContraction c F hF s) z hz
  have hl : (lam t).val x = p.val x hx := by
    apply PiElement.ext
    intro y f v
    have h := congrArg (fun k => k.val (𝟙 y) v) (p.natural f hx)
    refine (ht (extendObj A y v) (φ.natural f hx)).trans ?_
    change (p.val x hx).val (f ≫ 𝟙 y) v =
      (p.val y (φ.natural f hx)).val (𝟙 y) v at h
    change (p.val y (φ.natural f hx)).val (𝟙 y) v = (p.val x hx).val f v
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
    (c : Contractible A) (F : Filling A) (hF : F.Lawful)
    (σ : Δ ⟶ Γ) (φ : Subcontext Δ) (s : PartialSection (reindex (contr A) σ) φ) :
    Term (reindex (contr A) σ) :=
  Term.map (contrReindexIso A σ).inv
    (ContractibilityExtension.extend (c.reindex σ) (F.reindex σ) (hF.reindex σ)
      (s.map (contrReindexIso A σ).hom))

theorem contrExtend_boundary {Γ Δ : Context.{u}} {A : Family Γ}
    (c : Contractible A) (F : Filling A) (hF : F.Lawful)
    (σ : Δ ⟶ Γ) (φ : Subcontext Δ) (s : PartialSection (reindex (contr A) σ) φ)
    (x : Δ.Elements) (hx : φ.Holds x) : (contrExtend c F hF σ φ s).val x = s.val x hx :=
  (congrArg ((contrReindexIso A σ).inv.app x)
    (ContractibilityExtension.extend_boundary (c.reindex σ) (F.reindex σ) (hF.reindex σ)
      (s.map (contrReindexIso A σ).hom) x hx)).trans
    (congrArg (fun m => m.app x (s.val x hx)) (contrReindexIso A σ).hom_inv_id)

/-- An inhabited native contractibility family is itself contractible. -/
noncomputable def contrContractible {Γ : Context.{u}} {A : Family Γ}
    (c : Contractible A) (F : Filling A) (hF : F.Lawful) :
    Contractible (contr A) :=
  Contractible.ofExtensions (contrExtend c F hF) (contrExtend_boundary c F hF)

namespace IsEquivExtension
variable {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
  (e : HomotopyEquivalence f) (F : Filling A) (hF : F.Lawful)
  (G : Filling B) (hG : G.Lawful)
  {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
  (s : PartialSection (reindex (isEquiv f) σ) φ)

abbrev fiber := Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)

noncomputable def extendedBody : Term (reindex (contr (fiber (f := f))) (liftSub B σ)) :=
  contrExtend e.fibers (genericFiberFilling f F hF G hG)
    (genericFiberFilling_lawful f F hF G hG) (liftSub B σ)
    (φ.reindex (projection (reindex B σ)))
    ((s.map (piReindex B (contr (fiber (f := f))) σ)).app)

noncomputable def extend : Term (reindex (isEquiv f) σ) :=
  Term.map (piReindexIso B (contr (fiber (f := f))) σ).inv
    (lam (extendedBody e F hF G hG σ φ s))

theorem extend_boundary (x : Δ.Elements) (hx : φ.Holds x) :
    (extend e F hF G hG σ φ s).val x = s.val x hx := by
  let i := piReindexIso B (contr (fiber (f := f))) σ
  let p := s.map i.hom
  have h : (lam (extendedBody e F hF G hG σ φ s)).val x = p.val x hx := by
    apply PiElement.ext
    intro y g v
    have hb := contrExtend_boundary e.fibers (genericFiberFilling f F hF G hG)
      (genericFiberFilling_lawful f F hF G hG) (liftSub B σ)
      (φ.reindex (projection (reindex B σ))) p.app
      (extendObj (reindex B σ) y v) (φ.natural g hx)
    have hp := congrArg (fun k => k.val (𝟙 y) v) (p.natural g hx)
    refine hb.trans ?_
    change (p.val x hx).val (g ≫ 𝟙 y) v =
      (p.val y (φ.natural g hx)).val (𝟙 y) v at hp
    change (p.val y (φ.natural g hx)).val (𝟙 y) v = (p.val x hx).val g v
    simpa only [Category.comp_id] using hp.symm
  exact (congrArg (i.inv.app x) h).trans
    (congrArg (fun m => m.app x (s.val x hx)) i.hom_inv_id)
end IsEquivExtension

/-- Native equivalence witnesses form a contractible family whenever inhabited. -/
noncomputable def isEquivContractible {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (e : HomotopyEquivalence f) (F : Filling A) (hF : F.Lawful)
    (G : Filling B) (hG : G.Lawful) : Contractible (isEquiv f) :=
  Contractible.ofExtensions (IsEquivExtension.extend e F hF G hG)
    (IsEquivExtension.extend_boundary e F hF G hG)


noncomputable def contractAt {Γ : Context.{u}} {A : Family Γ}
    (c : Term A)
    (extend : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ),
      PartialSection (Cartesian.reindex A σ) φ → Term (Cartesian.reindex A σ))
    (boundary : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
      (a : PartialSection (Cartesian.reindex A σ) φ) (x : Δ.Elements) (hx : φ.Holds x),
      (extend σ φ a).val x = a.val x hx) : Contractible A := by
  let π := projection A
  let p := projection (interval (total A)) ≫ π
  let φ := (intervalFace (total A) false).join (intervalFace (total A) true)
  let b := endpointBoundary (Cartesian.reindex A p) (Term.reindex c π) (generic A)
  let s := extend p φ b
  have h₀ : Term.reindex s (endpointSub (total A) false) = Term.reindex c π := by
    apply Term.ext
    intro x
    let y := (endpointSub (total A) false).mapElements.obj x
    have hy : (intervalFace (total A) false).Holds y :=
      rfl
    have hu : φ.Holds y := (Subcontext.full_join _ _ y).mpr (Or.inl hy)
    exact (boundary p φ b y hu).trans (eq_of_heq
      ((heq_of_eq (endpointBoundary_zero _ _ _ y hu hy)).trans
        (endpointSection_val (Cartesian.reindex A p) false (Term.reindex c π) y hy)))
  have h₁ : Term.reindex s (endpointSub (total A) true) = generic A := by
    apply Term.ext
    intro x
    let y := (endpointSub (total A) true).mapElements.obj x
    have hy : (intervalFace (total A) true).Holds y :=
      rfl
    have hu : φ.Holds y := (Subcontext.full_join _ _ y).mpr (Or.inr hy)
    exact (boundary p φ b y hu).trans (eq_of_heq
      ((heq_of_eq (endpointBoundary_one _ _ _ y hu hy)).trans
        (endpointSection_val (Cartesian.reindex A p) true (generic A) y hy)))
  exact Contractible.ofContraction c (pathLam s h₀ h₁)


/-- Any two sections of the native equivalence-witness family are joined by a native path. -/
noncomputable def isEquivPath {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (a b : Term (isEquiv f)) : Term (homogeneousPath (isEquiv f) a b) :=
  (contractAt a (IsEquivExtension.extend (decodeIsEquiv a) F hF G hG)
    (IsEquivExtension.extend_boundary (decodeIsEquiv a) F hF G hG)).pathTo b


end EquivalenceFamilies

def sigmaSecondMap {Γ : Context.{u}} (A : Family Γ) {B C : Family (total A)}
    (e : B ⟶ C) : sigma A B ⟶ sigma A C where
  app x := TypeCat.ofHom (fun z => ⟨z.1,e.app (extendObj A x z.1) z.2⟩)
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply congrArg (Sigma.mk (A.map f z.1))
    exact e.naturality_apply (extendHom A f z.1) z.2

def homogeneousPathMap {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)
    {a b : Term A} (p : Term (homogeneousPath A a b)) :
    Term (homogeneousPath B (Term.map f a) (Term.map f b)) :=
  pathLam (Term.map (Functor.whiskerLeft (projection (interval Γ)).mapElements f) (pathApp p))
    (congrArg (Term.map f) (pathApp_zero p)) (congrArg (Term.map f) (pathApp_one p))

noncomputable def Contractible.retract {Γ : Context.{u}} {A B : Family Γ}
    (c : Contractible A) (F : Filling B) (hF : F.Lawful)
    (f : A ⟶ B) (g : B ⟶ A)
    (h : Term (homogeneousPath (Cartesian.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)))
      (generic B))) : Contractible B :=
  Contractible.ofContraction (Term.map f c.center) (homogeneousConcat (F.reindex (projection B)) (hF.reindex _)
    (homogeneousPathMap (Functor.whiskerLeft (projection B).mapElements f)
      ((c.reindex (projection B)).pathTo
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)))) h)

namespace ContractibleTotals
def verticalPath {Γ Δ : Context.{u}} {X : Family Γ} {B : Family (total X)}
    (σ : Δ ⟶ total X) {b₀ b₁ : Term (reindex B σ)}
    (p : Term (homogeneousPath (reindex B σ) b₀ b₁)) :
    Term (homogeneousPath (reindex (sigma X B) (σ ≫ projection X))
      (sigmaIntro (B := reindex B (liftSub X (σ ≫ projection X))) (Term.reindex (generic X) σ) b₀)
      (sigmaIntro (B := reindex B (liftSub X (σ ≫ projection X))) (Term.reindex (generic X) σ) b₁)) :=
  pathLam (sigmaIntro (B := reindex B
      (liftSub X (projection (interval Δ) ≫ σ ≫ projection X)))
    (Term.reindex (Term.reindex (generic X) σ) (projection (interval Δ))) (pathApp p))
    (by
      apply Term.ext
      intro x
      exact congrArg (fun t : Term (reindex B σ) =>
        (sigmaIntro (B := reindex B (liftSub X (σ ≫ projection X)))
          (Term.reindex (generic X) σ) t).val x) (pathApp_zero p))
    (by
      apply Term.ext
      intro x
      exact congrArg (fun t : Term (reindex B σ) =>
        (sigmaIntro (B := reindex B (liftSub X (σ ≫ projection X)))
          (Term.reindex (generic X) σ) t).val x) (pathApp_one p))

end ContractibleTotals
namespace FiberwiseHomotopyRetracts
variable {Γ : Context.{u}} {X : Family Γ} {A B : Family (total X)}

/-- Reassociate a generic total-space point without changing either component. -/
def totalPoint : total (sigma X B) ⟶ total B where
  app _ := TypeCat.ofHom (fun z => ⟨⟨z.1,z.2.1⟩,z.2.2⟩)
  naturality := by intros; rfl

variable (f : A ⟶ B) (g : B ⟶ A)
  (h : Term (homogeneousPath (Cartesian.reindex B (projection B))
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
    (generic B) τ).hom (Term.reindex h τ)
  let q := ContractibleTotals.verticalPath (τ ≫ projection B) p
  exact pathLam (pathApp q) (pathApp_zero q) (pathApp_one q)

end FiberwiseHomotopyRetracts

/-- Contractibility passes along a fiberwise homotopy retract of dependent totals.
The total homotopy is constructed from the supplied fiberwise one. -/
noncomputable def Contractible.fiberwiseRetract
    {Γ : Context.{u}} {X : Family Γ} {A B : Family (total X)}
    (c : Contractible (sigma X A))
    (FX : Filling X) (hFX : FX.Lawful) (FB : Filling B) (hFB : FB.Lawful)
    (f : A ⟶ B) (g : B ⟶ A)
    (h : Term (homogeneousPath (Cartesian.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)))
      (generic B))) : Contractible (sigma X B) :=
  c.retract (sigmaFilling FX hFX FB) (sigmaFilling_lawful FX hFX FB hFB)
    (sigmaSecondMap X f) (sigmaSecondMap X g)
    (FiberwiseHomotopyRetracts.totalHomotopy f g h)



theorem endpointBoundary_map {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (a₀ a₁ : Term A) :
    (endpointBoundary (intervalCoefficient A) a₀ a₁).map
      (Functor.whiskerLeft (projection (interval Γ)).mapElements f) =
      endpointBoundary (intervalCoefficient B) (Term.map f a₀) (Term.map f a₁) := by
  apply PartialSection.ext
  intro x hx
  rcases hx with h₀ | h₁
  · rcases x with @⟨I,γ,r⟩
    change r = ⟨Cube.endpoint I.unop false⟩ at h₀
    subst r
    let z := (endpointSub Γ false).mapElements.obj (Γ.elementsMk I γ)
    exact (congrArg (f.app _) ((endpointBoundary_zero (intervalCoefficient A) a₀ a₁ z _ rfl).trans
      (eq_of_heq (endpointSection_val (intervalCoefficient A) false a₀ z _)))).trans
      ((endpointBoundary_zero (intervalCoefficient B) (Term.map f a₀) (Term.map f a₁) z _ rfl).trans
      (eq_of_heq (endpointSection_val (intervalCoefficient B) false (Term.map f a₀) z _))).symm
  · rcases x with @⟨I,γ,r⟩
    change r = ⟨Cube.endpoint I.unop true⟩ at h₁
    subst r
    let z := (endpointSub Γ true).mapElements.obj (Γ.elementsMk I γ)
    exact (congrArg (f.app _) ((endpointBoundary_one (intervalCoefficient A) a₀ a₁ z _ rfl).trans
      (eq_of_heq (endpointSection_val (intervalCoefficient A) true a₁ z _)))).trans
      ((endpointBoundary_one (intervalCoefficient B) (Term.map f a₀) (Term.map f a₁) z _ rfl).trans
      (eq_of_heq (endpointSection_val (intervalCoefficient B) true (Term.map f a₁) z _))).symm

namespace Contractible
variable {Γ : Context.{u}} {A : Family Γ}
    (extend : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ),
      PartialSection (Cartesian.reindex A σ) φ → Term (Cartesian.reindex A σ))
    (boundary : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
      (a : PartialSection (Cartesian.reindex A σ) φ) (x : Δ.Elements) (hx : φ.Holds x),
      (extend σ φ a).val x = a.val x hx)
    (uniform : ∀ {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
      (a : PartialSection (Cartesian.reindex A σ) φ) (τ : Θ ⟶ Δ),
      extend (τ ≫ σ) (φ.reindex τ) (a.reindex τ) = Term.reindex (extend σ φ a) τ)

include uniform in
theorem ofExtensions_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    (ofExtensions extend boundary).reindex σ =
      ofExtensions (fun ρ φ a => extend (ρ ≫ σ) φ a)
        (fun ρ φ a x hx => boundary (ρ ≫ σ) φ a x hx) := by
  let empty : PartialSection A (Subcontext.bot (Γ := Γ)) := ⟨fun _ h => h.elim, fun _ h => h.elim⟩
  have hc : extend σ Subcontext.bot (empty.reindex σ) = Term.reindex (extend (𝟙 Γ) Subcontext.bot empty) σ :=
    uniform (𝟙 Γ) Subcontext.bot empty σ
  apply Contractible.ext hc.symm
  intro x a y f r
  let π := projection A
  let p := projection (interval (total A)) ≫ π
  let φ := (intervalFace (total A) false).join (intervalFace (total A) true)
  let c := extend (𝟙 Γ) Subcontext.bot empty
  let b := endpointBoundary (Cartesian.reindex A p) (Term.reindex c π) (generic A)
  let τ := liftSub (interval (total A)) (liftSub A σ)
  have hu := uniform p φ b τ
  have hb := endpointBoundary_reindex (Cartesian.reindex A p) (Term.reindex c π) (generic A) (liftSub A σ)
  have hbc : b.reindex τ = endpointBoundary
      (Cartesian.reindex A (projection (interval (total (Cartesian.reindex A σ))) ≫ projection (Cartesian.reindex A σ) ≫ σ))
      (Term.reindex (extend σ Subcontext.bot (empty.reindex σ)) (projection (Cartesian.reindex A σ)))
      (generic (Cartesian.reindex A σ)) := by
    exact hb.trans (congrArg (fun t => endpointBoundary
      (Cartesian.reindex A (projection (interval (total (Cartesian.reindex A σ))) ≫ projection (Cartesian.reindex A σ) ≫ σ))
      t (generic (Cartesian.reindex A σ)))
      (congrArg (fun t => Term.reindex t (projection (Cartesian.reindex A σ))) hc).symm)
  have he := (congrArg (extend (τ ≫ p) (φ.reindex τ)) hbc).symm.trans hu
  exact (congrArg (fun t => t.val (extendObj (interval (total (Cartesian.reindex A σ)))
    (extendObj (Cartesian.reindex A σ) y ((Cartesian.reindex A σ).map f a)) r)) he).symm

include uniform in
theorem ofExtensions_map {B : Family Γ} (e : A ≅ B)
    (extendB : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ),
      PartialSection (Cartesian.reindex B σ) φ → Term (Cartesian.reindex B σ))
    (boundaryB : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
      (a : PartialSection (Cartesian.reindex B σ) φ) (x : Δ.Elements) (hx : φ.Holds x),
      (extendB σ φ a).val x = a.val x hx)
    (commutes : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
      (a : PartialSection (Cartesian.reindex A σ) φ),
      extendB σ φ (a.map (Functor.whiskerLeft σ.mapElements e.hom)) =
        Term.map (Functor.whiskerLeft σ.mapElements e.hom) (extend σ φ a)) :
    Contractible.map e (ofExtensions extend boundary) = ofExtensions extendB boundaryB := by
  let empty : PartialSection A (Subcontext.bot (Γ := Γ)) := ⟨fun _ h => h.elim, fun _ h => h.elim⟩
  let emptyB : PartialSection B (Subcontext.bot (Γ := Γ)) := ⟨fun _ h => h.elim, fun _ h => h.elim⟩
  have hempty : empty.map e.hom = emptyB := by
    apply PartialSection.ext
    intro x hx
    exact hx.elim
  have hc := (congrArg (extendB (𝟙 Γ) Subcontext.bot) hempty).symm.trans
    (commutes (𝟙 Γ) Subcontext.bot empty)
  apply Contractible.ext hc.symm
  intro x a y f r
  let π := projection A
  let p := projection (interval (total A)) ≫ π
  let φ := (intervalFace (total A) false).join (intervalFace (total A) true)
  let c := extend (𝟙 Γ) Subcontext.bot empty
  let b := endpointBoundary (Cartesian.reindex A p) (Term.reindex c π) (generic A)
  let τ₀ := pair (projection B) (Term.map (Functor.whiskerLeft (projection B).mapElements e.inv) (generic B))
  let τ := liftSub (interval (total A)) τ₀
  let pB := projection (interval (total B)) ≫ projection B
  have hu := uniform p φ b τ
  have hb := endpointBoundary_reindex (Cartesian.reindex A p) (Term.reindex c π) (generic A) τ₀
  have hm := endpointBoundary_map (Functor.whiskerLeft (projection B).mapElements e.hom)
    (Term.reindex c (projection B)) (Term.map (Functor.whiskerLeft (projection B).mapElements e.inv) (generic B))
  have hbc : (b.reindex τ).map (Functor.whiskerLeft pB.mapElements e.hom) =
      endpointBoundary (Cartesian.reindex B pB)
        (Term.reindex (extendB (𝟙 Γ) Subcontext.bot emptyB) (projection B)) (generic B) := by
    refine (congrArg (fun s => s.map (Functor.whiskerLeft pB.mapElements e.hom)) hb).trans (hm.trans ?_)
    have hround : Term.map (Functor.whiskerLeft (projection B).mapElements e.hom)
        (Term.map (Functor.whiskerLeft (projection B).mapElements e.inv) (generic B)) = generic B :=
      Term.map_iso_roundtrip (Functor.isoWhiskerLeft (projection B).mapElements e).symm _
    exact congrArg₂ (endpointBoundary (Cartesian.reindex B pB))
      (congrArg (fun t => Term.reindex t (projection B)) hc).symm hround
  have he := (congrArg (extendB pB (φ.reindex τ)) hbc).symm.trans
    ((commutes pB (φ.reindex τ) (b.reindex τ)).trans
      (congrArg (Term.map (Functor.whiskerLeft pB.mapElements e.hom)) hu))
  have hev := congrArg (fun t => t.val (extendObj (interval (total B))
    (extendObj B y (B.map f a)) r)) he
  change (extendB pB (φ.reindex τ)
    (endpointBoundary (Cartesian.reindex B pB) (Term.reindex (extendB (𝟙 Γ) Subcontext.bot emptyB) (projection B)) (generic B))).val
    (extendObj (interval (total B)) (extendObj B y (B.map f a)) r) =
    e.hom.app y ((extend p φ b).val (extendObj (interval (total A))
      (extendObj A y (e.inv.app y (B.map f a))) r)) at hev
  change e.hom.app y ((extend p φ b).val (extendObj (interval (total A))
    (extendObj A y (A.map f (e.inv.app x a))) r)) = _
  exact (congrArg (fun q => e.hom.app y ((extend p φ b).val
    (extendObj (interval (total A)) (extendObj A y q) r)))
    (e.inv.naturality_apply f a).symm).trans hev.symm

end Contractible

end SquareKit.Cubical.Cartesian
