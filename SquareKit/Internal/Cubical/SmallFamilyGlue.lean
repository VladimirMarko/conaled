import SquareKit.Internal.Cubical.GlueFillingSubstitution
import SquareKit.Internal.Cubical.SmallFamilyClassification

/-! Glue on small lawful families retains the supplied whole filling data. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u


private theorem family_eq_of_iso_heq {Γ : Context.{u}} {A B : Family Γ} (i : A ≅ B)
    (ho : ∀ x, A.obj x = B.obj x)
    (hi : ∀ x (a : A.obj x), HEq (i.hom.app x a) a) : A = B := by
  apply Functor.hext ho
  intro x y f
  apply typeHom_hext (ho x) (ho y)
  intro a b hab
  have hx : i.hom.app x a = b := eq_of_heq ((hi x a).trans hab)
  have hn := ConcreteCategory.congr_hom (i.hom.naturality f) a
  exact (hi y (A.map f a)).symm.trans
    (heq_of_eq (hn.trans (congrArg (fun z => B.map f z) hx)))

namespace LocalFamily


/-- Decoding a native code recovers its family by equality of the indexed types. -/
theorem decodeCode_family_eq {Γ : Context.{u}} (A : LocalFamily Γ) : decode A.code = A.family :=
  family_eq_of_iso_heq A.decodeCodeIso
    (fun x => congrArg A.family.obj (represented_generic_source x)) A.decodeCodeIso_hom_heq

theorem decodeCodeIso_eq {Γ : Context.{u}} (A : LocalFamily Γ) :
    A.decodeCodeIso = eqToIso A.decodeCode_family_eq := by
  apply Iso.ext
  ext x a
  exact eq_of_heq ((A.decodeCodeIso_hom_heq x a).trans
    (family_eqToIso_hom_heq A.decodeCode_family_eq x a).symm)


private theorem eq_of_local_operations {Γ : Context.{u}} (A B : LocalFamily Γ)
    (h : A.family = B.family)
    (hf : ∀ {I : Cube} (p : total (interval (representable.{u} I)) ⟶ Γ)
      (φ : Cofibration (representable.{u} I)) (b : OpenBox (Presheaf.reindex A.family p) φ),
      B.filling.fill p φ (b.map (Functor.whiskerLeft p.mapElements (eqToIso h).hom)) =
        Term.map (Functor.whiskerLeft p.mapElements (eqToIso h).hom) (A.filling.fill p φ b)) : A = B := by
  cases A with
  | mk family filling lawful =>
    cases B with
    | mk family' filling' lawful' =>
      dsimp at h
      subst family'
      have he : filling = filling' := by
        cases filling with
        | mk fill =>
          cases filling' with
          | mk fill' =>
            congr 1
            funext I p φ b
            exact (hf p φ b).symm
      cases he
      rfl

/-- Recovery includes the selected local operation, not just the underlying family. -/
theorem decoded_code {Γ : Context.{u}} (A : LocalFamily Γ) : decodedLocalFamily A.code = A := by
  apply eq_of_local_operations _ _ A.decodeCode_family_eq
  intro I p φ b
  have h := A.decodeCode_filling p φ b
  exact (congrArg (fun i : decode A.code ≅ A.family =>
    A.filling.fill p φ (b.map (Functor.whiskerLeft p.mapElements i.hom))) A.decodeCodeIso_eq).symm.trans
      (h.trans (congrArg (fun i : decode A.code ≅ A.family =>
        Term.map (Functor.whiskerLeft p.mapElements i.hom) ((decodedLocalFilling A.code).fill p φ b))
          A.decodeCodeIso_eq))

/-- Native extension and restriction retain the chosen local filling operation. -/
theorem ofNative_toNative {Γ : Context.{u}} (A : LocalFamily Γ) :
    ofNative A.toNative = A := by
  cases A with
  | mk family filling lawful =>
    change LocalFamily.mk family _ _ = LocalFamily.mk family filling lawful
    congr 1
    exact filling.toFilling_toLocal lawful

/-- Equality of fibers and of the transported whole filler identifies a code. -/
theorem eq_of_filling {Γ : Context.{u}} (A B : LocalFamily Γ)
    (h : A.family = B.family)
    (hf : A.toNative.filling.transport (eqToIso h) = B.toNative.filling) : A = B := by
  cases A with
  | mk family filling lawful =>
    cases B with
    | mk family' filling' lawful' =>
      dsimp at h
      subst family'
      have hlocal := congrArg Filling.toLocal hf
      change (filling.toFilling lawful).toLocal = (filling'.toFilling lawful').toLocal at hlocal
      rw [LocalFilling.toFilling_toLocal, LocalFilling.toFilling_toLocal] at hlocal
      cases hlocal
      rfl

noncomputable def glue {Γ : Context.{u}} (φ : Cofibration Γ)
    (A : LocalFamily Γ) (T : LocalFamily (restrictContext φ))
    (e : T.family ⟶ Presheaf.reindex A.family (restrictInclusion φ)) (E : HomotopyEquivalence e) :
    LocalFamily Γ :=
  ofNative ⟨⟨Glue.family φ A.family T.family e,
    Glue.filling φ A.family T.family e E T.toNative.filling T.toNative.lawful
      A.toNative.filling A.toNative.lawful⟩,
    Glue.filling_lawful φ A.family T.family e E T.toNative.filling T.toNative.lawful
      A.toNative.filling A.toNative.lawful⟩

theorem glue_native_filling {Γ : Context.{u}} (φ : Cofibration Γ)
    (A : LocalFamily Γ) (T : LocalFamily (restrictContext φ))
    (e : T.family ⟶ Presheaf.reindex A.family (restrictInclusion φ)) (E : HomotopyEquivalence e) :
    (glue φ A T e E).toNative.filling =
      Glue.filling φ A.family T.family e E T.toNative.filling T.toNative.lawful
        A.toNative.filling A.toNative.lawful :=
  Filling.toLocal_toFilling _ (Glue.filling_lawful φ A.family T.family e E
    T.toNative.filling T.toNative.lawful A.toNative.filling A.toNative.lawful)

theorem glue_full {Γ : Context.{u}} (φ : Cofibration Γ)
    (A : LocalFamily Γ) (T : LocalFamily (restrictContext φ))
    (e : T.family ⟶ Presheaf.reindex A.family (restrictInclusion φ)) (E : HomotopyEquivalence e) :
    (glue φ A T e E).reindex (restrictInclusion φ) = T := by
  apply eq_of_filling _ _ (Glue.family_full φ A.family T.family e)
  have h := congrArg (fun F => (F.reindex (restrictInclusion φ)).transport
    (eqToIso (Glue.family_full φ A.family T.family e))) (glue_native_filling φ A T e E)
  exact h.trans (Glue.filling_full φ A.family T.family e E T.toNative.filling T.toNative.lawful
    A.toNative.filling A.toNative.lawful)


/-- Coding a decoded contextual family recovers the original codes, including fillers. -/
theorem code_decoded {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) :
    (decodedLocalFamily a).code = a := by
  ext I x
  exact (decoded_represented_family a (Γ.elementsMk I x.down)).trans
    (LocalFamily.decoded_code (a.app I x))

end LocalFamily
namespace Glue

/-- Data to be localized before selecting a small Glue carrier. -/
structure Datum (Γ : Context.{u}) where
  face : Cofibration Γ
  ambient : Family Γ
  faceFamily : Family (restrictContext face)
  map : faceFamily ⟶ Presheaf.reindex ambient (restrictInclusion face)

def Datum.reindex {Γ Δ : Context.{u}} (D : Datum Γ) (σ : Δ ⟶ Γ) : Datum Δ where
  face := D.face.reindex σ
  ambient := Presheaf.reindex D.ambient σ
  faceFamily := Presheaf.reindex D.faceFamily (restrictSubstitution D.face σ)
  map := Functor.whiskerLeft (restrictSubstitution D.face σ).mapElements D.map

theorem Datum.reindex_comp {Γ Δ Θ : Context.{u}} (D : Datum Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) : (D.reindex σ).reindex τ = D.reindex (τ ≫ σ) := rfl

def Datum.compatible {Γ : Context.{u}} (D : Datum Γ) : Family Γ :=
  compatibleFamily D.face D.ambient D.faceFamily D.map

/-- Localization uses only the represented cube as its indexing context. -/
def Datum.local {Γ : Context.{u}} (D : Datum Γ) (x : Γ.Elements) : Datum (representable.{u} x.obj.unop) :=
  D.reindex (represented x)

theorem Datum.local_substitution {Γ Δ : Context.{u}} (D : Datum Γ)
    (σ : Δ ⟶ Γ) (x : Δ.Elements) : (D.reindex σ).local x = D.local (σ.mapElements.obj x) :=
  congrArg D.reindex (represented_naturality σ x).symm

def Datum.localCarrier {Γ : Context.{u}} (D : Datum Γ) (x : Γ.Elements) : Type u :=
  (D.local x).compatible.obj (representableGeneric.{u} x.obj.unop)

theorem Datum.localCarrier_substitution {Γ Δ : Context.{u}} (D : Datum Γ)
    (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    (D.reindex σ).localCarrier x = D.localCarrier (σ.mapElements.obj x) :=
  congrArg (fun L => L.compatible.obj (representableGeneric.{u} x.obj.unop))
    (D.local_substitution σ x)

def Datum.localCarrierEquiv {Γ : Context.{u}} (D : Datum Γ) (x : Γ.Elements) :
    D.localCarrier x ≃ D.compatible.obj x :=
  (((compatibleReindexIso D.face D.ambient D.faceFamily D.map (represented x)).app
    (representableGeneric.{u} x.obj.unop)).symm.toEquiv).trans
      (D.compatible.mapIso (eqToIso (represented_generic_source x))).toEquiv

/-- Full faces retain the given carrier; other cubes use a local presentation. -/
def Datum.smallFiber {Γ : Context.{u}} (D : Datum Γ) (x : Γ.Elements) : Type u :=
  if h : D.face.full x then D.faceFamily.obj (faceObj D.face x h) else D.localCarrier x

def Datum.smallFiberEquiv {Γ : Context.{u}} (D : Datum Γ) (x : Γ.Elements) :
    D.smallFiber x ≃ D.compatible.obj x :=
  if h : D.face.full x then
    (Equiv.cast (show D.smallFiber x = D.faceFamily.obj (faceObj D.face x h) from dite_eq_left h)).trans
      (fullFaceEquiv D.face D.ambient D.faceFamily D.map h)
  else
    (Equiv.cast (show D.smallFiber x = D.localCarrier x from dite_eq_right h)).trans
      (D.localCarrierEquiv x)

theorem Datum.smallFiber_substitution {Γ Δ : Context.{u}} (D : Datum Γ)
    (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    (D.reindex σ).smallFiber x = D.smallFiber (σ.mapElements.obj x) := by
  unfold smallFiber
  change (if h : D.face.full (σ.mapElements.obj x) then
    D.faceFamily.obj (faceObj D.face (σ.mapElements.obj x) h) else (D.reindex σ).localCarrier x) = _
  by_cases h : D.face.full (σ.mapElements.obj x)
  · rw [dite_eq_left h, dite_eq_left h]
  · rw [dite_eq_right h, dite_eq_right h]
    exact D.localCarrier_substitution σ x

def Datum.smallFamily {Γ : Context.{u}} (D : Datum Γ) : Family Γ :=
  D.compatible.copyObj D.smallFiber (fun x => (D.smallFiberEquiv x).symm.toIso)

def Datum.smallFamilyIso {Γ : Context.{u}} (D : Datum Γ) : D.smallFamily ≅ D.compatible :=
  (D.compatible.isoCopyObj D.smallFiber (fun x => (D.smallFiberEquiv x).symm.toIso)).symm

def Datum.chartMap {Γ : Context.{u}} (D : Datum Γ) {I : Cube}
    (q : representable.{u} I ⟶ Γ) (x : Γ.Elements)
    (hx : q.mapElements.obj (representableGeneric.{u} I) = x) :
    D.compatible.obj x → (D.reindex q).compatible.obj (representableGeneric.{u} I) :=
  fun s => (compatibleReindexMap D.face D.ambient D.faceFamily D.map q).app _
    (D.compatible.map (eqToHom hx.symm) s)

theorem Datum.chartMap_substitution {Γ Δ : Context.{u}} (D : Datum Γ)
    (σ : Δ ⟶ Γ) {I : Cube} (q : representable.{u} I ⟶ Δ) (x : Δ.Elements)
    (hx : q.mapElements.obj (representableGeneric.{u} I) = x)
    (s : D.compatible.obj (σ.mapElements.obj x)) :
    (D.reindex σ).chartMap q x hx
      ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x s) =
    D.chartMap (q ≫ σ) (σ.mapElements.obj x) (congrArg σ.mapElements.obj hx) s := by
  subst x
  unfold chartMap
  simp only [eqToHom_refl]
  rfl

theorem Datum.chartMap_congr {Γ : Context.{u}} (D : Datum Γ) {I : Cube}
    (q r : representable.{u} I ⟶ Γ) (h : q = r) (x : Γ.Elements)
    (hq : q.mapElements.obj (representableGeneric.{u} I) = x)
    (hr : r.mapElements.obj (representableGeneric.{u} I) = x) (s : D.compatible.obj x) :
    HEq (D.chartMap q x hq s) (D.chartMap r x hr s) := by
  subst r
  rfl

theorem Datum.localCarrierEquiv_symm {Γ : Context.{u}} (D : Datum Γ) (x : Γ.Elements)
    (s : D.compatible.obj x) :
    (D.localCarrierEquiv x).symm s = D.chartMap (represented x) x (represented_generic_source x) s := rfl

theorem Datum.toLocal_substitution {Γ Δ : Context.{u}} (D : Datum Γ)
    (σ : Δ ⟶ Γ) (x : Δ.Elements) (s : D.compatible.obj (σ.mapElements.obj x)) :
    HEq ((D.localCarrierEquiv (σ.mapElements.obj x)).symm s)
      (((D.reindex σ).localCarrierEquiv x).symm
        ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x s)) := by
  exact (D.chartMap_congr _ _ (represented_naturality σ x)
    (σ.mapElements.obj x) (represented_generic_source (σ.mapElements.obj x))
    (congrArg σ.mapElements.obj (represented_generic_source x)) s).trans
      (heq_of_eq (D.chartMap_substitution σ (represented x) x (represented_generic_source x) s).symm)

theorem Datum.smallToLocal_substitution {Γ Δ : Context.{u}} (D : Datum Γ)
    (σ : Δ ⟶ Γ) (x : Δ.Elements) (s : D.compatible.obj (σ.mapElements.obj x)) :
    HEq ((D.smallFiberEquiv (σ.mapElements.obj x)).symm s)
      (((D.reindex σ).smallFiberEquiv x).symm
        ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x s)) := by
  by_cases h : D.face.full (σ.mapElements.obj x)
  · have h' : (D.reindex σ).face.full x := h
    simp only [smallFiberEquiv, dite_eq_left h, dite_eq_left h']
    exact (cast_heq _ _).trans (cast_heq _ _).symm
  · have h' : ¬(D.reindex σ).face.full x := h
    simp only [smallFiberEquiv, dite_eq_right h, dite_eq_right h']
    exact (cast_heq _ _).trans ((D.toLocal_substitution σ x s).trans (cast_heq _ _).symm)

theorem Datum.smallFamily_substitution {Γ Δ : Context.{u}} (D : Datum Γ) (σ : Δ ⟶ Γ) :
    Presheaf.reindex D.smallFamily σ = (D.reindex σ).smallFamily := by
  have ho : ∀ x, (Presheaf.reindex D.smallFamily σ).obj x = (D.reindex σ).smallFamily.obj x :=
    fun x => (D.smallFiber_substitution σ x).symm
  apply Functor.hext ho
  intro x y f
  apply typeHom_hext (ho x) (ho y)
  intro s t hst
  have ht : t = ((D.reindex σ).smallFiberEquiv x).symm
      ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x
        (D.smallFiberEquiv (σ.mapElements.obj x) s)) :=
    eq_of_heq (hst.symm.trans
      ((heq_of_eq ((D.smallFiberEquiv (σ.mapElements.obj x)).symm_apply_apply s)).symm.trans
        (D.smallToLocal_substitution σ x (D.smallFiberEquiv (σ.mapElements.obj x) s))))
  subst t
  change HEq ((D.smallFiberEquiv (σ.mapElements.obj y)).symm
    (D.compatible.map (σ.mapElements.map f) (D.smallFiberEquiv (σ.mapElements.obj x) s)))
    (((D.reindex σ).smallFiberEquiv y).symm
      ((D.reindex σ).compatible.map f (((D.reindex σ).smallFiberEquiv x)
        (((D.reindex σ).smallFiberEquiv x).symm
          ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x
            (D.smallFiberEquiv (σ.mapElements.obj x) s))))))
  exact (D.smallToLocal_substitution σ y
    (D.compatible.map (σ.mapElements.map f) (D.smallFiberEquiv (σ.mapElements.obj x) s))).trans
      (heq_of_eq (congrArg (fun a => ((D.reindex σ).smallFiberEquiv y).symm
        ((D.reindex σ).compatible.map f a))
          (((D.reindex σ).smallFiberEquiv x).apply_symm_apply
            ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x
              (D.smallFiberEquiv (σ.mapElements.obj x) s)))).symm)

theorem Datum.smallFiberEquiv_full {Γ : Context.{u}} (D : Datum Γ) {x : Γ.Elements}
    (h : D.face.full x) (a : D.smallFiber x) (t : D.faceFamily.obj (faceObj D.face x h))
    (ha : HEq a t) : D.smallFiberEquiv x a = fromFace D.face D.ambient D.faceFamily D.map h t := by
  simp only [smallFiberEquiv, dite_eq_left h]
  apply congrArg (fromFace D.face D.ambient D.faceFamily D.map h)
  exact eq_of_heq ((cast_heq _ a).trans ha)

theorem Datum.smallFiberEquiv_symm_full {Γ : Context.{u}} (D : Datum Γ) {x : Γ.Elements}
    (h : D.face.full x) (s : D.compatible.obj x) :
    HEq ((D.smallFiberEquiv x).symm s) (s.face (𝟙 x) h) := by
  simp only [smallFiberEquiv, dite_eq_left h]
  exact cast_heq _ _

theorem Datum.smallFamily_full {Γ : Context.{u}} (D : Datum Γ) :
    Presheaf.reindex D.smallFamily (restrictInclusion D.face) = D.faceFamily := by
  have ho : ∀ x, (Presheaf.reindex D.smallFamily (restrictInclusion D.face)).obj x = D.faceFamily.obj x :=
    fun x => dite_eq_left x.val.property
  apply Functor.hext ho
  intro x y f
  apply typeHom_hext (ho x) (ho y)
  intro a t hat
  let q := (restrictInclusion D.face).mapElements.map f
  have hx := D.smallFiberEquiv_full x.val.property a t hat
  have hy := D.smallFiberEquiv_symm_full y.val.property
    (D.compatible.map q (D.smallFiberEquiv _ a))
  apply hy.trans
  apply heq_of_eq
  change (D.smallFiberEquiv _ a).face (q ≫ 𝟙 _) y.val.property = D.faceFamily.map f t
  exact (congrArg (fun z : D.compatible.obj ((restrictInclusion D.face).mapElements.obj x) =>
    z.face (q ≫ 𝟙 _) y.val.property) hx).trans
      (congrArg (fun k => D.faceFamily.map k t) (by apply Functor.Elements.hom_ext; exact Category.comp_id _))

def Datum.nativeIso {Γ : Context.{u}} (D : Datum Γ) :
    family D.face D.ambient D.faceFamily D.map ≅ D.smallFamily :=
  familyIso D.face D.ambient D.faceFamily D.map ≪≫ D.smallFamilyIso.symm


theorem Datum.nativeIso_substitution {Γ Δ : Context.{u}} (D : Datum Γ) (σ : Δ ⟶ Γ) :
    (Functor.isoWhiskerLeft σ.mapElements D.nativeIso) ≪≫ eqToIso (D.smallFamily_substitution σ) =
      reindexIso D.face D.ambient D.faceFamily D.map σ ≪≫ (D.reindex σ).nativeIso := by
  apply Iso.ext
  ext x z
  have hnew := congrArg (fun m => m.app x
    ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x
      ((familyIso D.face D.ambient D.faceFamily D.map).hom.app (σ.mapElements.obj x) z)))
    (familyIso (D.face.reindex σ) (Presheaf.reindex D.ambient σ)
      (Presheaf.reindex D.faceFamily (restrictSubstitution D.face σ))
      (Functor.whiskerLeft (restrictSubstitution D.face σ).mapElements D.map)).inv_hom_id
  exact eq_of_heq ((family_eqToIso_hom_heq (D.smallFamily_substitution σ) x _).trans
    ((D.smallToLocal_substitution σ x ((familyIso D.face D.ambient D.faceFamily D.map).hom.app
      (σ.mapElements.obj x) z)).trans
        (heq_of_eq (congrArg ((D.reindex σ).smallFiberEquiv x).symm hnew).symm)))

noncomputable def Datum.smallFilling {Γ : Context.{u}} (D : Datum Γ)
    (E : HomotopyEquivalence D.map) (F : Filling D.faceFamily) (hF : F.Lawful)
    (G : Filling D.ambient) (hG : G.Lawful) : Filling D.smallFamily :=
  (filling D.face D.ambient D.faceFamily D.map E F hF G hG).transport D.nativeIso

theorem Datum.smallFilling_lawful {Γ : Context.{u}} (D : Datum Γ)
    (E : HomotopyEquivalence D.map) (F : Filling D.faceFamily) (hF : F.Lawful)
    (G : Filling D.ambient) (hG : G.Lawful) : (D.smallFilling E F hF G hG).Lawful :=
  Filling.transport_lawful _ _ (filling_lawful D.face D.ambient D.faceFamily D.map E F hF G hG)


theorem Datum.smallFilling_substitution {Γ Δ : Context.{u}} (D : Datum Γ)
    (E : HomotopyEquivalence D.map) (F : Filling D.faceFamily) (hF : F.Lawful)
    (G : Filling D.ambient) (hG : G.Lawful) (σ : Δ ⟶ Γ) :
    ((D.smallFilling E F hF G hG).reindex σ).transport (eqToIso (D.smallFamily_substitution σ)) =
      (D.reindex σ).smallFilling (E.reindex (restrictSubstitution D.face σ))
        (F.reindex (restrictSubstitution D.face σ)) (hF.reindex _) (G.reindex σ) (hG.reindex _) := by
  let H := filling D.face D.ambient D.faceFamily D.map E F hF G hG
  exact (congrArg (fun i => (H.reindex σ).transport i) (D.nativeIso_substitution σ)).trans
    (congrArg (fun K => K.transport (D.reindex σ).nativeIso)
      (filling_reindex_iso D.face D.ambient D.faceFamily D.map σ E F hF G hG))

theorem Datum.nativeIso_full {Γ : Context.{u}} (D : Datum Γ) :
    (Functor.isoWhiskerLeft (restrictInclusion D.face).mapElements D.nativeIso) ≪≫
      eqToIso D.smallFamily_full = eqToIso (family_full D.face D.ambient D.faceFamily D.map) := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro a
  have hc : ∀ {B C : Family (restrictContext D.face)} (h : B = C) (z : B.obj x),
      HEq ((eqToHom h).app x z) z := by
    intro B C h z
    cases h
    rfl
  let t := (eqToHom (family_full D.face D.ambient D.faceFamily D.map)).app x a
  have ha : HEq a t := (hc _ a).symm
  have hf := fiberEquiv_full D.face D.ambient D.faceFamily D.map x.val.property a t ha
  have hr := congrArg (fun z : D.compatible.obj ((restrictInclusion D.face).mapElements.obj x) =>
    z.face (𝟙 _) x.val.property) hf
  exact eq_of_heq ((hc D.smallFamily_full _).trans
    ((D.smallFiberEquiv_symm_full x.val.property
      (fiberEquiv D.face D.ambient D.faceFamily D.map _ a)).trans
        (heq_of_eq (hr.trans (fromFace_read D.face D.ambient D.faceFamily D.map x.val.property t)))))

theorem Datum.smallFilling_full {Γ : Context.{u}} (D : Datum Γ)
    (E : HomotopyEquivalence D.map) (F : Filling D.faceFamily) (hF : F.Lawful)
    (G : Filling D.ambient) (hG : G.Lawful) :
    ((D.smallFilling E F hF G hG).reindex (restrictInclusion D.face)).transport
      (eqToIso D.smallFamily_full) = F := by
  let H := filling D.face D.ambient D.faceFamily D.map E F hF G hG
  exact (congrArg (fun i => (H.reindex (restrictInclusion D.face)).transport i)
    D.nativeIso_full).trans (filling_full D.face D.ambient D.faceFamily D.map E F hF G hG)


noncomputable def Datum.smallLocalFamily {Γ : Context.{u}} (D : Datum Γ)
    (E : HomotopyEquivalence D.map) (F : Filling D.faceFamily) (hF : F.Lawful)
    (G : Filling D.ambient) (hG : G.Lawful) : LocalFamily Γ :=
  LocalFamily.ofNative ⟨⟨D.smallFamily,D.smallFilling E F hF G hG⟩,D.smallFilling_lawful E F hF G hG⟩

theorem Datum.smallLocalFamily_native {Γ Δ : Context.{u}} (D : Datum Γ)
    (E : HomotopyEquivalence D.map) (F : Filling D.faceFamily) (hF : F.Lawful)
    (G : Filling D.ambient) (hG : G.Lawful) (σ : Δ ⟶ Γ) :
    ((D.smallLocalFamily E F hF G hG).reindex σ).toNative.filling =
      (D.smallFilling E F hF G hG).reindex σ :=
  Filling.toLocal_toFilling _ ((D.smallFilling_lawful E F hF G hG).reindex σ)

theorem Datum.smallLocalFamily_substitution {Γ Δ : Context.{u}} (D : Datum Γ)
    (E : HomotopyEquivalence D.map) (F : Filling D.faceFamily) (hF : F.Lawful)
    (G : Filling D.ambient) (hG : G.Lawful) (σ : Δ ⟶ Γ) :
    (D.smallLocalFamily E F hF G hG).reindex σ =
      (D.reindex σ).smallLocalFamily (E.reindex (restrictSubstitution D.face σ))
        (F.reindex (restrictSubstitution D.face σ)) (hF.reindex _) (G.reindex σ) (hG.reindex _) := by
  apply LocalFamily.eq_of_filling _ _ (D.smallFamily_substitution σ)
  exact (congrArg (fun H => H.transport (eqToIso (D.smallFamily_substitution σ)))
    (D.smallLocalFamily_native E F hF G hG σ)).trans
      ((D.smallFilling_substitution E F hF G hG σ).trans
        ((D.reindex σ).smallLocalFamily_native (E.reindex (restrictSubstitution D.face σ))
          (F.reindex (restrictSubstitution D.face σ)) (hF.reindex _) (G.reindex σ) (hG.reindex _) (𝟙 _)).symm)

theorem Datum.smallLocalFamily_full {Γ : Context.{u}} (D : Datum Γ)
    (E : HomotopyEquivalence D.map) (F : Filling D.faceFamily) (hF : F.Lawful)
    (G : Filling D.ambient) (hG : G.Lawful) :
    (D.smallLocalFamily E F hF G hG).reindex (restrictInclusion D.face) =
      LocalFamily.ofNative ⟨⟨D.faceFamily,F⟩,hF⟩ := by
  apply LocalFamily.eq_of_filling _ _ D.smallFamily_full
  exact (congrArg (fun H => H.transport (eqToIso D.smallFamily_full))
    (D.smallLocalFamily_native E F hF G hG (restrictInclusion D.face))).trans
      ((D.smallFilling_full E F hF G hG).trans (Filling.toLocal_toFilling F hF).symm)

end Glue

namespace LocalFamily

noncomputable def normalizedGlue {Γ : Context.{u}} (φ : Cofibration Γ)
    (A : LocalFamily Γ) (T : LocalFamily (restrictContext φ))
    (e : T.family ⟶ Presheaf.reindex A.family (restrictInclusion φ)) (E : HomotopyEquivalence e) :
    LocalFamily Γ :=
  (Glue.Datum.mk φ A.family T.family e).smallLocalFamily E
    T.toNative.filling T.toNative.lawful A.toNative.filling A.toNative.lawful

theorem normalizedGlue_full {Γ : Context.{u}} (φ : Cofibration Γ)
    (A : LocalFamily Γ) (T : LocalFamily (restrictContext φ))
    (e : T.family ⟶ Presheaf.reindex A.family (restrictInclusion φ)) (E : HomotopyEquivalence e) :
    (normalizedGlue φ A T e E).reindex (restrictInclusion φ) = T :=
  ((Glue.Datum.mk φ A.family T.family e).smallLocalFamily_full E
    T.toNative.filling T.toNative.lawful A.toNative.filling A.toNative.lawful).trans T.ofNative_toNative

theorem normalizedGlue_substitution {Γ Δ : Context.{u}} (φ : Cofibration Γ)
    (A : LocalFamily Γ) (T : LocalFamily (restrictContext φ))
    (e : T.family ⟶ Presheaf.reindex A.family (restrictInclusion φ)) (E : HomotopyEquivalence e)
    (σ : Δ ⟶ Γ) :
    (normalizedGlue φ A T e E).reindex σ = normalizedGlue (φ.reindex σ) (A.reindex σ)
      (T.reindex (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) (E.reindex (restrictSubstitution φ σ)) :=
  (Glue.Datum.mk φ A.family T.family e).smallLocalFamily_substitution E
    T.toNative.filling T.toNative.lawful A.toNative.filling A.toNative.lawful σ

end LocalFamily

namespace Glue

/-- A small universe code retaining the whole selected Glue filling. -/
noncomputable def localCode {Γ : Context.{u}} (φ : Cofibration Γ)
    (A : LocalFamily Γ) (T : LocalFamily (restrictContext φ))
    (e : T.family ⟶ reindex A.family (restrictInclusion φ)) (E : HomotopyEquivalence e) :
    raisedContext Γ ⟶ smallFamilyCodes.{u} := (LocalFamily.normalizedGlue φ A T e E).code

theorem localCode_full {Γ : Context.{u}} (φ : Cofibration Γ)
    (A : LocalFamily Γ) (T : LocalFamily (restrictContext φ))
    (e : T.family ⟶ reindex A.family (restrictInclusion φ)) (E : HomotopyEquivalence e) :
    raisedSub (restrictInclusion φ) ≫ localCode φ A T e E = T.code :=
  ((LocalFamily.normalizedGlue φ A T e E).code_reindex (restrictInclusion φ)).symm.trans
    (congrArg LocalFamily.code (LocalFamily.normalizedGlue_full φ A T e E))

theorem localCode_substitution {Γ Δ : Context.{u}} (φ : Cofibration Γ)
    (A : LocalFamily Γ) (T : LocalFamily (restrictContext φ))
    (e : T.family ⟶ reindex A.family (restrictInclusion φ)) (E : HomotopyEquivalence e) (σ : Δ ⟶ Γ) :
    raisedSub σ ≫ localCode φ A T e E = localCode (φ.reindex σ) (A.reindex σ)
      (T.reindex (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) (E.reindex (restrictSubstitution φ σ)) :=
  ((LocalFamily.normalizedGlue φ A T e E).code_reindex σ).symm.trans
    (congrArg LocalFamily.code (LocalFamily.normalizedGlue_substitution φ A T e E σ))

/-- Glue applied to supplied universe maps has their exact original boundary code. -/
noncomputable def code {Γ : Context.{u}} (φ : Cofibration Γ)
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (t : raisedContext (restrictContext φ) ⟶ smallFamilyCodes.{u})
    (e : decode t ⟶ reindex (decode a) (restrictInclusion φ)) (E : HomotopyEquivalence e) :
    raisedContext Γ ⟶ smallFamilyCodes.{u} :=
  localCode φ (decodedLocalFamily a) (decodedLocalFamily t) e E

theorem code_full {Γ : Context.{u}} (φ : Cofibration Γ)
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (t : raisedContext (restrictContext φ) ⟶ smallFamilyCodes.{u})
    (e : decode t ⟶ reindex (decode a) (restrictInclusion φ)) (E : HomotopyEquivalence e) :
    raisedSub (restrictInclusion φ) ≫ code φ a t e E = t :=
  (localCode_full φ (decodedLocalFamily a) (decodedLocalFamily t) e E).trans (LocalFamily.code_decoded t)

end Glue

end SquareKit.Cubical.Presheaf
