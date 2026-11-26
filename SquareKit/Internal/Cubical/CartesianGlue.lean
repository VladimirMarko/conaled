import SquareKit.Internal.Cubical.CartesianDependentFamilies
import SquareKit.Internal.Cubical.CartesianLocalFillingBridge
import SquareKit.Internal.Cubical.CartesianSubstitution

/-! Compatible ambient and face data for Glue. The compatibility presentation
is kept separate from its full-face strictification and selected filling. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Glue
variable {Γ : Context.{u}} (φ : Subcontext Γ)

def faceObj (x : Γ.Elements) (h : φ.Holds x) : (restrictContext φ).Elements :=
  (restrictContext φ).elementsMk x.obj ⟨x.val,h⟩

def faceHom {x y : Γ.Elements} (f : x ⟶ y) (h : φ.Holds x) :
    faceObj φ x h ⟶ faceObj φ y (φ.natural f h) :=
  Functor.Elements.homMk f.hom (Subtype.ext f.map_val)

variable (A : Family Γ) (T : Family (restrictContext φ))
  (e : T ⟶ reindex A (restrictInclusion φ))

/-- Face data is coherent after every restriction, including newly full faces. -/
structure CompatibleElement (x : Γ.Elements) where
  ambient : A.obj x
  face : ∀ {y : Γ.Elements} (_f : x ⟶ y) (h : φ.Holds y), T.obj (faceObj φ y h)
  naturality : ∀ {y z : Γ.Elements} (f : x ⟶ y) (g : y ⟶ z) (h : φ.Holds y),
    T.map (faceHom φ g h) (face f h) = face (f ≫ g) (φ.natural g h)
  compatible : ∀ {y : Γ.Elements} (f : x ⟶ y) (h : φ.Holds y),
    e.app (faceObj φ y h) (face f h) = A.map f ambient

@[ext] theorem CompatibleElement.ext {x : Γ.Elements} {s t : CompatibleElement φ A T e x}
    (ha : s.ambient = t.ambient) (ht : ∀ {y} (f : x ⟶ y) h, s.face f h = t.face f h) : s = t := by
  cases s
  cases t
  cases ha
  simp_all only [mk.injEq, true_and]
  funext y f h
  exact ht f h

def CompatibleElement.restrict {x y : Γ.Elements} (f : x ⟶ y)
    (s : CompatibleElement φ A T e x) : CompatibleElement φ A T e y where
  ambient := A.map f s.ambient
  face g h := s.face (f ≫ g) h
  naturality g k h := by simpa only [Category.assoc] using s.naturality (f ≫ g) k h
  compatible g h := by
    simpa only [Functor.map_comp, types_comp_apply] using s.compatible (f ≫ g) h

def compatibleFamily : Family Γ where
  obj x := CompatibleElement φ A T e x
  map f := TypeCat.ofHom (CompatibleElement.restrict φ A T e f)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro s
    apply CompatibleElement.ext
    · exact ConcreteCategory.congr_hom (A.map_id x) s.ambient
    · intro y f h
      change s.face (𝟙 x ≫ f) h = s.face f h
      rw [Category.id_comp]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    apply CompatibleElement.ext
    · exact ConcreteCategory.congr_hom (A.map_comp f g) s.ambient
    · intro y k h
      change s.face ((f ≫ g) ≫ k) h = s.face (f ≫ (g ≫ k)) h
      rw [Category.assoc]

def compatibleUnglue : compatibleFamily φ A T e ⟶ A where
  app _ := TypeCat.ofHom CompatibleElement.ambient
  naturality _ _ _ := rfl

/-- On a full face the ambient component is determined by the face element. -/
def fromFace {x : Γ.Elements} (h : φ.Holds x) (t : T.obj (faceObj φ x h)) :
    CompatibleElement φ A T e x where
  ambient := e.app (faceObj φ x h) t
  face f _ := T.map (faceHom φ f h) t
  naturality f g _ := by
    exact (ConcreteCategory.congr_hom (T.map_comp (faceHom φ f h)
      (faceHom φ g (φ.natural f h))) t).symm
  compatible f _ := ConcreteCategory.congr_hom (e.naturality (faceHom φ f h)) t

theorem fromFace_read {x : Γ.Elements} (h : φ.Holds x)
    (t : T.obj (faceObj φ x h)) : (fromFace φ A T e h t).face (𝟙 x) h = t :=
  ConcreteCategory.congr_hom (T.map_id (faceObj φ x h)) t

theorem read_fromFace {x : Γ.Elements} (h : φ.Holds x)
    (s : CompatibleElement φ A T e x) : fromFace φ A T e h (s.face (𝟙 x) h) = s := by
  apply CompatibleElement.ext
  · exact (s.compatible (𝟙 x) h).trans
      (ConcreteCategory.congr_hom (A.map_id x) s.ambient)
  · intro y f hy
    change T.map (faceHom φ f h) (s.face (𝟙 x) h) = s.face f hy
    simpa only [Category.id_comp] using s.naturality (𝟙 x) f h

def fullFaceEquiv {x : Γ.Elements} (h : φ.Holds x) :
    T.obj (faceObj φ x h) ≃ CompatibleElement φ A T e x where
  toFun := fromFace φ A T e h
  invFun s := s.face (𝟙 x) h
  left_inv := fromFace_read φ A T e h
  right_inv := read_fromFace φ A T e h

/-- The strict carrier uses the supplied face type whenever the face is full. -/
def Fiber (x : Γ.Elements) : Type u :=
  if h : φ.Holds x then T.obj (faceObj φ x h) else CompatibleElement φ A T e x

def fiberEquiv (x : Γ.Elements) : Fiber φ A T e x ≃ CompatibleElement φ A T e x :=
  if h : φ.Holds x then
    (Equiv.cast (show Fiber φ A T e x = T.obj (faceObj φ x h) from dite_eq_left h)).trans
      (fullFaceEquiv φ A T e h)
  else Equiv.cast (show Fiber φ A T e x = CompatibleElement φ A T e x from dite_eq_right h)

/-- Restrictions use compatible data also when a face becomes full later. -/
def family : Family Γ :=
  (compatibleFamily φ A T e).copyObj (Fiber φ A T e)
    (fun x => (fiberEquiv φ A T e x).symm.toIso)

def familyIso : family φ A T e ≅ compatibleFamily φ A T e :=
  ((compatibleFamily φ A T e).isoCopyObj (Fiber φ A T e)
    (fun x => (fiberEquiv φ A T e x).symm.toIso)).symm

def unglue : family φ A T e ⟶ A :=
  (familyIso φ A T e).hom ≫ compatibleUnglue φ A T e

/-- Introduction retains a global ambient section compatible with face data. -/
def compatibleIntro (t : Term T) (a : Term A)
    (h : Term.map e t = Term.reindex a (restrictInclusion φ)) :
    Term (compatibleFamily φ A T e) where
  val x := {
    ambient := a.val x
    face := fun {_} _ hy => t.val (faceObj φ _ hy)
    naturality := fun _ g hy => t.property (faceHom φ g hy)
    compatible := fun {y} f hy =>
      (congrArg (fun q => q.val (faceObj φ y hy)) h).trans (a.property f).symm }
  property f := by
    apply CompatibleElement.ext
    · exact a.property f
    · intro y g hy
      rfl

def intro (t : Term T) (a : Term A)
    (h : Term.map e t = Term.reindex a (restrictInclusion φ)) : Term (family φ A T e) :=
  Term.map (familyIso φ A T e).inv (compatibleIntro φ A T e t a h)

theorem unglue_intro (t : Term T) (a : Term A)
    (h : Term.map e t = Term.reindex a (restrictInclusion φ)) :
    Term.map (unglue φ A T e) (intro φ A T e t a h) = a := by
  apply Term.ext
  intro x
  exact congrArg CompatibleElement.ambient
    ((fiberEquiv φ A T e x).apply_symm_apply ((compatibleIntro φ A T e t a h).val x))

def compatibleFace (s : Term (compatibleFamily φ A T e)) : Term T where
  val x := (s.val ((restrictInclusion φ).mapElements.obj x)).face (𝟙 _) x.val.property
  property {x y} f := by
    let q := (restrictInclusion φ).mapElements.map f
    have hn := (s.val ((restrictInclusion φ).mapElements.obj x)).naturality (𝟙 _) q x.val.property
    have hs := congrArg (fun z : CompatibleElement φ A T e
      ((restrictInclusion φ).mapElements.obj y) => z.face (𝟙 _) y.val.property) (s.property q)
    change T.map f ((s.val ((restrictInclusion φ).mapElements.obj x)).face (𝟙 _) x.val.property) =
      (s.val ((restrictInclusion φ).mapElements.obj y)).face (𝟙 _) y.val.property
    simp only [Category.id_comp] at hn
    change (s.val ((restrictInclusion φ).mapElements.obj x)).face (q ≫ 𝟙 _) y.val.property = _ at hs
    rw [Category.comp_id] at hs
    exact hn.trans hs

theorem compatibleFace_ambient (s : Term (compatibleFamily φ A T e)) :
    Term.map e (compatibleFace φ A T e s) =
      Term.reindex (Term.map (compatibleUnglue φ A T e) s) (restrictInclusion φ) := by
  apply Term.ext
  intro x
  exact ((s.val ((restrictInclusion φ).mapElements.obj x)).compatible (𝟙 _) x.val.property).trans
    (ConcreteCategory.congr_hom (A.map_id _) _)

theorem compatible_eta (s : Term (compatibleFamily φ A T e)) :
    compatibleIntro φ A T e (compatibleFace φ A T e s)
      (Term.map (compatibleUnglue φ A T e) s) (compatibleFace_ambient φ A T e s) = s := by
  apply Term.ext
  intro x
  apply CompatibleElement.ext
  · rfl
  · intro y f h
    have hs := congrArg (fun z : CompatibleElement φ A T e y => z.face (𝟙 _) h) (s.property f)
    change (s.val y).face (𝟙 _) h = (s.val x).face f h
    change (s.val x).face (f ≫ 𝟙 _) h = (s.val y).face (𝟙 _) h at hs
    rw [Category.comp_id] at hs
    exact hs.symm

theorem fiber_full (x : Γ.Elements) (h : φ.Holds x) :
    Fiber φ A T e x = T.obj (faceObj φ x h) := dite_eq_left h

def compatibleFullFaceIso : reindex (compatibleFamily φ A T e) (restrictInclusion φ) ≅ T :=
  NatIso.ofComponents (fun x =>
    (fullFaceEquiv φ A T e (x := (restrictInclusion φ).mapElements.obj x) x.val.property).symm.toIso)
    (by
      intro x y f
      apply ConcreteCategory.hom_ext
      intro a
      let q := (restrictInclusion φ).mapElements.map f
      have hn := a.naturality (𝟙 _) q x.val.property
      change a.face (q ≫ 𝟙 _) y.val.property = T.map f (a.face (𝟙 _) x.val.property)
      rw [Category.comp_id]
      simp only [Category.id_comp] at hn
      exact hn.symm)

def fullFaceIso : reindex (family φ A T e) (restrictInclusion φ) ≅ T :=
  (Functor.isoWhiskerLeft (restrictInclusion φ).mapElements (familyIso φ A T e)) ≪≫
    compatibleFullFaceIso φ A T e

theorem fiberEquiv_full {x : Γ.Elements} (h : φ.Holds x)
    (a : Fiber φ A T e x) (t : T.obj (faceObj φ x h)) (ha : HEq a t) :
    (fiberEquiv φ A T e x) a = fromFace φ A T e h t := by
  simp only [fiberEquiv, dite_eq_left h]
  apply congrArg (fromFace φ A T e h)
  exact eq_of_heq ((cast_heq _ a).trans ha)

theorem fiberEquiv_symm_full {x : Γ.Elements} (h : φ.Holds x)
    (s : CompatibleElement φ A T e x) :
    HEq ((fiberEquiv φ A T e x).symm s) (s.face (𝟙 x) h) := by
  simp only [fiberEquiv, dite_eq_left h]
  exact cast_heq _ _

private theorem ofHom_hext {A B C D : Type u} {f : A → B} {g : C → D}
    (ha : A = C) (hb : B = D) (h : ∀ a c, HEq a c → HEq (f a) (g c)) :
    HEq (TypeCat.ofHom f) (TypeCat.ofHom g) := by
  cases ha
  cases hb
  have hf : f = g := funext (fun a => eq_of_heq (h a a HEq.rfl))
  cases hf
  rfl

/-- Full-face reduction is equality of families, beyond the comparison isomorphism. -/
theorem family_full : reindex (family φ A T e) (restrictInclusion φ) = T := by
  have ho : ∀ x, (reindex (family φ A T e) (restrictInclusion φ)).obj x = T.obj x :=
    fun x => fiber_full φ A T e ((restrictInclusion φ).mapElements.obj x) x.val.property
  apply Functor.hext ho
  intro x y f
  apply ofHom_hext (ho x) (ho y)
  intro a t hat
  let q := (restrictInclusion φ).mapElements.map f
  have hx := fiberEquiv_full φ A T e x.val.property a t hat
  have hy := fiberEquiv_symm_full φ A T e y.val.property
    ((compatibleFamily φ A T e).map q ((fiberEquiv φ A T e _) a))
  apply hy.trans
  apply heq_of_eq
  change ((fiberEquiv φ A T e _) a).face (q ≫ 𝟙 _) y.val.property = T.map f t
  exact (congrArg (fun z : CompatibleElement φ A T e ((restrictInclusion φ).mapElements.obj x) =>
    z.face (q ≫ 𝟙 _) y.val.property) hx).trans
      (congrArg (fun k => T.map k t) (by apply Functor.Elements.hom_ext; exact Category.comp_id _))

end Glue

namespace Glue
variable {Γ Δ : Context.{u}} (φ : Subcontext Γ) (A : Family Γ)
  (T : Family (restrictContext φ)) (e : T ⟶ reindex A (restrictInclusion φ))
  (σ : Δ ⟶ Γ)

def compatibleReindexMap : reindex (compatibleFamily φ A T e) σ ⟶
    compatibleFamily (φ.reindex σ) (reindex A σ)
      (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) where
  app _ := TypeCat.ofHom (fun s => {
    ambient := s.ambient
    face := fun {_} f h => s.face (σ.mapElements.map f) h
    naturality := fun f g h => s.naturality (σ.mapElements.map f) (σ.mapElements.map g) h
    compatible := fun f h => s.compatible (σ.mapElements.map f) h })
  naturality _ _ _ := rfl

def reindexMap : reindex (family φ A T e) σ ⟶
    family (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) :=
  Functor.whiskerLeft σ.mapElements (familyIso φ A T e).hom ≫
    compatibleReindexMap φ A T e σ ≫
      (familyIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
        (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)).inv

theorem compatibleReindexMap_compatibleIntro (t : Term T) (a : Term A)
    (h : Term.map e t = Term.reindex a (restrictInclusion φ)) :
    Term.map (compatibleReindexMap φ A T e σ)
      (Term.reindex (compatibleIntro φ A T e t a h) σ) =
    compatibleIntro (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)
      (Term.reindex t (restrictSubstitution φ σ)) (Term.reindex a σ)
      (congrArg (fun t => Term.reindex t (restrictSubstitution φ σ)) h) := rfl

def inverseFace {x : Δ.Elements}
    (s : CompatibleElement (φ.reindex σ) (reindex A σ)
      (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) x)
    {y : Γ.Elements} (f : σ.mapElements.obj x ⟶ y) (h : φ.Holds y) : T.obj (faceObj φ y h) :=
  Equiv.piCongrLeft (P := fun z : Σ y, σ.mapElements.obj x ⟶ y =>
    ∀ h : φ.Holds z.1, T.obj (faceObj φ z.1 h)) (substitutionArrowEquiv σ x)
      (fun z h => s.face z.2 h) ⟨y,f⟩ h

theorem inverseFace_map {x y : Δ.Elements}
    (s : CompatibleElement (φ.reindex σ) (reindex A σ)
      (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) x)
    (f : x ⟶ y) (h : φ.Holds (σ.mapElements.obj y)) :
    inverseFace φ A T e σ s (σ.mapElements.map f) h = s.face f h :=
  congrFun (Equiv.piCongrLeft_apply_apply
    (P := fun z : Σ y, σ.mapElements.obj x ⟶ y =>
      ∀ h : φ.Holds z.1, T.obj (faceObj φ z.1 h))
    (e := substitutionArrowEquiv σ x) (fun z h => s.face z.2 h) ⟨y,f⟩) h

def inverseElement {x : Δ.Elements}
    (s : CompatibleElement (φ.reindex σ) (reindex A σ)
      (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) x) :
    CompatibleElement φ A T e (σ.mapElements.obj x) where
  ambient := s.ambient
  face := inverseFace φ A T e σ s
  naturality {y z} f g h := by
    obtain ⟨⟨y',f'⟩,hf⟩ := (substitutionArrowEquiv σ x).surjective ⟨y,f⟩
    change (⟨σ.mapElements.obj y',σ.mapElements.map f'⟩ : Σ y, σ.mapElements.obj x ⟶ y) = ⟨y,f⟩ at hf
    cases hf
    obtain ⟨⟨z',g'⟩,hg⟩ := (substitutionArrowEquiv σ y').surjective ⟨z,g⟩
    change (⟨σ.mapElements.obj z',σ.mapElements.map g'⟩ : Σ z, σ.mapElements.obj y' ⟶ z) = ⟨z,g⟩ at hg
    cases hg
    change T.map (faceHom φ (σ.mapElements.map g') h)
      (inverseFace φ A T e σ s (σ.mapElements.map f') h) =
      inverseFace φ A T e σ s (σ.mapElements.map (f' ≫ g')) _
    rw [inverseFace_map, inverseFace_map]
    exact s.naturality f' g' h
  compatible {y} f h := by
    obtain ⟨⟨y',f'⟩,hf⟩ := (substitutionArrowEquiv σ x).surjective ⟨y,f⟩
    change (⟨σ.mapElements.obj y',σ.mapElements.map f'⟩ : Σ y, σ.mapElements.obj x ⟶ y) = ⟨y,f⟩ at hf
    cases hf
    rw [inverseFace_map]
    exact s.compatible f' h

def compatibleReindexInv :
    compatibleFamily (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) ⟶
    reindex (compatibleFamily φ A T e) σ where
  app _ := TypeCat.ofHom (inverseElement φ A T e σ)
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply CompatibleElement.ext
    · rfl
    · intro z g h
      obtain ⟨⟨z',g'⟩,hg⟩ := (substitutionArrowEquiv σ y).surjective ⟨z,g⟩
      change (⟨σ.mapElements.obj z',σ.mapElements.map g'⟩ : Σ z, σ.mapElements.obj y ⟶ z) = ⟨z,g⟩ at hg
      cases hg
      change inverseFace φ A T e σ (s.restrict _ _ _ _ f) (σ.mapElements.map g') h =
        inverseFace φ A T e σ s (σ.mapElements.map (f ≫ g')) h
      exact (inverseFace_map φ A T e σ (s.restrict _ _ _ _ f) g' h).trans
        (inverseFace_map φ A T e σ s (f ≫ g') h).symm

/-- Every restriction datum is recovered, including arrows outside the displayed substitution. -/
def compatibleReindexIso : reindex (compatibleFamily φ A T e) σ ≅
    compatibleFamily (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) where
  hom := compatibleReindexMap φ A T e σ
  inv := compatibleReindexInv φ A T e σ
  hom_inv_id := by
    ext x s
    apply CompatibleElement.ext
    · rfl
    · intro y f h
      obtain ⟨⟨y',f'⟩,hf⟩ := (substitutionArrowEquiv σ x).surjective ⟨y,f⟩
      change (⟨σ.mapElements.obj y',σ.mapElements.map f'⟩ : Σ y, σ.mapElements.obj x ⟶ y) = ⟨y,f⟩ at hf
      cases hf
      exact inverseFace_map φ A T e σ _ f' h
  inv_hom_id := by
    ext x s
    apply CompatibleElement.ext
    · rfl
    · intro y f h
      exact inverseFace_map φ A T e σ s f h

/-- Glue substitution is invertible for its complete compatible-data presentation. -/
noncomputable def reindexIso : reindex (family φ A T e) σ ≅
    family (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) :=
  (Functor.isoWhiskerLeft σ.mapElements (familyIso φ A T e)) ≪≫
    compatibleReindexIso φ A T e σ ≪≫
      (familyIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
        (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)).symm

end Glue

namespace Glue
/-- Data to be localized before selecting a small Glue carrier. -/
structure Datum (Γ : Context.{u}) where
  face : Subcontext Γ
  ambient : Family Γ
  faceFamily : Family (restrictContext face)
  map : faceFamily ⟶ Cartesian.reindex ambient (restrictInclusion face)

def Datum.reindex {Γ Δ : Context.{u}} (D : Datum Γ) (σ : Δ ⟶ Γ) : Datum Δ where
  face := D.face.reindex σ
  ambient := Cartesian.reindex D.ambient σ
  faceFamily := Cartesian.reindex D.faceFamily (restrictSubstitution D.face σ)
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

def Datum.LocalCarrier {Γ : Context.{u}} (D : Datum Γ) (x : Γ.Elements) : Type u :=
  (D.local x).compatible.obj (representableGeneric.{u} x.obj.unop)

theorem Datum.localCarrier_substitution {Γ Δ : Context.{u}} (D : Datum Γ)
    (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    (D.reindex σ).LocalCarrier x = D.LocalCarrier (σ.mapElements.obj x) :=
  congrArg (fun L => L.compatible.obj (representableGeneric.{u} x.obj.unop))
    (D.local_substitution σ x)

def Datum.localCarrierEquiv {Γ : Context.{u}} (D : Datum Γ) (x : Γ.Elements) :
    D.LocalCarrier x ≃ D.compatible.obj x :=
  (((compatibleReindexIso D.face D.ambient D.faceFamily D.map (represented x)).app
    (representableGeneric.{u} x.obj.unop)).symm.toEquiv).trans
      (D.compatible.mapIso (eqToIso (represented_generic_source x))).toEquiv

/-- Full faces retain the given carrier; other cubes use a local presentation. -/
def Datum.SmallFiber {Γ : Context.{u}} (D : Datum Γ) (x : Γ.Elements) : Type u :=
  if h : D.face.Holds x then D.faceFamily.obj (faceObj D.face x h) else D.LocalCarrier x

def Datum.smallFiberEquiv {Γ : Context.{u}} (D : Datum Γ) (x : Γ.Elements) :
    D.SmallFiber x ≃ D.compatible.obj x :=
  if h : D.face.Holds x then
    (Equiv.cast (show D.SmallFiber x = D.faceFamily.obj (faceObj D.face x h) from dite_eq_left h)).trans
      (fullFaceEquiv D.face D.ambient D.faceFamily D.map h)
  else
    (Equiv.cast (show D.SmallFiber x = D.LocalCarrier x from dite_eq_right h)).trans
      (D.localCarrierEquiv x)

theorem Datum.smallFiber_substitution {Γ Δ : Context.{u}} (D : Datum Γ)
    (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    (D.reindex σ).SmallFiber x = D.SmallFiber (σ.mapElements.obj x) := by
  unfold SmallFiber
  change (if h : D.face.Holds (σ.mapElements.obj x) then
    D.faceFamily.obj (faceObj D.face (σ.mapElements.obj x) h) else (D.reindex σ).LocalCarrier x) = _
  by_cases h : D.face.Holds (σ.mapElements.obj x)
  · rw [dite_eq_left h, dite_eq_left h]
  · rw [dite_eq_right h, dite_eq_right h]
    exact D.localCarrier_substitution σ x

def Datum.smallFamily {Γ : Context.{u}} (D : Datum Γ) : Family Γ :=
  D.compatible.copyObj D.SmallFiber (fun x => (D.smallFiberEquiv x).symm.toIso)

def Datum.smallFamilyIso {Γ : Context.{u}} (D : Datum Γ) : D.smallFamily ≅ D.compatible :=
  (D.compatible.isoCopyObj D.SmallFiber (fun x => (D.smallFiberEquiv x).symm.toIso)).symm

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

theorem Datum.localCarrierEquiv_symm_substitution {Γ Δ : Context.{u}} (D : Datum Γ)
    (σ : Δ ⟶ Γ) (x : Δ.Elements) (s : D.compatible.obj (σ.mapElements.obj x)) :
    HEq ((D.localCarrierEquiv (σ.mapElements.obj x)).symm s)
      (((D.reindex σ).localCarrierEquiv x).symm
        ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x s)) := by
  exact (D.chartMap_congr _ _ (represented_naturality σ x)
    (σ.mapElements.obj x) (represented_generic_source (σ.mapElements.obj x))
    (congrArg σ.mapElements.obj (represented_generic_source x)) s).trans
      (heq_of_eq (D.chartMap_substitution σ (represented x) x (represented_generic_source x) s).symm)

theorem Datum.smallFiberEquiv_symm_substitution {Γ Δ : Context.{u}} (D : Datum Γ)
    (σ : Δ ⟶ Γ) (x : Δ.Elements) (s : D.compatible.obj (σ.mapElements.obj x)) :
    HEq ((D.smallFiberEquiv (σ.mapElements.obj x)).symm s)
      (((D.reindex σ).smallFiberEquiv x).symm
        ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x s)) := by
  by_cases h : D.face.Holds (σ.mapElements.obj x)
  · have h' : (D.reindex σ).face.Holds x := h
    simp only [smallFiberEquiv, dite_eq_left h, dite_eq_left h']
    exact (cast_heq _ _).trans (cast_heq _ _).symm
  · have h' : ¬(D.reindex σ).face.Holds x := h
    simp only [smallFiberEquiv, dite_eq_right h, dite_eq_right h']
    exact (cast_heq _ _).trans ((D.localCarrierEquiv_symm_substitution σ x s).trans (cast_heq _ _).symm)

theorem Datum.smallFamily_substitution {Γ Δ : Context.{u}} (D : Datum Γ) (σ : Δ ⟶ Γ) :
    Cartesian.reindex D.smallFamily σ = (D.reindex σ).smallFamily := by
  have ho : ∀ x, (Cartesian.reindex D.smallFamily σ).obj x = (D.reindex σ).smallFamily.obj x :=
    fun x => (D.smallFiber_substitution σ x).symm
  apply Functor.hext ho
  intro x y f
  apply ofHom_hext (ho x) (ho y)
  intro s t hst
  have ht : t = ((D.reindex σ).smallFiberEquiv x).symm
      ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x
        (D.smallFiberEquiv (σ.mapElements.obj x) s)) :=
    eq_of_heq (hst.symm.trans
      ((heq_of_eq ((D.smallFiberEquiv (σ.mapElements.obj x)).symm_apply_apply s)).symm.trans
        (D.smallFiberEquiv_symm_substitution σ x (D.smallFiberEquiv (σ.mapElements.obj x) s))))
  subst t
  change HEq ((D.smallFiberEquiv (σ.mapElements.obj y)).symm
    (D.compatible.map (σ.mapElements.map f) (D.smallFiberEquiv (σ.mapElements.obj x) s)))
    (((D.reindex σ).smallFiberEquiv y).symm
      ((D.reindex σ).compatible.map f (((D.reindex σ).smallFiberEquiv x)
        (((D.reindex σ).smallFiberEquiv x).symm
          ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x
            (D.smallFiberEquiv (σ.mapElements.obj x) s))))))
  exact (D.smallFiberEquiv_symm_substitution σ y
    (D.compatible.map (σ.mapElements.map f) (D.smallFiberEquiv (σ.mapElements.obj x) s))).trans
      (heq_of_eq (congrArg (fun a => ((D.reindex σ).smallFiberEquiv y).symm
        ((D.reindex σ).compatible.map f a))
          (((D.reindex σ).smallFiberEquiv x).apply_symm_apply
            ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x
              (D.smallFiberEquiv (σ.mapElements.obj x) s)))).symm)

theorem Datum.smallFiberEquiv_full {Γ : Context.{u}} (D : Datum Γ) {x : Γ.Elements}
    (h : D.face.Holds x) (a : D.SmallFiber x) (t : D.faceFamily.obj (faceObj D.face x h))
    (ha : HEq a t) : D.smallFiberEquiv x a = fromFace D.face D.ambient D.faceFamily D.map h t := by
  simp only [smallFiberEquiv, dite_eq_left h]
  apply congrArg (fromFace D.face D.ambient D.faceFamily D.map h)
  exact eq_of_heq ((cast_heq _ a).trans ha)

theorem Datum.smallFiberEquiv_symm_full {Γ : Context.{u}} (D : Datum Γ) {x : Γ.Elements}
    (h : D.face.Holds x) (s : D.compatible.obj x) :
    HEq ((D.smallFiberEquiv x).symm s) (s.face (𝟙 x) h) := by
  simp only [smallFiberEquiv, dite_eq_left h]
  exact cast_heq _ _

theorem Datum.smallFamily_full {Γ : Context.{u}} (D : Datum Γ) :
    Cartesian.reindex D.smallFamily (restrictInclusion D.face) = D.faceFamily := by
  have ho : ∀ x, (Cartesian.reindex D.smallFamily (restrictInclusion D.face)).obj x = D.faceFamily.obj x :=
    fun x => dite_eq_left x.val.property
  apply Functor.hext ho
  intro x y f
  apply ofHom_hext (ho x) (ho y)
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

/-- The normalized family retains the actual ambient projection. -/
def Datum.smallUnglue {Γ : Context.{u}} (D : Datum Γ) : D.smallFamily ⟶ D.ambient :=
  D.smallFamilyIso.hom ≫ compatibleUnglue D.face D.ambient D.faceFamily D.map

/-- On the full face, unglue is the supplied map with only the family-equality cast. -/
theorem Datum.smallUnglue_full {Γ : Context.{u}} (D : Datum Γ) :
    Functor.whiskerLeft (restrictInclusion D.face).mapElements D.smallUnglue =
      (eqToIso D.smallFamily_full).hom ≫ D.map := by
  ext x a
  let t := (eqToIso D.smallFamily_full).hom.app x a
  have ht : HEq a t := by
    exact (show HEq t a from by
      dsimp [t]
      have eqCast : ∀ {B C : Family (restrictContext D.face)} (h : B = C)
          (y : (restrictContext D.face).Elements) (b : B.obj y),
          HEq ((eqToIso h).hom.app y b) b := by
        intro B C h y b
        cases h
        rfl
      exact eqCast D.smallFamily_full x a).symm
  exact congrArg CompatibleElement.ambient (D.smallFiberEquiv_full x.val.property a t ht)

private theorem family_eqToIso_hom_heq {Γ : Context.{u}} {A B : Family Γ}
    (h : A = B) (x : Γ.Elements) (z : A.obj x) : HEq ((eqToIso h).hom.app x z) z := by
  cases h
  rfl

theorem Datum.nativeIso_substitution {Γ Δ : Context.{u}} (D : Datum Γ) (σ : Δ ⟶ Γ) :
    (Functor.isoWhiskerLeft σ.mapElements D.nativeIso) ≪≫ eqToIso (D.smallFamily_substitution σ) =
      reindexIso D.face D.ambient D.faceFamily D.map σ ≪≫ (D.reindex σ).nativeIso := by
  apply Iso.ext
  ext x z
  have hnew := congrArg (fun m => m.app x
    ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x
      ((familyIso D.face D.ambient D.faceFamily D.map).hom.app (σ.mapElements.obj x) z)))
    (familyIso (D.face.reindex σ) (Cartesian.reindex D.ambient σ)
      (Cartesian.reindex D.faceFamily (restrictSubstitution D.face σ))
      (Functor.whiskerLeft (restrictSubstitution D.face σ).mapElements D.map)).inv_hom_id
  exact eq_of_heq ((family_eqToIso_hom_heq (D.smallFamily_substitution σ) x _).trans
    ((D.smallFiberEquiv_symm_substitution σ x ((familyIso D.face D.ambient D.faceFamily D.map).hom.app
      (σ.mapElements.obj x) z)).trans
        (heq_of_eq (congrArg ((D.reindex σ).smallFiberEquiv x).symm hnew).symm)))

end Glue
end
end SquareKit.Cubical.Cartesian

namespace SquareKit.Cubical.Cartesian.Glue
open CategoryTheory
universe u
theorem Datum.nativeIso_unglue {Γ : Context.{u}} (D : Datum Γ) :
    D.nativeIso.hom ≫ D.smallUnglue = unglue D.face D.ambient D.faceFamily D.map := by
  change ((familyIso _ _ _ _).hom ≫ D.smallFamilyIso.inv) ≫ (D.smallFamilyIso.hom ≫ _) = _
  erw [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

theorem reindexIso_unglue {Γ Δ : Context.{u}} (D : Datum Γ) (σ : Δ ⟶ Γ) :
    (reindexIso D.face D.ambient D.faceFamily D.map σ).hom ≫
      unglue (D.reindex σ).face (D.reindex σ).ambient (D.reindex σ).faceFamily (D.reindex σ).map =
    Functor.whiskerLeft σ.mapElements (unglue D.face D.ambient D.faceFamily D.map) := by
  ext x z
  exact congrArg CompatibleElement.ambient
    (congrArg (fun m => m.app x
      ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x
        ((familyIso D.face D.ambient D.faceFamily D.map).hom.app (σ.mapElements.obj x) z)))
      (familyIso (D.reindex σ).face (D.reindex σ).ambient (D.reindex σ).faceFamily (D.reindex σ).map).inv_hom_id)

theorem Datum.smallUnglue_substitution {Γ Δ : Context.{u}} (D : Datum Γ) (σ : Δ ⟶ Γ) :
    Functor.whiskerLeft σ.mapElements D.smallUnglue =
      eqToHom (D.smallFamily_substitution σ) ≫ (D.reindex σ).smallUnglue := by
  apply (cancel_epi (Functor.whiskerLeft σ.mapElements D.nativeIso.hom)).mp
  have h := congrArg (fun i => i.hom) (D.nativeIso_substitution σ)
  change Functor.whiskerLeft σ.mapElements D.nativeIso.hom ≫ eqToHom (D.smallFamily_substitution σ) =
    (reindexIso D.face D.ambient D.faceFamily D.map σ).hom ≫ (D.reindex σ).nativeIso.hom at h
  erw [← Category.assoc, h, Category.assoc, Datum.nativeIso_unglue, reindexIso_unglue]
  exact congrArg (Functor.whiskerLeft σ.mapElements) D.nativeIso_unglue
end SquareKit.Cubical.Cartesian.Glue
