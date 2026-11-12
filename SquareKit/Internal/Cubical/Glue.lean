import SquareKit.Internal.Cubical.EquivalenceExtension

/-! Compatible ambient and face data for Glue. The compatibility presentation
is kept separate from its full-face strictification and selected filling. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace Glue
variable {Γ : Context.{u}} (φ : Cofibration Γ)

def faceObj (x : Γ.Elements) (h : φ.full x) : (restrictContext φ).Elements :=
  (restrictContext φ).elementsMk x.obj ⟨x.val,h⟩

def faceHom {x y : Γ.Elements} (f : x ⟶ y) (h : φ.full x) :
    faceObj φ x h ⟶ faceObj φ y (φ.full_natural f h) :=
  Functor.Elements.homMk f.hom (Subtype.ext f.map_val)

variable (A : Family Γ) (T : Family (restrictContext φ))
  (e : T ⟶ reindex A (restrictInclusion φ))

/-- Face data is coherent after every restriction, including newly full faces. -/
structure CompatibleElement (x : Γ.Elements) where
  ambient : A.obj x
  face : ∀ {y : Γ.Elements} (_f : x ⟶ y) (h : φ.full y), T.obj (faceObj φ y h)
  naturality : ∀ {y z : Γ.Elements} (f : x ⟶ y) (g : y ⟶ z) (h : φ.full y),
    T.map (faceHom φ g h) (face f h) = face (f ≫ g) (φ.full_natural g h)
  compatible : ∀ {y : Γ.Elements} (f : x ⟶ y) (h : φ.full y),
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
def fromFace {x : Γ.Elements} (h : φ.full x) (t : T.obj (faceObj φ x h)) :
    CompatibleElement φ A T e x where
  ambient := e.app (faceObj φ x h) t
  face f _ := T.map (faceHom φ f h) t
  naturality f g _ := by
    exact (ConcreteCategory.congr_hom (T.map_comp (faceHom φ f h)
      (faceHom φ g (φ.full_natural f h))) t).symm
  compatible f _ := ConcreteCategory.congr_hom (e.naturality (faceHom φ f h)) t

theorem fromFace_read {x : Γ.Elements} (h : φ.full x)
    (t : T.obj (faceObj φ x h)) : (fromFace φ A T e h t).face (𝟙 x) h = t :=
  ConcreteCategory.congr_hom (T.map_id (faceObj φ x h)) t

theorem read_fromFace {x : Γ.Elements} (h : φ.full x)
    (s : CompatibleElement φ A T e x) : fromFace φ A T e h (s.face (𝟙 x) h) = s := by
  apply CompatibleElement.ext
  · exact (s.compatible (𝟙 x) h).trans
      (ConcreteCategory.congr_hom (A.map_id x) s.ambient)
  · intro y f hy
    change T.map (faceHom φ f h) (s.face (𝟙 x) h) = s.face f hy
    simpa only [Category.id_comp] using s.naturality (𝟙 x) f h

def fullFaceEquiv {x : Γ.Elements} (h : φ.full x) :
    T.obj (faceObj φ x h) ≃ CompatibleElement φ A T e x where
  toFun := fromFace φ A T e h
  invFun s := s.face (𝟙 x) h
  left_inv := fromFace_read φ A T e h
  right_inv := read_fromFace φ A T e h

/-- The strict carrier uses the supplied face type whenever the face is full. -/
def fiber (x : Γ.Elements) : Type u :=
  if h : φ.full x then T.obj (faceObj φ x h) else CompatibleElement φ A T e x

def fiberEquiv (x : Γ.Elements) : fiber φ A T e x ≃ CompatibleElement φ A T e x :=
  if h : φ.full x then
    (Equiv.cast (show fiber φ A T e x = T.obj (faceObj φ x h) from dite_eq_left h)).trans
      (fullFaceEquiv φ A T e h)
  else Equiv.cast (show fiber φ A T e x = CompatibleElement φ A T e x from dite_eq_right h)

/-- Restrictions use compatible data also when a face becomes full later. -/
def family : Family Γ :=
  (compatibleFamily φ A T e).copyObj (fiber φ A T e)
    (fun x => (fiberEquiv φ A T e x).symm.toIso)

def familyIso : family φ A T e ≅ compatibleFamily φ A T e :=
  ((compatibleFamily φ A T e).isoCopyObj (fiber φ A T e)
    (fun x => (fiberEquiv φ A T e x).symm.toIso)).symm

def unglue : family φ A T e ⟶ A :=
  (familyIso φ A T e).hom ≫ compatibleUnglue φ A T e

/-- Introduction retains a global ambient section compatible with face data. -/
def compatibleIntro (t : Term T) (a : Term A)
    (h : Term.map e t = a.reindex (restrictInclusion φ)) :
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
    (h : Term.map e t = a.reindex (restrictInclusion φ)) : Term (family φ A T e) :=
  Term.map (familyIso φ A T e).inv (compatibleIntro φ A T e t a h)

theorem unglue_intro (t : Term T) (a : Term A)
    (h : Term.map e t = a.reindex (restrictInclusion φ)) :
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
      (Term.map (compatibleUnglue φ A T e) s).reindex (restrictInclusion φ) := by
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

theorem fiber_full (x : Γ.Elements) (h : φ.full x) :
    fiber φ A T e x = T.obj (faceObj φ x h) := dite_eq_left h

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

theorem fiberEquiv_full {x : Γ.Elements} (h : φ.full x)
    (a : fiber φ A T e x) (t : T.obj (faceObj φ x h)) (ha : HEq a t) :
    (fiberEquiv φ A T e x) a = fromFace φ A T e h t := by
  simp only [fiberEquiv, dite_eq_left h]
  apply congrArg (fromFace φ A T e h)
  exact eq_of_heq ((cast_heq _ a).trans ha)

theorem fiberEquiv_symm_full {x : Γ.Elements} (h : φ.full x)
    (s : CompatibleElement φ A T e x) :
    HEq ((fiberEquiv φ A T e x).symm s) (s.face (𝟙 x) h) := by
  simp only [fiberEquiv, dite_eq_left h]
  exact cast_heq _ _

/-- Full-face reduction is equality of families, beyond the comparison isomorphism. -/
theorem family_full : reindex (family φ A T e) (restrictInclusion φ) = T := by
  have ho : ∀ x, (reindex (family φ A T e) (restrictInclusion φ)).obj x = T.obj x :=
    fun x => fiber_full φ A T e ((restrictInclusion φ).mapElements.obj x) x.val.property
  apply Functor.hext ho
  intro x y f
  apply typeHom_hext (ho x) (ho y)
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
end SquareKit.Cubical.Presheaf
