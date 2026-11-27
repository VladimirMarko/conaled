import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-! Diagrams over a fixed context diagram, and equivalences preserving that context. -/
noncomputable section
set_option autoImplicit false

namespace SquareKit.BasedDiagram
open CategoryTheory

universe u v u' v' a b i j
variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
variable {D : Type a} [Category.{b} D] {I : Type i} [Category.{j} I]

/-- Diagrams projecting to `K`, with arbitrary vertical natural transformations. -/
abbrev Over (p : C ⥤ D) (K : I ⥤ D) :=
  BasedFunctor (BasedCategory.ofFunctor K) (BasedCategory.ofFunctor p)

/-- Postcomposition with a functor that preserves projection to the base. -/
def postcompose {p : C ⥤ D} {q : C' ⥤ D} (K : I ⥤ D)
    (F : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q)) :
    Over p K ⥤ Over q K where
  obj A := BasedFunctor.comp A F
  map η := BasedCategory.whiskerRight η F
  map_id A := by
    apply BasedNatTrans.ext
    ext a
    exact F.map_id (A.obj a)
  map_comp η θ := by
    apply BasedNatTrans.ext
    ext a
    exact F.map_comp (η.app a) (θ.app a)

@[simp] theorem postcompose_obj_toFunctor {p : C ⥤ D} {q : C' ⥤ D} (K : I ⥤ D)
    (F : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (A : Over p K) : ((postcompose K F).obj A).toFunctor = A.toFunctor ⋙ F.toFunctor := rfl

@[simp] theorem postcompose_map_app {p : C ⥤ D} {q : C' ⥤ D} (K : I ⥤ D)
    (F : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    {A B : Over p K} (η : A ⟶ B) (i : I) :
    ((postcompose K F).map η).app i = F.map (η.app i) := rfl

variable (p : C ⥤ D) (q : C' ⥤ D) (K : I ⥤ D) (e : C ≌ C')
variable (hf : e.functor ⋙ q = p) (hg : e.inverse ⋙ p = q)
variable (hunit : ∀ X, p.IsHomLift (𝟙 (p.obj X)) (e.unitIso.hom.app X))
variable (hcounit : ∀ Y, q.IsHomLift (𝟙 (q.obj Y)) (e.counitIso.hom.app Y))

/-- Restrict an equivalence over the base to diagrams over `K`, retaining its recovery. -/
def equivalence : Over p K ≌ Over q K where
  functor := postcompose K ⟨e.functor, hf⟩
  inverse := postcompose K ⟨e.inverse, hg⟩
  unitIso := NatIso.ofComponents (fun A =>
    BasedNatIso.mkNatIso (Functor.isoWhiskerLeft A.toFunctor e.unitIso) (fun i => by
      have h := hunit (A.obj i)
      have hA : p.obj (A.obj i) = K.obj i := A.w_obj i
      change p.IsHomLift (𝟙 (K.obj i)) _
      rw [← hA]
      exact h)) (by
        intro A B η
        apply BasedNatTrans.ext
        ext i
        exact e.unitIso.hom.naturality (η.app i))
  counitIso := NatIso.ofComponents (fun A =>
    BasedNatIso.mkNatIso (Functor.isoWhiskerLeft A.toFunctor e.counitIso) (fun i => by
      have h := hcounit (A.obj i)
      have hA : q.obj (A.obj i) = K.obj i := A.w_obj i
      change q.IsHomLift (𝟙 (K.obj i)) _
      rw [← hA]
      exact h)) (by
        intro A B η
        apply BasedNatTrans.ext
        ext i
        exact e.counitIso.hom.naturality (η.app i))
  functor_unitIso_comp A := by
    apply BasedNatTrans.ext
    ext i
    exact e.functor_unit_comp (A.obj i)

@[simp] theorem equivalence_unit_app (A : Over p K) (i : I) :
    ((equivalence p q K e hf hg hunit hcounit).unitIso.hom.app A).app i =
      e.unitIso.hom.app (A.obj i) := rfl

@[simp] theorem equivalence_unit_inv_app (A : Over p K) (i : I) :
    ((equivalence p q K e hf hg hunit hcounit).unitIso.inv.app A).app i =
      e.unitIso.inv.app (A.obj i) := rfl

@[simp] theorem equivalence_counit_app (A : Over q K) (i : I) :
    ((equivalence p q K e hf hg hunit hcounit).counitIso.hom.app A).app i =
      e.counitIso.hom.app (A.obj i) := rfl

@[simp] theorem equivalence_counit_inv_app (A : Over q K) (i : I) :
    ((equivalence p q K e hf hg hunit hcounit).counitIso.inv.app A).app i =
      e.counitIso.inv.app (A.obj i) := rfl

/-- Cartesian transitions are an object property; maps between these diagrams remain arbitrary. -/
def Cartesian (p : C ⥤ D) (K : I ⥤ D) : ObjectProperty (Over p K) :=
  fun A => ∀ ⦃i j : I⦄ (f : i ⟶ j), p.IsCartesian (p.map (A.map f)) (A.map f)

/-- The full subcategory of diagrams whose transitions are cartesian. -/
abbrev CartesianOver (p : C ⥤ D) (K : I ⥤ D) := (Cartesian p K).FullSubcategory

variable (hforward : ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
  p.IsCartesian (p.map f) f →
    q.IsCartesian (q.map (e.functor.map f)) (e.functor.map f))
variable (hbackward : ∀ ⦃X Y : C'⦄ (f : X ⟶ Y),
  q.IsCartesian (q.map f) f →
    p.IsCartesian (p.map (e.inverse.map f)) (e.inverse.map f))

/-- Two-way preservation of cartesian arrows restricts the original diagram equivalence.
All vertical maps are retained by the full subcategories. -/
def cartesianEquivalence : CartesianOver p K ≌ CartesianOver q K where
  functor := (Cartesian q K).lift
    ((Cartesian p K).ι ⋙ (equivalence p q K e hf hg hunit hcounit).functor)
    (fun A _ _ f => hforward (A.obj.map f) (A.property f))
  inverse := (Cartesian p K).lift
    ((Cartesian q K).ι ⋙ (equivalence p q K e hf hg hunit hcounit).inverse)
    (fun A _ _ f => hbackward (A.obj.map f) (A.property f))
  unitIso := ((Cartesian p K).fullyFaithfulι.whiskeringRight _).preimageIso
    ((Cartesian p K).ι.isoWhiskerLeft (equivalence p q K e hf hg hunit hcounit).unitIso)
  counitIso := ((Cartesian q K).fullyFaithfulι.whiskeringRight _).preimageIso
    ((Cartesian q K).ι.isoWhiskerLeft (equivalence p q K e hf hg hunit hcounit).counitIso)
  functor_unitIso_comp A :=
    ObjectProperty.hom_ext _ ((equivalence p q K e hf hg hunit hcounit).functor_unit_comp A.obj)

@[simp] theorem cartesianEquivalence_unit_app (A : CartesianOver p K) (i : I) :
    ((cartesianEquivalence p q K e hf hg hunit hcounit hforward hbackward).unitIso.hom.app A).hom.app i =
      e.unitIso.hom.app (A.obj.obj i) := rfl

@[simp] theorem cartesianEquivalence_unit_inv_app (A : CartesianOver p K) (i : I) :
    ((cartesianEquivalence p q K e hf hg hunit hcounit hforward hbackward).unitIso.inv.app A).hom.app i =
      e.unitIso.inv.app (A.obj.obj i) := rfl

@[simp] theorem cartesianEquivalence_counit_app (A : CartesianOver q K) (i : I) :
    ((cartesianEquivalence p q K e hf hg hunit hcounit hforward hbackward).counitIso.hom.app A).hom.app i =
      e.counitIso.hom.app (A.obj.obj i) := rfl

@[simp] theorem cartesianEquivalence_counit_inv_app (A : CartesianOver q K) (i : I) :
    ((cartesianEquivalence p q K e hf hg hunit hcounit hforward hbackward).counitIso.inv.app A).hom.app i =
      e.counitIso.inv.app (A.obj.obj i) := rfl

end SquareKit.BasedDiagram
