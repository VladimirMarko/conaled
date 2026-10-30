import SquareKit.ListInitial.Fusion
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

noncomputable section
namespace SquareKit.ListInitial.Presheaves
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {J : Type} [Category.{0} J]

/-- Pointwise lists, with restriction mapping every entry. -/
def listObject (A : J ⥤ Type) : J ⥤ Type where
  obj j := List (A.obj j)
  map f := ↾List.map (A.map f)
  map_id j := by ext xs; simp
  map_comp f g := by ext xs; simp [List.map_map]

def nilMap (A : J ⥤ Type) : (𝟙_ (J ⥤ Type)) ⟶ listObject A where
  app _ := ↾fun _ => []

def consMap (A : J ⥤ Type) : A ⊗ listObject A ⟶ listObject A where
  app _ := ↾fun p => p.1 :: p.2

/-- The actual list algebra in the functor category. -/
def lists (A : J ⥤ Type) : Endofunctor.Algebra (signature A) where
  a := listObject A
  str := coprod.desc (nilMap A) (consMap A)

def nil {A : J ⥤ Type} (B : Endofunctor.Algebra (signature A)) (j : J) : B.a.obj j :=
  (coprod.inl ≫ B.str).app j PUnit.unit

def cons {A : J ⥤ Type} (B : Endofunctor.Algebra (signature A)) (j : J)
    (a : A.obj j) (b : B.a.obj j) : B.a.obj j := (coprod.inr ≫ B.str).app j (a,b)

theorem nil_natural {A : J ⥤ Type} (B : Endofunctor.Algebra (signature A))
    {j k : J} (q : j ⟶ k) : B.a.map q (nil B j) = nil B k := by
  have h := NatTrans.naturality_apply (coprod.inl ≫ B.str) q PUnit.unit
  exact h.symm

theorem cons_natural {A : J ⥤ Type} (B : Endofunctor.Algebra (signature A))
    {j k : J} (q : j ⟶ k) (a : A.obj j) (b : B.a.obj j) :
    B.a.map q (cons B j a b) = cons B k (A.map q a) (B.a.map q b) := by
  let t : A ⊗ B.a ⟶ B.a := coprod.inr ≫ B.str
  exact (congrArg (fun k : A.obj j × B.a.obj j ⟶ B.a.obj k => k.hom (a,b)) (t.naturality q)).symm

def fold {A : J ⥤ Type} (B : Endofunctor.Algebra (signature A)) (j : J) :
    List (A.obj j) → B.a.obj j
  | [] => nil B j
  | a :: xs => cons B j a (fold B j xs)

/-- Component recursion assembles into a natural transformation. -/
def foldMap {A : J ⥤ Type} (B : Endofunctor.Algebra (signature A)) : listObject A ⟶ B.a where
  app j := ↾fold B j
  naturality j k q := by
    ext xs
    change fold B k (xs.map (A.map q)) = B.a.map q (fold B j xs)
    induction xs with
    | nil => exact (nil_natural B q).symm
    | cons a xs ih => simpa only [List.map_cons, fold, ih] using
        (cons_natural B q a (fold B j xs)).symm

def foldMorphism {A : J ⥤ Type} (B : Endofunctor.Algebra (signature A)) : lists A ⟶ B where
  f := foldMap B
  h := by
    apply coprod.hom_ext
    · simp only [signature, lists, coprod.inl_map_assoc, Category.id_comp, coprod.inl_desc_assoc]
      ext j x
      cases x
      rfl
    · simp only [signature, lists, coprod.inr_map_assoc, coprod.inr_desc_assoc]
      ext j x
      rfl

/-- Uniqueness is equality of natural transformations, not just chosen stages. -/
def initial (A : J ⥤ Type) : IsInitial (lists A) :=
  IsInitial.ofUniqueHom (fun B => foldMorphism B) (by
    intro B m
    apply Endofunctor.Algebra.Hom.ext
    ext j xs
    have hn := congrArg (fun k : (signature A).obj (listObject A) ⟶ B.a =>
      (coprod.inl ≫ k).app j PUnit.unit) m.h
    have hc := fun a xs => congrArg (fun k : (signature A).obj (listObject A) ⟶ B.a =>
      (coprod.inr ≫ k).app j (a,xs)) m.h
    induction xs with
    | nil => simpa [signature, lists, foldMorphism, foldMap, nilMap, fold, nil] using hn.symm
    | cons a xs ih =>
      have step := (hc a xs).symm
      simp only [signature, lists, coprod.inr_map_assoc, coprod.inr_desc_assoc] at step
      change m.f.app j (a :: xs) = cons B j a (m.f.app j xs) at step
      change m.f.app j (a :: xs) = cons B j a (fold B j xs)
      rw [step]
      exact congrArg (cons B j a) ih)


/-- Beta at a component follows from the closed adjunction's universal property. -/
theorem curry_apply {I X Y : J ⥤ Type} (k : I ⊗ X ⟶ Y) (j : J)
    (i : I.obj j) (x : X.obj j) :
    (((curry k).app j x).app j (𝟙 j)).hom i = k.app j (i,x) := by
  exact congrArg (fun t : I ⊗ X ⟶ Y => (t.app j).hom (i,x)) (uncurry_curry k)

/-- Component equation for the constructed action; evaluation is not asserted
 to preserve exponentials. The exponential used here is Mathlib's natural
 family of maps along all arrows out of a stage. -/
theorem run_eq {A I : J ⥤ Type} (f : I ⊗ A ⟶ I) (j : J)
    (i : I.obj j) (xs : List (A.obj j)) :
    (run (initial A) f).app j (i,xs) =
      xs.foldl (fun r a => f.app j (r,a)) i := by
  have eq := congrArg Endofunctor.Algebra.Hom.f ((initial A).hom_ext
    ((initial A).to (actionAlgebra f (𝟙 I))) (foldMorphism _))
  unfold run
  rw [eq]
  change ((fold (actionAlgebra f (𝟙 I)) j xs).app j (𝟙 j)).hom i = _
  induction xs generalizing i with
  | nil =>
    simp only [fold, nil, actionAlgebra, coprod.inl_desc, curry_apply]
    rfl
  | cons a xs ih =>
    simp only [fold, cons, actionAlgebra, coprod.inr_desc, List.foldl_cons,
      consAction, curry_apply]
    exact ih (f.app j (i,a))

/-- This application invokes the shared categorical theorem, with no new
 stagewise fusion induction. -/
theorem foldl_fusion {A I S : J ⥤ Type} (f : I ⊗ A ⟶ I) (g : S ⊗ A ⟶ S)
    (h : I ⟶ S) (square : f ≫ h = (h ⊗ₘ 𝟙 A) ≫ g)
    (j : J) (i : I.obj j) (xs : List (A.obj j)) :
    h.app j (xs.foldl (fun r a => f.app j (r,a)) i) =
      xs.foldl (fun s a => g.app j (s,a)) (h.app j i) := by
  have eq := fusion (initial A) f g h square
  have value := congrArg (fun k : I ⊗ listObject A ⟶ S => (k.app j).hom (i,xs)) eq
  change h.app j ((run (initial A) f).app j (i,xs)) =
    (run (initial A) g).app j (h.app j i,xs) at value
  simpa only [run_eq] using value

end SquareKit.ListInitial.Presheaves
