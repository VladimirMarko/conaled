import SquareKit.ListInitial.Fusion
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.Types.Coproducts

noncomputable section
namespace SquareKit.ListInitial.Types
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w

/-- Ordinary lists with the empty/cons signature. -/
def lists (A : Type u) : Endofunctor.Algebra (signature (C := Type u) A) where
  a := List A
  str := coprod.desc (↾fun _ => []) (↾fun p => p.1 :: p.2)

def nil {A : Type u} (B : Endofunctor.Algebra (signature (C := Type u) A)) : B.a :=
  (coprod.inl ≫ B.str) PUnit.unit

def cons {A : Type u} (B : Endofunctor.Algebra (signature (C := Type u) A))
    (a : A) (b : B.a) : B.a := (coprod.inr ≫ B.str) (a,b)

def fold {A : Type u} (B : Endofunctor.Algebra (signature (C := Type u) A)) : List A → B.a
  | [] => nil B
  | a :: xs => cons B a (fold B xs)

def foldMorphism {A : Type u} (B : Endofunctor.Algebra (signature (C := Type u) A)) : lists A ⟶ B where
  f := ↾fold B
  h := by
    apply coprod.hom_ext
    · ext x
      cases x
      simp [signature, lists, nil, fold]
    · ext x
      simp [signature, lists, cons, fold]
      rfl

/-- Host induction establishes the model's initiality, not application fusion. -/
def initial (A : Type u) : IsInitial (lists A) :=
  IsInitial.ofUniqueHom (fun B => foldMorphism B) (by
    intro B m
    apply Endofunctor.Algebra.Hom.ext
    apply ConcreteCategory.hom_ext
    intro xs
    have hn := congrArg (fun k : (signature A).obj (List A) ⟶ B.a => (coprod.inl ≫ k) PUnit.unit) m.h
    have hc := fun a b => congrArg (fun k : (signature A).obj (List A) ⟶ B.a => (coprod.inr ≫ k) (a,b)) m.h
    induction xs with
    | nil => simpa [signature, lists, foldMorphism, fold, nil] using hn.symm
    | cons a xs ih =>
      have step := (hc a xs).symm
      simp only [signature, lists, coprod.inr_desc_assoc, coprod.inr_map_assoc] at step
      change m.f (a :: xs) = cons B a (m.f xs) at step
      change m.f (a :: xs) = cons B a (fold B xs)
      rw [step]
      exact congrArg (cons B a) ih)

/-- Evaluation of the constructed continuation action is the ordinary left fold. -/
theorem run_eq {A I : Type u} (f : I → A → I) (i : I) (xs : List A) :
    run (initial A) (↾fun p => f p.1 p.2) (i,xs) = xs.foldl f i := by
  have unique := (initial A).hom_ext
    ((initial A).to (actionAlgebra (↾fun p : I × A => f p.1 p.2) (𝟙 I)))
    (foldMorphism _)
  have eq := congrArg Endofunctor.Algebra.Hom.f unique
  change (((initial A).to (actionAlgebra (↾fun p : I × A => f p.1 p.2) (𝟙 I))).f xs : I ⟶ I).hom i = _
  rw [eq]
  change (fold (actionAlgebra (↾fun p : I × A => f p.1 p.2) (𝟙 I)) xs : I ⟶ I).hom i = _
  induction xs generalizing i with
  | nil => simp [fold, nil, actionAlgebra]; rfl
  | cons a xs ih =>
    simp only [fold, cons, actionAlgebra, coprod.inr_desc, List.foldl_cons]
    change (fold (actionAlgebra (↾fun p : I × A => f p.1 p.2) (𝟙 I)) xs : I ⟶ I).hom (f i a) = _
    exact ih (f i a)


/-- Ordinary fusion is a specialization of the categorical theorem. -/
theorem foldl_fusion {A I S : Type u} (f : I → A → I) (g : S → A → S)
    (h : I → S) (square : ∀ i a, h (f i a) = g (h i) a)
    (i : I) (xs : List A) : h (xs.foldl f i) = xs.foldl g (h i) := by
  have eq := fusion (initial A) (↾fun p => f p.1 p.2) (↾fun p => g p.1 p.2)
    (↾h) (by ext p; exact square p.1 p.2)
  have value := congrArg (fun k : I × List A ⟶ S => k (i,xs)) eq
  change h (run (initial A) (↾fun p => f p.1 p.2) (i,xs)) =
    run (initial A) (↾fun p => g p.1 p.2) (h i,xs) at value
  simpa only [run_eq] using value

/-- Forgetting the valid-state run also uses the same categorical fusion proof. -/
theorem reachable {A R S : Type u} (f : R → A → R) (g : S → A → S)
    (h : R → S) (P : R → Prop) (e : R) (base : P e)
    (closed : ∀ r a, P r → P (f r a))
    (square : ∀ r a, P r → h (f r a) = g (h r) a) (xs : List A) :
    h (xs.foldl f e) = xs.foldl g (h e) := by
  let fi : {r // P r} → A → {r // P r} := fun r a => ⟨f r.1 a, closed r.1 a r.2⟩
  have forget := foldl_fusion fi f Subtype.val (fun _ _ => rfl) ⟨e,base⟩ xs
  have observe := foldl_fusion fi g (fun r => h r.1)
    (fun r a => square r.1 a r.2) ⟨e,base⟩ xs
  change h (Subtype.val (xs.foldl fi ⟨e,base⟩)) = _ at observe
  rw [forget] at observe
  exact observe

/-- Universe lifting changes representation, not the fold's computation. -/
theorem foldl_ulift {A : Type u} {R : Type v} (f : R → A → R)
    (xs : List A) (r : R) :
    (xs.map (ULift.up : A → ULift.{w} A)).foldl
      (fun r a => ULift.up (f r.down a.down) : ULift.{w} R → ULift.{w} A → ULift.{w} R)
      (ULift.up r) = ULift.up (xs.foldl f r) := by
  induction xs generalizing r with
  | nil => rfl
  | cons a xs ih => exact ih (f r a)

/-- The original theorem's independent universes and hypotheses are retained. -/
theorem foldl_reachable {A : Type u} {R : Type v} {S : Type w}
    (f : R → A → R) (g : S → A → S) (h : R → S) (P : R → Prop)
    (e : R) (base : P e) (closed : ∀ r a, P r → P (f r a))
    (square : ∀ r a, P r → h (f r a) = g (h r) a) (xs : List A) :
    h (xs.foldl f e) = xs.foldl g (h e) := by
  have eq := reachable
    (A := ULift.{max u v w} A) (R := ULift.{max u v w} R) (S := ULift.{max u v w} S)
    (fun r a => ⟨f r.down a.down⟩) (fun s a => ⟨g s.down a.down⟩)
    (fun r => ⟨h r.down⟩) (fun r => P r.down) ⟨e⟩ base
    (fun r a hr => closed r.down a.down hr)
    (fun r a hr => congrArg ULift.up (square r.down a.down hr)) (xs.map ULift.up)
  simpa only [foldl_ulift, ULift.up.injEq] using eq

end SquareKit.ListInitial.Types
