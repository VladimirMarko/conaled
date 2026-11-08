import SquareKit.DependentBaseChange
import SquareKit.AdjointComparison
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! Selected dependent sums use the existing slice map/pullback adjunction.
The comparisons below retain an element, rather than only its inhabitation. -/
noncomputable section
namespace SquareKit.IndexedSumBaseChange
open CategoryTheory Limits ConcreteCategory
universe u v

section Category
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {A B A' B' : C} {f : A ⟶ B} {g : B' ⟶ B} {f' : A' ⟶ B'} {g' : A' ⟶ A}

/-- A commuting square always gives this forward sum comparison. -/
def comparison (w : f' ≫ g = g' ≫ f) :
    Over.pullback f' ⋙ Over.map g' ⟶ Over.map g ⋙ Over.pullback f where
  app X := Over.homMk (pullback.lift (pullback.fst X.hom f')
    (pullback.snd X.hom f' ≫ g') (by
      change _ ≫ (X.hom ≫ g) = _
      rw [← Category.assoc, pullback.condition, Category.assoc, w, Category.assoc])) (by simp)
  naturality X Y k := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [Over.pullback, Over.map, Category.assoc]

/-- For a pullback square the map is exactly the existing canonical iso. -/
theorem comparison_eq (h : IsPullback f' g' g f) :
    comparison h.w = (DependentBaseChange.leftComparison h).hom := by
  apply NatTrans.ext
  funext X
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;> simp [comparison]

/-- Arbitrary generalized selected values keep both their value and base. -/
theorem selected (h : IsPullback f' g' g f) (X : Over B')
    {T : C} (x : T ⟶ X.left) (a : T ⟶ A') (e : x ≫ X.hom = a ≫ f') :
    pullback.lift x a e ≫ ((DependentBaseChange.leftComparison h).hom.app X).left =
      pullback.lift x (a ≫ g') (by
        change x ≫ (X.hom ≫ g) = _
        rw [← Category.assoc, e, Category.assoc, h.w, Category.assoc]) := by
  apply pullback.hom_ext <;> simp [Category.assoc]
end Category

section Types
variable {A B : Type u} (f : A ⟶ B) (X : Over B)

/-- Independent selected fiber contract. The index and the complete value remain. -/
abbrev Fiber (a : A) := { x : X.left // X.hom x = f a }

/-- Encode the independent fiber in the actual chosen categorical pullback. -/
def encode (a : A) (x : Fiber f X a) : pullback X.hom f :=
  (Types.pullbackIsoPullback X.hom f).inv ⟨(x.val, a), x.property⟩

@[simp] theorem encode_value (a : A) (x : Fiber f X a) :
    pullback.fst X.hom f (encode f X a x) = x.val := by
  exact congr_hom (Types.pullbackIsoPullback_inv_fst X.hom f) _

@[simp] theorem encode_base (a : A) (x : Fiber f X a) :
    pullback.snd X.hom f (encode f X a x) = a := by
  exact congr_hom (Types.pullbackIsoPullback_inv_snd X.hom f) _
/-- Reindexing an actual slice map preserves its specified value map. -/
theorem reindex_value {X Y : Over B} (k : X ⟶ Y) (x : pullback X.hom f) :
    pullback.fst Y.hom f (((Over.pullback f).map k).left x) =
      k.left (pullback.fst X.hom f x) := by
  have e : ((Over.pullback f).map k).left ≫ pullback.fst Y.hom f =
      pullback.fst X.hom f ≫ k.left := by simp [Over.pullback]
  exact congr_hom e x
theorem reindex_base {X Y : Over B} (k : X ⟶ Y) (x : pullback X.hom f) :
    pullback.snd Y.hom f (((Over.pullback f).map k).left x) =
      pullback.snd X.hom f x :=
  congr_hom (Over.w ((Over.pullback f).map k)) x
end Types

section SelectedComparison
variable {A B A' B' : Type u} {f : A ⟶ B} {g : B' ⟶ B} {f' : A' ⟶ B'} {g' : A' ⟶ A}
variable (h : IsPullback f' g' g f) (X : Over B')

/-- The canonical sum/base-change isomorphism on an independently selected fiber. -/
def transport (a : A') (x : Fiber f' X a) :
    pullback (X.hom ≫ g) f :=
  ((DependentBaseChange.leftComparison h).hom.app X).left (encode f' X a x)

@[simp] theorem transport_value (a : A') (x : Fiber f' X a) :
    pullback.fst (X.hom ≫ g) f (transport h X a x) = x.val := by
  have e := congr_hom (DependentBaseChange.leftComparison_fst h X) (encode f' X a x)
  exact e.trans (encode_value f' X a x)

@[simp] theorem transport_base (a : A') (x : Fiber f' X a) :
    pullback.snd (X.hom ≫ g) f (transport h X a x) = g' a := by
  have e := congr_hom (DependentBaseChange.leftComparison_snd h X) (encode f' X a x)
  exact e.trans (congrArg g' (encode_base f' X a x))
end SelectedComparison
end SquareKit.IndexedSumBaseChange
