# Checked assessment probes

These sources were checked independently against the pinned Mathlib before
implementation. They test selection claims, not the completed adapter.

## Contract

```lean
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

noncomputable section
open CategoryTheory
open CategoryTheory.Functor

universe u v a b i j
variable {C : Type u} [Category.{v} C] {D : Type a} [Category.{b} D]
variable {I : Type i} [Category.{j} I]

abbrev fixedDiagrams (p : C ⥤ D) (K : I ⥤ D) :=
  Functor.Fiber ((whiskeringRight I C D).obj p) K

example (p : C ⥤ D) (K : I ⥤ D) : Category (fixedDiagrams p K) := inferInstance

example (p : C ⥤ D) (K : I ⥤ D) {A B : fixedDiagrams p K}
    (η : A ⟶ B) :
    whiskerRight η.val p = eqToHom (A.property.trans B.property.symm) := by
  haveI := η.property
  simpa using IsHomLift.fac' ((whiskeringRight I C D).obj p) (𝟙 K) η.val

abbrev fixedBased (p : C ⥤ D) (K : I ⥤ D) :=
  BasedFunctor (BasedCategory.ofFunctor K) (BasedCategory.ofFunctor p)

example (p : C ⥤ D) (K : I ⥤ D) : Category (fixedBased p K) := inferInstance

-- A full subcategory selected only by object projection admits this arrow.
def boolCollapse : Bool ⟶ Bool := TypeCat.ofHom (fun _ => false)

example : ¬ (𝟭 (Type)).IsHomLift (𝟙 Bool) boolCollapse := by
  intro h
  haveI := h
  have he := IsHomLift.eq_of_isHomLift (𝟭 (Type)) (𝟙 Bool) boolCollapse
  have hc := congrArg (fun f : Bool ⟶ Bool => f true) he
  cases hc


-- The same rejection directly in the functor category, at an inhabited index category.
example (i₀ : I) :
    ¬ ((whiskeringRight I (Type) (Type)).obj (𝟭 (Type))).IsHomLift
      (𝟙 ((Functor.const I).obj Bool)) ((Functor.const I).map boolCollapse) := by
  intro h
  haveI := h
  have he := IsHomLift.eq_of_isHomLift
    ((whiskeringRight I (Type) (Type)).obj (𝟭 (Type)))
    (a := (Functor.const I).obj Bool) (b := (Functor.const I).obj Bool)
    (𝟙 ((Functor.const I).obj Bool)) ((Functor.const I).map boolCollapse)
  have hc := congrArg (fun f : Bool ⟶ Bool => f true) (NatTrans.congr_app he i₀)
  cases hc

universe u' v'
variable {C' : Type u'} [Category.{v'} C']

-- Composition already transports all based diagrams and all their vertical maps.
example (p : C ⥤ D) (q : C' ⥤ D) (K : I ⥤ D)
    (F : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (A : fixedBased p K) : fixedBased q K := BasedFunctor.comp A F

example (p : C ⥤ D) (q : C' ⥤ D) (K : I ⥤ D)
    (F : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    {A B : fixedBased p K} (η : A ⟶ B) :
    BasedFunctor.comp A F ⟶ BasedFunctor.comp B F :=
  BasedCategory.whiskerRight η F

```

## Use

```lean
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u v w a b i j
variable {C : Type u} [Category.{v} C]
variable {S : Type w} [Category.{a} S]
variable {D : Type b} [Category.{i} D]
variable {I : Type j} [Category I]

abbrev Systems (p : C ⥤ D) (K : I ⥤ D) :=
  Functor.Fiber ((whiskeringRight I C D).obj p) K

-- The precise proposed target types use Mathlib's existing categorical fiber.
def systemsObject (p : C ⥤ D) (K : I ⥤ D) (A : I ⥤ C) (hA : A ⋙ p = K) :
    Systems p K := ⟨A, hA⟩

-- The unrestricted equivalence already exists without additional infrastructure.
def unrestricted (E : C ≌ S) : (I ⥤ C) ≌ (I ⥤ S) := E.congrRight

-- These are consumers of a proposed fixed-context equivalence, not a construction
-- of that equivalence. Neither proof presumes equalizers exist in either category.
def equalizerForward (p : C ⥤ D) (q : S ⥤ D) (K : I ⥤ D)
    (E : Systems p K ≌ Systems q K)
    {A X Y : Systems p K} {f g : X ⟶ Y} {h : A ⟶ X}
    (w : h ≫ f = h ≫ g) (hlim : IsLimit (Fork.ofι h w)) :
    IsLimit (Fork.ofι (E.functor.map h)
      (by simp only [← Functor.map_comp, w]) : Fork (E.functor.map f) (E.functor.map g)) :=
  isLimitForkMapOfIsLimit E.functor w hlim

-- Reflection permits proving the code universal property on the sheaf side.
def equalizerBackward (p : C ⥤ D) (q : S ⥤ D) (K : I ⥤ D)
    (E : Systems p K ≌ Systems q K)
    {A X Y : Systems p K} {f g : X ⟶ Y} {h : A ⟶ X}
    (w : h ≫ f = h ≫ g)
    (hlim : IsLimit (Fork.ofι (E.functor.map h)
      (by simp only [← Functor.map_comp, w]) : Fork (E.functor.map f) (E.functor.map g))) :
    IsLimit (Fork.ofι h w) :=
  isLimitOfIsLimitForkMap E.functor w hlim

-- Existence transfer requires a separate existence assumption.
example (p : C ⥤ D) (q : S ⥤ D) (K : I ⥤ D)
    (E : Systems p K ≌ Systems q K) [HasEqualizers (Systems q K)] :
    HasEqualizers (Systems p K) :=
  Adjunction.hasLimitsOfShape_of_equivalence E.functor

```

## Alternatives

```lean
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

open CategoryTheory
set_option autoImplicit false
universe u v x y z t i j
namespace Alternatives
variable {D : Type u} [Category.{v} D]
variable {X : Type x} [Category.{y} X] {Y : Type z} [Category.{t} Y]
variable {I : Type i} [Category.{j} I]

abbrev Diagrams (p : X ⥤ D) (K : I ⥤ D) :=
  BasedFunctor (BasedCategory.ofFunctor K) (BasedCategory.ofFunctor p)

abbrev FiberDiagrams (p : X ⥤ D) (K : I ⥤ D) :=
  Functor.Fiber ((Functor.whiskeringRight I X D).obj p) K

example (p : X ⥤ D) (K : I ⥤ D) : Category (Diagrams p K) := inferInstance
example (p : X ⥤ D) (K : I ⥤ D) : Category (FiberDiagrams p K) := inferInstance

-- Arbitrary vertical transformations are morphisms of the existing based-functor category.
def diagramHom (p : X ⥤ D) (K : I ⥤ D) (A B : Diagrams p K)
    (η : A.toFunctor ⟶ B.toFunctor)
    (hη : ∀ a, p.IsHomLift (𝟙 (K.obj a)) (η.app a)) : A ⟶ B :=
  { toNatTrans := η, isHomLift' := hη }

def post (p : X ⥤ D) (q : Y ⥤ D) (K : I ⥤ D)
    (F : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q)) :
    Diagrams p K ⥤ Diagrams q K where
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

example (p : X ⥤ D) (q : Y ⥤ D) (K : I ⥤ D)
    (F : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    {A B : Diagrams p K} (η : A ⟶ B) (a : I) :
    ((post p q K F).map η).app a = F.map (η.app a) := rfl

end Alternatives

namespace Alternatives
open Functor
abbrev Star := Discrete PUnit
abbrev star : Star := ⟨PUnit.unit⟩
abbrev pointProjection : Type ⥤ Star := (const (Type)).obj star
abbrev pointDiagram : Star ⥤ Star := (const Star).obj star

def boolSection : Diagrams pointProjection pointDiagram where
  toFunctor := (const Star).obj Bool
  w := rfl

def collapse : boolSection ⟶ boolSection where
  toNatTrans := { app := fun _ => TypeCat.ofHom (fun _ => false) }
  isHomLift' a := by
    apply IsHomLift.of_fac _ _ _ rfl rfl
    rfl

example : collapse ≫ collapse = collapse := by
  apply BasedNatTrans.ext
  rfl

theorem collapse_not_id : collapse ≠ 𝟙 boolSection := by
  intro h
  have hh := congrArg (fun f : boolSection ⟶ boolSection => (show Bool → Bool from (f.app star).hom.toFun) true) h
  change false = true at hh
  cases hh

theorem collapse_not_iso : ¬ IsIso collapse := by
  intro h
  have hcomp : collapse ≫ collapse = (𝟙 boolSection) ≫ collapse := by
    rw [Category.id_comp]
    apply BasedNatTrans.ext
    rfl
  exact collapse_not_id ((cancel_mono collapse).mp hcomp)
end Alternatives

```
