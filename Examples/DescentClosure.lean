import SquareKit.GrothendieckEquivalence
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.Int.Defs

/-! Context extension preserves equivalences without identifying presentations;
identity descent cannot forget distinguishable arrows. -/
noncomputable section
namespace Examples.DescentClosure
open CategoryTheory SquareKit.GrothendieckEquivalence
set_option backward.isDefEq.respectTransparency false

inductive Two where
  | left
  | right
  deriving DecidableEq

instance : Groupoid Two where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  inv _ := PUnit.unit

def collapse : Two ⥤ Discrete PUnit :=
  (Functor.const Two).obj (Discrete.mk PUnit.unit)

instance : collapse.Full where
  map_surjective _ := ⟨PUnit.unit, Subsingleton.elim _ _⟩
instance : collapse.Faithful where
  map_injective := by intro X Y f g _; exact @Subsingleton.elim PUnit inferInstance f g
instance : collapse.EssSurj where
  mem_essImage _ := ⟨Two.left, ⟨eqToIso (Subsingleton.elim _ _)⟩⟩
instance : collapse.IsEquivalence where

/-- An equivalence can collapse two distinct object representations. -/
theorem collapse_not_object_injective : ¬ Function.Injective collapse.obj := by
  intro h
  have he : Two.left = Two.right := h rfl
  cases he

abbrev twoFamily : Discrete Bool ⥤ Cat :=
  (Functor.const (Discrete Bool)).obj (Cat.of Two)
abbrev oneFamily : Discrete Bool ⥤ Cat :=
  (Functor.const (Discrete Bool)).obj (Cat.of (Discrete PUnit))

def collapseFamily : twoFamily ⟶ oneFamily where
  app _ := collapse.toCatHom
  naturality {_ _} _ := rfl

instance (x : Discrete Bool) : (collapseFamily.app x).toFunctor.IsEquivalence :=
  inferInstanceAs collapse.IsEquivalence

/-- Both context objects remain available, while each fiber changes from two
isomorphic representatives to one. No bijection of fiber objects is needed. -/
def extensionComparison : Grothendieck twoFamily ≌ Grothendieck oneFamily :=
  fiberEquivalence collapseFamily

example : (extensionComparison.functor.obj ⟨Discrete.mk false, Two.left⟩).base =
    Discrete.mk false := rfl

example : extensionComparison.functor.obj ⟨Discrete.mk true, Two.left⟩ =
    extensionComparison.functor.obj ⟨Discrete.mk true, Two.right⟩ := rfl

abbrev Loops := SingleObj (Multiplicative ℤ)
abbrev zeroLoop : (SingleObj.star (Multiplicative ℤ)) ⟶ SingleObj.star (Multiplicative ℤ) :=
  Multiplicative.ofAdd 0
abbrev oneLoop : (SingleObj.star (Multiplicative ℤ)) ⟶ SingleObj.star (Multiplicative ℤ) :=
  Multiplicative.ofAdd 1

def forgetLoops : Loops ⥤ Discrete PUnit :=
  (Functor.const Loops).obj (Discrete.mk PUnit.unit)

/-- Equality of endpoints and of observations does not recover an arrow. -/
theorem forgetLoops_not_faithful : ¬ forgetLoops.Faithful := by
  intro h
  let := h
  have he : zeroLoop = oneLoop := forgetLoops.map_injective
    (show forgetLoops.map zeroLoop = forgetLoops.map oneLoop from rfl)
  exact (by change (0 : ℤ) ≠ 1; decide : zeroLoop ≠ oneLoop) he

/-- A valid identity comparison retains those same selected loops. -/
example : identityEquiv (𝟭 Loops) _ _ zeroLoop ≠ identityEquiv (𝟭 Loops) _ _ oneLoop :=
  fun h => (by change (0 : ℤ) ≠ 1; decide : zeroLoop ≠ oneLoop) ((identityEquiv (𝟭 Loops) _ _).injective h)

end Examples.DescentClosure
