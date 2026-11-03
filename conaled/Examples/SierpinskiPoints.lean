import SquareKit.Internal.SierpinskiGeneric
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Extensive

/-! The two Set points retain the noninvertible false-to-true transformation.
The generic arrow has empty domain and singleton codomain. -/
noncomputable section
set_option autoImplicit false
namespace Examples.SierpinskiPoints
open CategoryTheory CategoryTheory.Limits SquareKit.Internal
open SquareKit.Internal.ArrowGeometry
universe u

/-- The generic proposition in the arrow category of sets. -/
def generic : Arrow (Type u) := Arrow.mk (show PEmpty.{u + 1} ⟶ PUnit.{u + 1} from
  TypeCat.ofHom (fun x => PEmpty.elim x))

/-- False interprets the generic proposition as the empty set. -/
example : ((falsePoint (Type u)).inverseImage.obj generic) = PEmpty.{u + 1} := rfl

/-- True interprets the generic proposition as a singleton. -/
example : ((truePoint (Type u)).inverseImage.obj generic) = PUnit.{u + 1} := rfl

/-- Its component at every Set arrow is the original function. -/
example (a : Arrow (Type u)) : (falseToTrue (Type u)).app a = a.hom :=
  falseToTrue_app _ a

/-- Every commutative square is the naturality square of this transformation. -/
example {a b : Arrow (Type u)} (f : a ⟶ b) :
    f.left ≫ (falseToTrue (Type u)).app b =
      (falseToTrue (Type u)).app a ≫ f.right :=
  (falseToTrue (Type u)).naturality f

/-- A reverse geometric transformation would send the true witness to false. -/
theorem noReverse : IsEmpty (truePoint (Type u) ⟶ falsePoint (Type u)) :=
  ⟨fun α => PEmpty.elim (α.app generic PUnit.unit)⟩

/-- In particular the transformation retained by the interface is not invertible. -/
theorem falseToTrue_not_isIso : ¬ IsIso (falseToTrue (Type u)) := by
  intro h
  let := h
  exact noReverse.false (inv (falseToTrue (Type u)))

/-- The same obstruction holds in the category over the base. -/
theorem noReverseOver : IsEmpty (trueLift (Type u) ⟶ falseLift (Type u)) :=
  ⟨fun α => noReverse.false α.transformation⟩

/-- These are the actual models obtained by generic-model evaluation. -/
abbrev falseModel : MonoOver (⊤_ (Type u)) :=
  Sierpinski.interpret (falsePoint (Type u))
abbrev trueModel : MonoOver (⊤_ (Type u)) :=
  Sierpinski.interpret (truePoint (Type u))

def modelMap : falseModel ⟶ trueModel :=
  Sierpinski.interpretation.map (falseToTrue (Type u))

/-- The classifier evaluates the transformation to the generic arrow itself. -/
example : modelMap.hom.left = (Sierpinski.generic (Type u)).hom := rfl

/-- A reverse model map would produce an inhabitant of the initial set. -/
theorem noReverseModel : IsEmpty (trueModel.{u} ⟶ falseModel.{u}) := by
  refine ⟨fun q => ?_⟩
  let empty := (initialIsInitial (C := Type u)).to (PEmpty.{u + 1})
  let witness := ((Types.isTerminalPUnit.{u}).uniqueUpToIso terminalIsTerminal).hom PUnit.unit
  exact PEmpty.elim (empty (q.hom.left witness))

theorem modelMap_not_isIso : ¬ IsIso (modelMap.{u}) := by
  intro h
  let := h
  exact noReverseModel.false (inv modelMap)

/-- A groupoid cannot be equivalent to the full model category: it would make
false-to-true invertible. In particular, passing to a core loses information. -/
theorem noGroupoidEquivalence {C : Type*} [Groupoid C]
    (e : MonoOver (⊤_ (Type u)) ≌ C) : False := by
  have : IsIso (modelMap.{u}) := isIso_of_reflects_iso modelMap e.functor
  exact modelMap_not_isIso this

end Examples.SierpinskiPoints
