import SquareKit.Internal.ModalHigher.Keys
import Mathlib.CategoryTheory.Bicategory.Product

/-! Restricted access is factorization through an actual higher projection.
The Boolean is a discrete context coordinate, not part of the locked input. -/
namespace SquareKit.Internal.ModalHigher
open CategoryTheory Bicategory
open SquareKit.Internal.PathTransport
universe u
variable (G : Type u) [AddCommGroup G]
abbrev Full := Base G × LocallyDiscrete (Discrete Bool)
abbrev forgetHidden : StrictPseudofunctor (Full G) (Base G) := Bicategory.Prod.fst _ _
abbrev view (d : ℤ) := (forgetHidden G).comp (key (G := G) d)

def fullPoint (b : Bool) : Full G := (point G, ⟨⟨b⟩⟩)
def fullCell (b : Bool) (g : G) :
    (𝟙 (fullPoint G b)) ⟶ 𝟙 (fullPoint G b) :=
  (Multiplicative.ofAdd g, 𝟙 _)

/-- A full-context selected cell has the same locked view for either Boolean. -/
theorem view_cell (d : ℤ) (b : Bool) (g : G) :
    Multiplicative.toAdd ((view G d).map₂ (fullCell G b g)) = d • g := rfl

/-- The action on a view is evaluation of the reindexed higher family. -/
theorem full_action (d : ℤ) (b : Bool) (g : G) :
    Multiplicative.toAdd (((TwoFamily.reindex (view G d) (family G)).map₂
      (fullCell G b g)).app (fiberPoint G)).as = d • g := rfl

/-- An operation on selected labels is allowed only through the same projection. -/
def Factors {R : Type*} (op : Bool → G → R) : Prop :=
  ∃ locked : G → R, ∀ b g, op b g = locked g

omit [AddCommGroup G] in
theorem noninterference {R : Type*} {op : Bool → G → R} (h : Factors G op)
    (g : G) : op false g = op true g := by
  rcases h with ⟨locked, h⟩
  exact (h false g).trans (h true g).symm

/-- It is impossible to recover the hidden coordinate through this projection. -/
theorem hidden_recovery_rejected : ¬ Factors G (fun b (_ : G) => b) := by
  intro h
  have := noninterference G h 0
  cases this

/-- Choosing a locked cell according to the hidden Boolean fails factorization. -/
theorem dependent_substitution_rejected (g : G) (hg : g ≠ 0) :
    ¬ Factors G (fun b (_ : G) => if b then g else 0) := by
  intro h
  have he := noninterference G h 0
  simp only [Bool.false_eq_true, ↓reduceIte] at he
  exact hg he.symm

/-- The access contract on semantic substitutions is all-dimensional factorization. -/
def Allowed (σ : StrictPseudofunctor (Full G) (Base G)) : Prop :=
  ∃ locked : StrictPseudofunctor (Base G) (Base G),
    σ = (forgetHidden G).comp locked

theorem view_allowed (d : ℤ) : Allowed G (view G d) := ⟨key d, rfl⟩

theorem allowed_cell_factors {σ : StrictPseudofunctor (Full G) (Base G)}
    (h : Allowed G σ) : Factors G (fun b g =>
      Multiplicative.toAdd (σ.map₂ (fullCell G b g))) := by
  rcases h with ⟨locked, rfl⟩
  refine ⟨fun g => Multiplicative.toAdd (locked.map₂
    (show (𝟙 (point G)) ⟶ 𝟙 (point G) from Multiplicative.ofAdd g)), ?_⟩
  intro b g
  rfl

theorem allowed_boolean_choice_rejected (g : G) (hg : g ≠ 0) :
    ¬ ∃ σ : StrictPseudofunctor (Full G) (Base G), Allowed G σ ∧
      ∀ b, Multiplicative.toAdd (σ.map₂ (fullCell G b g)) = if b then g else 0 := by
  rintro ⟨σ, hσ, h⟩
  have he := noninterference G (allowed_cell_factors G hσ) g
  rw [h false, h true] at he
  simp only [Bool.false_eq_true, ↓reduceIte] at he
  exact hg he.symm

/-- Key compatibility is equality of whole higher functors. -/
theorem view_key (c d : ℤ) : (view G c).comp (key d) = view G (d * c) := by
  calc
    (view G c).comp (key d) =
        (forgetHidden G).comp ((key c).comp (key d)) :=
      StrictTwoTransformation.functor_ext rfl
    _ = view G (d * c) := congrArg (fun k => (forgetHidden G).comp k) (key_comp d c)

end SquareKit.Internal.ModalHigher
