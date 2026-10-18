import Applications.Intervals.ConditionedComposition
import Examples.InternalAuthoring
import Examples.PresheafInternal
import SquareKit.Internal.PresheafFrobenius

/-! Checked interval, capture, empty-witness, presheaf, and mixed-style cases for #50. -/
namespace Examples.Frobenius
open SquareKit.Internal Relational IntervalAnalysis

-- An input admits the interval [-2,3]; realization adds one to a contained point.
def enclosure : Unit → Interval → Prop := fun _ I => I = ⟨-2, 3⟩
def realize : ℚ → ℚ → Prop := fun x z => z = x + 1

theorem accepted : ∃ I, (0 : ℚ) ≤ 2 ∧ enclosure () I ∧ compRel representation.Rel realize I 2 := by
  apply (nonnegative_composition enclosure realize () 2).mp
  refine ⟨by norm_num, 1, ⟨⟨-2, 3⟩, rfl, ?_⟩, ?_⟩
  · norm_num [representation, Contains]
  · norm_num [realize]

-- Containment and realization are satisfiable here, but the output condition fails.
theorem negative_realization : compRel (compRel enclosure representation.Rel) realize () (-1) := by
  refine ⟨-2, ⟨⟨-2, 3⟩, rfl, ?_⟩, ?_⟩
  · norm_num [representation, Contains]
  · norm_num [realize]

theorem rejected_negative :
    ¬ ∃ I, (0 : ℚ) ≤ -1 ∧ enclosure () I ∧ compRel representation.Rel realize I (-1) := by
  intro h
  have nonnegative := ((nonnegative_composition enclosure realize () (-1)).mpr h).1
  norm_num at nonnegative

-- A positive endpoint outside the realized enclosure must also be rejected.
theorem rejected_outside :
    ¬ ∃ I, (0 : ℚ) ≤ 5 ∧ enclosure () I ∧ compRel representation.Rel realize I 5 := by
  intro h
  obtain ⟨_, x, ⟨I, hI, hx⟩, hz⟩ := (nonnegative_composition enclosure realize () 5).mpr h
  change I = ⟨-2, 3⟩ at hI
  subst I
  change -2 ≤ x ∧ x ≤ 3 at hx
  change 5 = x + 1 at hz
  linarith

-- Empty intermediate carriers require no Nonempty assumptions.
example (R : Unit → Empty → Prop) (S : Empty → ℚ → Prop) :
    ¬ ∃ b, (0 : ℚ) ≤ 2 ∧ R () b ∧ compRel S realize b 2 := by
  intro h
  obtain ⟨_, _, ⟨b, _, _⟩, _⟩ := (compRel_condition R S realize (fun z => 0 ≤ z) () 2).mpr h
  exact nomatch b

namespace Capture
inductive ValueSort where | value
abbrev Arrow (_ _ : ValueSort) := PEmpty
inductive Relation : ValueSort → ValueSort → Type where | nonnegative : Relation .value .value

def model : Interpretation Arrow Relation where
  Carrier _ := ℚ
  arrow f := nomatch f
  relation _ x _ := 0 ≤ x

def condition : Formula Arrow [.value] Relation :=
  .atom .nonnegative (.var .zero) (.var .zero)

def predicate : Formula Arrow [.value, .value] Relation :=
  .eq (.var .zero) (.var (.succ .zero))

def environment (q : ℚ) : Env model [.value] :=
  Env.extend q (fun {_} (i : Var [] _) => nomatch i)

-- Free output and bound witness have the same sort. The condition stays on z.
theorem same_sort (z : ℚ) :
    (0 ≤ z ∧ ∃ x : ℚ, x = z) ↔ ∃ x : ℚ, 0 ≤ z ∧ x = z :=
  SquareKit.Internal.Frobenius.inSet condition predicate model (environment z)

-- A condition accidentally placed on the witness would accept this false case.
def reflexive : Formula Arrow [.value, .value] Relation := .eq (.var .zero) (.var .zero)

theorem shifted_rejects :
    ¬ (Formula.ex (.conj condition.shift reflexive)).eval model (environment (-1)) := by
  intro h
  have hh := (SquareKit.Internal.Frobenius.inSet condition reflexive model (environment (-1))).mpr h
  change (0 : ℚ) ≤ -1 ∧ _ at hh
  norm_num at hh

theorem captured_accepts :
    (Formula.ex (.conj (.atom Relation.nonnegative (.var .zero) (.var .zero)) reflexive)).eval
      model (environment (-1)) := by
  exact ⟨(0 : ℚ), le_rfl, rfl⟩

-- The derived sequent remains usable under arbitrary substitution and weakening.
example {Δ : List ValueSort} (σ : SquareKit.Internal.Sub Arrow [.value] Δ) :
    Derives ((Formula.conj condition (.ex predicate)).subst σ)
      ((Formula.ex (.conj condition.shift predicate)).subst σ) :=
  Rules.substitute σ (SquareKit.Internal.Frobenius.forward condition predicate)

example : Derives ((Formula.conj condition (.ex predicate)).shift (s := .value))
    (Formula.ex (.conj condition.shift predicate)).shift :=
  Rules.weaken (SquareKit.Internal.Frobenius.forward condition predicate)
end Capture

namespace Fiber
open CategoryTheory Opposite SquareKit.Internal.Presheaf Examples.PresheafInternal

-- Both free variables and the new witness have the same syntactic sort.
def witnessBody : Formula FunctionSymbol [.value, .value, .value] Relation :=
  .atom .le (.var .zero) (.var (.succ .zero))

theorem fine_equivalence :
    ((3 : Nat) ≤ 4 ∧ ∃ x : Nat × Nat, x.1 ≤ 3) ↔
      ∃ x : Nat × Nat, (3 : Nat) ≤ 4 ∧ x.1 ≤ 3 :=
  frobenius_evaluation relationalModel orderedPair witnessBody (op .fine)
    (pairEnv (op .fine) (3, 9) (4, 0))

theorem fine_witness :
    (relationalModel.formula (.ex (.conj orderedPair.shift witnessBody))).obj
      (op .fine) (pairEnv (op .fine) (3, 9) (4, 0)) := by
  apply (relationalModel.evaluation _ _ _).mpr
  exact fine_equivalence.mp ⟨by decide, (2, 7), by decide⟩

theorem restricted_witness :
    (relationalModel.formula (.ex (.conj orderedPair.shift witnessBody))).obj
      (op .coarse) (relationalModel.restrict drop (pairEnv (op .fine) (3, 9) (4, 0))) :=
  relationalModel.formula_restrict _ drop _ fine_witness

example : relationalModel.formula (.ex (.conj orderedPair.shift witnessBody)) =
    relationalModel.formula orderedPair ⊓ (relationalModel.formula witnessBody).image relationalModel.projection :=
  frobenius_semantic_comparison relationalModel orderedPair witnessBody
end Fiber

-- Local notation, existing typeclass arithmetic, ordinary calls, and both
-- proof styles coexist. No notation or instance escapes this section.
section Mixed
local infix:45 " ⊢₅₀ " => Derives
example : Capture.condition ⊢₅₀ Capture.condition := Rules.hypothesis
example : (Formula.conj Capture.condition (.ex Capture.predicate)) ⊢₅₀
    (.ex (.conj Capture.condition.shift Capture.predicate)) :=
  InternalAuthoring.Helpers.frobenius_forward _ _
example : (Formula.conj Capture.condition (.ex Capture.predicate)) ⊢₅₀
    (.ex (.conj Capture.condition.shift Capture.predicate)) :=
  InternalAuthoring.Direct.frobenius_forward _ _
example : (∃ b : ℚ, b = 3 + 1 ∧ 8 = b * 2) :=
  (Graph.inSet (fun x : ℚ => x + 1) (fun x => x * 2) 3 8).mpr (by norm_num)
example : Contains (add (singleton 1) (singleton 2)) 3 :=
  by
    convert add_contains (singleton_contains 1) (singleton_contains 2) using 1
    norm_num
end Mixed
end Examples.Frobenius
