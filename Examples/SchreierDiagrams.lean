import Applications.GroupActions.FiniteDiagram
import Examples.Schreier
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.IntervalCases

/-! Checked consumers for the finite diagrams: regular C3, natural S3 and an
ineffective S3 action. Generator indices 0 and 2 intentionally repeat (01). -/

open Quiver Schreier Schreier.FiniteDiagram SchreierExamples
namespace SchreierDiagrams

abbrev C3 := Multiplicative (Fin 3)
def cyclicVertices : Fin 3 ≃ C3 := Multiplicative.ofAdd
def cyclicGenerator : Fin 1 → C3 := fun _ => Multiplicative.ofAdd 1

theorem cyclic_targets :
    (row cyclicVertices cyclicGenerator 0 0).target = 1 ∧
    (row cyclicVertices cyclicGenerator 1 0).target = 2 ∧
    (row cyclicVertices cyclicGenerator 2 0).target = 0 := by decide

example (v : Fin 3) :
    (⟨v, (row cyclicVertices cyclicGenerator v 0).target, 0,
      Multiplicative.ofAdd 1⟩ : Row C3 3 1) ∈ rows cyclicVertices cyclicGenerator :=
  row_mem cyclicVertices cyclicGenerator v 0

example : rows cyclicVertices (Fin.elim0 : Fin 0 → C3) = [] := by
  simp [rows]

theorem cyclic_stabilizer (x : C3) : MulAction.stabilizer C3 x = ⊥ := by
  ext g
  simp

theorem cyclic_generated : Subgroup.closure (Set.range cyclicGenerator) = ⊤ := by
  apply top_unique
  intro g _
  have h : Multiplicative.ofAdd (1 : Fin 3) ∈ Subgroup.closure (Set.range cyclicGenerator) :=
    Subgroup.subset_closure ⟨0, rfl⟩
  rcases g with ⟨i, hi⟩
  interval_cases i
  · exact (Subgroup.closure _).one_mem
  · exact h
  · exact (Subgroup.closure _).mul_mem h h

example (x y : PathCategory C3 cyclicGenerator)
    (a : (interpretation cyclicGenerator).obj x ⟶ (interpretation cyclicGenerator).obj y) :
    ∃ p : x ⟶ y, (interpretation cyclicGenerator).map p = a :=
  arrow_coverage cyclicGenerator cyclic_generated x y a

def permutations (s : Fin 3) : S3 := if s = 1 then b else a

/-- The two transpositions generate every S3 label; duplicate index 2 adds no
new group element but remains a separate exported edge. -/
theorem permutations_generated : Subgroup.closure (Set.range permutations) = ⊤ := by
  have ha : a ∈ Subgroup.closure (Set.range permutations) :=
    Subgroup.subset_closure ⟨0, rfl⟩
  have hb : b ∈ Subgroup.closure (Set.range permutations) :=
    Subgroup.subset_closure ⟨1, rfl⟩
  have enumeration : ∀ g : S3,
      g = 1 ∨ g = a ∨ g = b ∨ g = a * b ∨ g = b * a ∨ g = a * b * a := by decide
  apply top_unique
  intro g _
  rcases enumeration g with h | h | h | h | h | h <;> subst g
  · exact (Subgroup.closure _).one_mem
  · exact ha
  · exact hb
  · exact (Subgroup.closure _).mul_mem ha hb
  · exact (Subgroup.closure _).mul_mem hb ha
  · exact (Subgroup.closure _).mul_mem ((Subgroup.closure _).mul_mem ha hb) ha

example (x y : PathCategory (Fin 3) permutations)
    (a : (interpretation permutations).obj x ⟶ (interpretation permutations).obj y) :
    ∃ p : x ⟶ y, (interpretation permutations).map p = a :=
  arrow_coverage permutations permutations_generated x y a

theorem repeated_indices : permutations 0 = permutations 2 ∧
    row (Equiv.refl (Fin 3)) permutations 0 0 ≠
      row (Equiv.refl (Fin 3)) permutations 0 2 := by
  constructor
  · rfl
  · intro h
    have h' := congrArg Row.generator h
    exact (by decide : (0 : Fin 3) ≠ 2) h'

/-- Every rendered natural-action row consumes the public endpoint theorem. -/
theorem natural_target (v s : Fin 3) :
    (row (Equiv.refl (Fin 3)) permutations v s).target = permutations s v :=
  target_correct (Equiv.refl _) permutations v s

example : (row (Equiv.refl (Fin 3)) permutations 2 0).target = 2 := by
  rw [natural_target]
  norm_num [permutations, a, Equiv.swap_apply_def]

/-- The rendered generator family uses the same chronological bridge. -/
theorem chronological_trace :
    label permutations (chronologicalPath permutations
      (⟨0⟩ : SchreierGraph (Fin 3) permutations) [(0, true), (1, true)]) 0 = 2 := by
  rw [label_chronologicalPath]
  norm_num [permutations, a, b, SchreierGraph.evalWord_cons_true,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def]

theorem written_trace :
    label permutations (SchreierGraph.pathFromWord permutations
      (⟨0⟩ : SchreierGraph (Fin 3) permutations) [(0, true), (1, true)]) 0 = 1 := by
  rw [label_pathFromWord]
  norm_num [permutations, a, b, SchreierGraph.evalWord_cons_true,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def]

instance trivialAction : MulAction S3 Unit where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def unitVertices : Fin 1 ≃ Unit where
  toFun _ := ()
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Same endpoints, distinct action arrows: the interpreter retains stabilizers. -/
theorem trivial_distinct_arrows :
    ((edgeInterpretation permutations).map (.inl (edge unitVertices permutations 0 0))).hom ≠
    ((edgeInterpretation permutations).map (.inl (edge unitVertices permutations 0 1))).hom := by
  rw [interpreted_label, interpreted_label]
  intro h
  have h0 := congrArg (fun p : S3 => p 0) h
  norm_num [row, permutations, a, b, Equiv.swap_apply_def] at h0

example : (rows unitVertices permutations).length = 3 :=
  length_rows unitVertices permutations

/-- The prior nonempty proper-subgroup control still applies: no full-coverage
claim follows merely from having drawn generator edges. -/
example : ¬ Reachable (Symmetrify.of.obj (⟨1⟩ : SchreierGraph S3 oneGenerator))
    (Symmetrify.of.obj ⟨b⟩) := nonempty_proper_subgroup_control

end SchreierDiagrams
