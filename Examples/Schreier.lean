import Applications.GroupActions.Equivariant
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.NormNum

/-! Finite regular, nonfree and ineffective actions consume the same interpretation.
The transpositions (01), then (12), take 0 to 2; the reverse order takes 0 to 1. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Quiver Schreier
namespace SchreierExamples

abbrev S3 := Equiv.Perm (Fin 3)
def a : S3 := Equiv.swap 0 1
def b : S3 := Equiv.swap 1 2

theorem ab_ne_ba : b * a ≠ a * b := by
  intro h
  have h0 := congrArg (fun k : S3 => k 0) h
  norm_num [a, b, Equiv.Perm.mul_apply, Equiv.swap_apply_def] at h0

/-- The regular action is finite and has trivial stabilizers. -/
theorem regular_stabilizer (x : S3) : MulAction.stabilizer S3 x = ⊥ := by
  ext g
  simp

example : Finite S3 := inferInstance

/-- Chronological execution in the Cayley graph keeps the noncommuting order. -/
theorem cayley_order :
    label (id : S3 → S3)
      (chronologicalPath id (⟨1⟩ : SchreierGraph S3 id) [(a, true), (b, true)]) = b * a := by
  rw [label_chronologicalPath]
  simp [SchreierGraph.evalWord_cons_true]

/-- The same interpreter on the nonfree natural S3 action sends 0 to 2. -/
theorem schreier_order :
    label (id : S3 → S3)
      (chronologicalPath id (⟨0⟩ : SchreierGraph (Fin 3) id) [(a, true), (b, true)]) 0 = 2 := by
  rw [label_chronologicalPath]
  norm_num [a, b, SchreierGraph.evalWord_cons_true, Equiv.Perm.mul_apply, Equiv.swap_apply_def]

/-- Mathlib's written order has the other answer, so reversal is observable. -/
theorem mathlib_order :
    label (id : S3 → S3)
      (SchreierGraph.pathFromWord id (⟨0⟩ : SchreierGraph (Fin 3) id)
        [(a, true), (b, true)]) 0 = 1 := by
  rw [label_pathFromWord]
  norm_num [a, b, SchreierGraph.evalWord_cons_true, Equiv.Perm.mul_apply, Equiv.swap_apply_def]

def fixedEdge : @Quiver.Hom (SchreierGraph (Fin 3) (id : S3 → S3)) _ ⟨2⟩ ⟨2⟩ :=
  ⟨a, by
    apply SchreierGraph.ext
    change a 2 = 2
    norm_num [a, Equiv.swap_apply_def]⟩

def fixedVertex : Vertices (Fin 3) (id : S3 → S3) := ⟨2⟩

def fixedPath : Path fixedVertex fixedVertex :=
  Path.nil.cons (.inl fixedEdge)

theorem nonfree_retains_stabilizer :
    label id fixedPath = a ∧ label id fixedPath ≠ label id (Path.nil : Path fixedVertex fixedVertex) := by
  constructor
  · simp [fixedPath, fixedEdge]
  · intro h
    have h0 := congrArg (fun k : S3 => k 0) h
    norm_num [fixedPath, fixedEdge, a, Equiv.swap_apply_def] at h0

/-- A trivial action of the nontrivial group has one endpoint and many arrows. -/
local instance : MulAction S3 Unit where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def trivialEdge : @Quiver.Hom (SchreierGraph Unit (id : S3 → S3)) _ ⟨()⟩ ⟨()⟩ :=
  ⟨a, rfl⟩
def trivialVertex : Vertices Unit (id : S3 → S3) := ⟨()⟩
def trivialPath : Path trivialVertex trivialVertex :=
  Path.nil.cons (.inl trivialEdge)

theorem trivial_labels_distinct :
    ¬ (semanticEquiv (X := Unit) (id : S3 → S3)).Rel trivialPath Path.nil := by
  rw [semantic_iff_label]
  intro h
  have h0 := congrArg (fun k : S3 => k 0) h
  norm_num [trivialPath, trivialEdge, a, Equiv.swap_apply_def] at h0

theorem raw_paths_distinct_but_semantically_equal :
    trivialPath.comp trivialPath.reverse ≠ Path.nil ∧
    (semanticEquiv (X := Unit) (id : S3 → S3)).Rel
      (trivialPath.comp trivialPath.reverse) Path.nil := by
  constructor
  · intro h
    have hl := congrArg Path.length h
    simp [trivialPath, Path.reverse, Path.comp, Quiver.Hom.toPath] at hl
  · rw [semantic_iff_label, label_comp, label_reverse, inv_mul_cancel, label_nil]

/-- Empty generators form a proper subgroup; the full regular orbit is larger. -/
def noGenerators : Empty → S3 := Empty.elim

theorem proper_subgroup_control :
    (∃ g : S3, g • (⟨1⟩ : SchreierGraph S3 noGenerators) = ⟨a⟩) ∧
    ¬ Reachable (Symmetrify.of.obj (⟨1⟩ : SchreierGraph S3 noGenerators))
      (Symmetrify.of.obj ⟨a⟩) := by
  constructor
  · exact ⟨a, by apply SchreierGraph.ext; exact mul_one a⟩
  · rw [Schreier.reachable_iff]
    rintro ⟨g, hg, h⟩
    have hr : Set.range noGenerators = ∅ := by ext x; simp [noGenerators]
    rw [hr, Subgroup.closure_empty, Subgroup.mem_bot] at hg
    subst g
    have ha : (1 : S3) = a := by simpa using congrArg SchreierGraph.toVertex h
    have h0 := congrArg (fun k : S3 => k 0) ha
    norm_num [a, Equiv.swap_apply_def] at h0

/-- Even a nonempty generator family can miss full-orbit arrows. The subgroup
of (01) fixes 2, whereas (12) moves 2. -/
def oneGenerator : Unit → S3 := fun _ => a

theorem nonempty_proper_subgroup_control :
    ¬ Reachable (Symmetrify.of.obj (⟨1⟩ : SchreierGraph S3 oneGenerator))
      (Symmetrify.of.obj ⟨b⟩) := by
  rw [Schreier.reachable_iff]
  rintro ⟨g, hg, h⟩
  have hsub : Subgroup.closure (Set.range oneGenerator) ≤ MulAction.stabilizer S3 (2 : Fin 3) := by
    rw [Subgroup.closure_le]
    rintro k ⟨s, rfl⟩
    change a 2 = 2
    norm_num [a, Equiv.swap_apply_def]
  have hb : g = b := by
    have hval := congrArg SchreierGraph.toVertex h
    change g * 1 = b at hval
    simpa using hval
  have hg2 := hsub hg
  rw [hb] at hg2
  change b 2 = 2 at hg2
  norm_num [b, Equiv.swap_apply_def] at hg2

theorem all_labels_generated : Subgroup.closure (Set.range (id : S3 → S3)) = ⊤ := by
  simp

example (x y : SchreierGraph (Fin 3) (id : S3 → S3)) :
    Reachable (Symmetrify.of.obj x) (Symmetrify.of.obj y) ↔ ∃ g : S3, g • x = y :=
  reachable_iff_full id all_labels_generated x y

/-- Two equivariant changes: regular action to evaluation at 0, then to Unit.
These collapse vertices and stabilizers differently, but retain arrow labels. -/
def evaluateZero : S3 → Fin 3 := fun g => g 0

theorem evaluateZero_equivariant (g x : S3) : evaluateZero (g • x) = g • evaluateZero x := rfl

theorem forget_equivariant (g : S3) (x : Fin 3) :
    (fun _ : Fin 3 => ()) (g • x) = g • () := rfl

example {x y z : PathCategory S3 (id : S3 → S3)} (p : x ⟶ y) (q : y ⟶ z) :
    (twiceChanged id (MonoidHom.id S3) (MonoidHom.id S3)
      evaluateZero (fun _ : Fin 3 => ()) evaluateZero_equivariant forget_equivariant).map (p ≫ q) =
    (twiceChanged id (MonoidHom.id S3) (MonoidHom.id S3)
      evaluateZero (fun _ : Fin 3 => ()) evaluateZero_equivariant forget_equivariant).map p ≫
    (twiceChanged id (MonoidHom.id S3) (MonoidHom.id S3)
      evaluateZero (fun _ : Fin 3 => ()) evaluateZero_equivariant forget_equivariant).map q :=
  twiceChanged_comp _ _ _ _ _ _ _ p q

example {x y : PathCategory S3 (id : S3 → S3)} (p : x ⟶ y) :
    (interpretation (X := Unit) id).map
      ((equivariantPaths (ι := id) (κ := id) (MonoidHom.id S3) (fun _ : Fin 3 => ())
        forget_equivariant id (fun _ => rfl)).map
      ((equivariantPaths (ι := id) (κ := id) (MonoidHom.id S3) evaluateZero
        evaluateZero_equivariant id (fun _ => rfl)).map p)) =
    (twiceChanged id (MonoidHom.id S3) (MonoidHom.id S3)
      evaluateZero (fun _ : Fin 3 => ()) evaluateZero_equivariant forget_equivariant).map p :=
  twiceChanged_agrees (ι := id) (κ := id) (μ := id)
    (MonoidHom.id S3) (MonoidHom.id S3) evaluateZero (fun _ : Fin 3 => ())
    evaluateZero_equivariant forget_equivariant id id (fun _ => rfl) (fun _ => rfl) p

example (x y : PathCategory (Fin 3) (id : S3 → S3))
    (arrow : (interpretation id).obj x ⟶ (interpretation id).obj y) :
    ∃ p : x ⟶ y, (interpretation id).map p = arrow :=
  arrow_coverage id all_labels_generated x y arrow

end SchreierExamples
