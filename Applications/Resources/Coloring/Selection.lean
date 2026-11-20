import Applications.Resources.Coloring.Helpers
import Mathlib.Tactic.Linarith

/-!
# Measured selection and its actual residual trajectory

The executor scans, chooses, and removes using the actual returned values. Its
well-founded measure is proof data, with no executable cardinality or fuel.
The terminal scan and failed choice remain charged even for a nonempty core.
Residual lists and finite sums below are proof observations of this execution.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.Coloring

open Search.PositiveTrie Numerals.PositiveArithmetic Graphs.Coloring

def selectRun (prices : Prices) (bound : Nat) (g : Graph) : Measured (List Node) Cost :=
  let scanned := eligibleRun prices bound g
  let picked := observe .candidateChoice 1 (choose scanned.1)
  enter .select (match _chosen : picked.1 with
  | none => ([], scanned.2 + picked.2)
  | some node =>
      let removed := removeNodeRun node g
      let tail := selectRun prices bound removed.1
      (node :: tail.1, scanned.2 + picked.2 + removed.2 +
        structural 1 + mark .selectedCons 1 + tail.2))
termination_by SparseMap.cardinal g
decreasing_by
  rw [removeNodeRun_value]
  dsimp only [picked, scanned] at _chosen
  exact select_terminates bound g node
    (by simpa only [observe_value, choose_value, eligibleRun_value] using _chosen)

theorem selectRun_of_none (prices : Prices) (bound : Nat) (g : Graph)
    (chosen : KeySet.choose (eligible bound g) = none) :
    selectRun prices bound g = enter .select
      ([], (eligibleRun prices bound g).2 +
        (observe .candidateChoice 1 (choose (eligible bound g))).2) := by
  rw [selectRun]
  split
  · simp only [eligibleRun_value]
  · rename_i node actual
    have h : KeySet.choose (eligible bound g) = some node := by
      simpa only [observe_value, choose_value, eligibleRun_value] using actual
    simp only [chosen, reduceCtorEq] at h

theorem selectRun_of_some (prices : Prices) (bound : Nat) (g : Graph) (node : Node)
    (chosen : KeySet.choose (eligible bound g) = some node) :
    selectRun prices bound g =
      let tail := selectRun prices bound (removeNode node g)
      enter .select (node :: tail.1,
        (eligibleRun prices bound g).2 + (observe .candidateChoice 1 (choose (eligible bound g))).2 +
        (removeNodeRun node g).2 + structural 1 + mark .selectedCons 1 + tail.2) := by
  rw [selectRun]
  split
  · rename_i actual
    have h : KeySet.choose (eligible bound g) = none := by
      simpa only [observe_value, choose_value, eligibleRun_value] using actual
    simp only [chosen, reduceCtorEq] at h
  · rename_i current actual
    have h : KeySet.choose (eligible bound g) = some current := by
      simpa only [observe_value, choose_value, eligibleRun_value] using actual
    have same := Option.some.inj (h.symm.trans chosen)
    subst current
    simp only [eligibleRun_value, removeNodeRun_value]

@[simp] theorem selectRun_value (prices : Prices) (bound : Nat) (g : Graph) :
    (selectRun prices bound g).1 = select bound g := by
  induction g using (measure SparseMap.cardinal).wf.induction with
  | h g ih =>
      cases chosen : KeySet.choose (eligible bound g) with
      | none => rw [selectRun_of_none prices bound g chosen, select_of_none bound g chosen]; rfl
      | some node =>
          rw [selectRun_of_some prices bound g node chosen, select_of_some bound g chosen]
          exact congrArg (List.cons node)
            (ih (removeNode node g) (select_terminates bound g node chosen))

theorem selectRun_work_none (prices : Prices) (bound : Nat) (g : Graph)
    (chosen : KeySet.choose (eligible bound g) = none) :
    work (selectRun prices bound g).2 =
      1 + work (eligibleRun prices bound g).2 + work (choose (eligible bound g)).2 := by
  rw [selectRun_of_none prices bound g chosen]
  simp only [enter_work, work_add, observe_work, Nat.add_assoc]

theorem selectRun_nil_work (prices : Prices) (bound : Nat) : work (selectRun prices bound .nil).2 = 5 := by
  rw [selectRun_work_none prices bound .nil rfl]
  rfl

theorem selectRun_work_some (prices : Prices) (bound : Nat) (g : Graph) (node : Node)
    (chosen : KeySet.choose (eligible bound g) = some node) :
    work (selectRun prices bound g).2 =
      2 + work (eligibleRun prices bound g).2 + work (choose (eligible bound g)).2 +
        work (removeNodeRun node g).2 + work (selectRun prices bound (removeNode node g)).2 := by
  rw [selectRun_of_some prices bound g node chosen]
  simp only [enter_work, work_add, observe_work, work_structural, work_mark]
  omega

theorem selectRun_count_none (event : Event) (prices : Prices) (bound : Nat) (g : Graph)
    (chosen : KeySet.choose (eligible bound g) = none) :
    count event (selectRun prices bound g).2 =
      (if event = .select then 1 else 0) +
      scanCount event (SparseMap.cardinal g) (KeySet.cardinal (eligible bound g)) +
      (if event = .candidateChoice then 1 else 0) := by
  rw [selectRun_of_none prices bound g chosen]
  simp only [enter_count, count_add, eligibleRun_count, observe_count, choose_count, Nat.add_zero]
  omega

theorem selectRun_count_some (event : Event) (prices : Prices) (bound : Nat) (g : Graph) (node : Node)
    (chosen : KeySet.choose (eligible bound g) = some node) :
    count event (selectRun prices bound g).2 =
      (if event = .select then 1 else 0) +
      scanCount event (SparseMap.cardinal g) (KeySet.cardinal (eligible bound g)) +
      (if event = .candidateChoice then 1 else 0) +
      (if event = .remove then 1 else 0) + (if event = .mapErase then 1 else 0) +
      (if event = .valueMap then 1 else 0) +
      SparseMap.cardinal (removeNode node g) * (if event = .adjErase then 1 else 0) +
      (if event = .selectedCons then 1 else 0) +
      count event (selectRun prices bound (removeNode node g)).2 := by
  rw [selectRun_of_some prices bound g node chosen]
  simp only [enter_count, count_add, eligibleRun_count, observe_count, choose_count,
    removeNodeRun_count, count_structural, count_mark, cardinal_removeNode]
  omega

def residuals : List Node → Graph → List Graph
  | [], g => [g]
  | node :: rest, g => g :: residuals rest (removeNode node g)

theorem residuals_range (vertices : List Node) (g : Graph) :
    residuals vertices g = (List.range (vertices.length + 1)).map
      (fun index => removeNodes (vertices.take index) g) := by
  induction vertices generalizing g with
  | nil => simp [residuals]
  | cons node rest ih =>
      rw [residuals, ih, List.length_cons, List.range_succ_eq_map (n := rest.length + 1)]
      simp only [List.map_cons, List.take_zero, removeNodes_nil, List.map_map,
        Function.comp_def, List.take_succ_cons, removeNodes_cons]

def scanVisits (vertices removed : Nat) : Nat :=
  ((List.range (removed + 1)).map (fun index => vertices - index)).sum

def eraseVisits (vertices removed : Nat) : Nat :=
  ((List.range removed).map (fun index => vertices - index - 1)).sum

def triangle (removed : Nat) : Nat :=
  ((List.range removed).map (fun index => index + 1)).sum

theorem scanVisits_zero (vertices : Nat) : scanVisits vertices 0 = vertices := by
  simp [scanVisits]

theorem eraseVisits_zero (vertices : Nat) : eraseVisits vertices 0 = 0 := rfl

theorem scanVisits_succ (vertices removed : Nat) :
    scanVisits (vertices + 1) (removed + 1) = vertices + 1 + scanVisits vertices removed := by
  rw [scanVisits, List.range_succ_eq_map (n := removed + 1)]
  simp only [List.map_cons, List.sum_cons, Nat.sub_zero, List.map_map,
    Function.comp_def, Nat.succ_eq_add_one, Nat.add_sub_add_right, scanVisits]

theorem eraseVisits_succ (vertices removed : Nat) :
    eraseVisits (vertices + 1) (removed + 1) = vertices + eraseVisits vertices removed := by
  rw [eraseVisits, List.range_succ_eq_map]
  simp only [List.map_cons, List.sum_cons, Nat.sub_zero, List.map_map,
    Function.comp_def, Nat.succ_eq_add_one, Nat.add_sub_add_right, Nat.add_sub_cancel, eraseVisits]

theorem triangle_zero : triangle 0 = 0 := rfl

theorem triangle_succ (removed : Nat) : triangle (removed + 1) = triangle removed + removed + 1 := by
  simp only [triangle, List.range_succ, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton, Nat.add_assoc]

theorem twice_triangle (removed : Nat) : 2 * triangle removed = removed * (removed + 1) := by
  induction removed with
  | zero => rfl
  | succ removed ih => rw [triangle_succ]; nlinarith

theorem scanVisits_add_triangle (vertices removed : Nat) (within : removed ≤ vertices) :
    scanVisits vertices removed + triangle removed = (removed + 1) * vertices := by
  induction removed generalizing vertices with
  | zero => simp [scanVisits_zero, triangle_zero]
  | succ removed ih =>
      cases vertices with
      | zero => omega
      | succ vertices =>
          have h := ih vertices (by omega)
          rw [scanVisits_succ, triangle_succ]
          nlinarith

theorem eraseVisits_add_triangle (vertices removed : Nat) (within : removed ≤ vertices) :
    eraseVisits vertices removed + triangle removed = removed * vertices := by
  induction removed generalizing vertices with
  | zero => simp [eraseVisits_zero, triangle_zero]
  | succ removed ih =>
      cases vertices with
      | zero => omega
      | succ vertices =>
          have h := ih vertices (by omega)
          rw [eraseVisits_succ, triangle_succ]
          nlinarith

theorem scanVisits_eq_add_eraseVisits (vertices removed : Nat) (within : removed ≤ vertices) :
    scanVisits vertices removed = vertices + eraseVisits vertices removed := by
  have scans := scanVisits_add_triangle vertices removed within
  have erases := eraseVisits_add_triangle vertices removed within
  nlinarith

theorem triangle_eq (removed : Nat) : triangle removed = removed * (removed + 1) / 2 := by
  have h := twice_triangle removed
  omega

theorem scanVisits_eq (vertices removed : Nat) (within : removed ≤ vertices) :
    scanVisits vertices removed = (removed + 1) * vertices - removed * (removed + 1) / 2 := by
  have h := scanVisits_add_triangle vertices removed within
  rw [triangle_eq] at h
  omega

theorem eraseVisits_eq (vertices removed : Nat) (within : removed ≤ vertices) :
    eraseVisits vertices removed = removed * vertices - removed * (removed + 1) / 2 := by
  have h := eraseVisits_add_triangle vertices removed within
  rw [triangle_eq] at h
  omega

theorem scanVisits_full (vertices : Nat) :
    scanVisits vertices vertices = vertices * (vertices + 1) / 2 := by
  have balance := scanVisits_add_triangle vertices vertices (Nat.le_refl vertices)
  have twice := twice_triangle vertices
  have same : scanVisits vertices vertices = triangle vertices := by nlinarith
  rw [same, triangle_eq]

theorem eraseVisits_full (vertices : Nat) :
    eraseVisits vertices vertices = vertices * (vertices - 1) / 2 := by
  cases vertices with
  | zero => rfl
  | succ vertices =>
      rw [eraseVisits_succ, ← scanVisits_eq_add_eraseVisits vertices vertices (Nat.le_refl vertices),
        scanVisits_full]
      simp only [Nat.add_sub_cancel]
      rw [Nat.mul_comm vertices]

theorem residuals_cardinal_sum (bound : Nat) (g : Graph) :
    ((residuals (select bound g) g).map SparseMap.cardinal).sum =
      scanVisits (SparseMap.cardinal g) (select bound g).length := by
  rw [residuals_range, List.map_map, scanVisits]
  apply congrArg List.sum
  apply List.map_congr_left
  intro index member
  exact cardinal_removeNodes_take bound g index (by
    have h := List.mem_range.mp member
    omega)

theorem residuals_tail_cardinal_sum (bound : Nat) (g : Graph) :
    (((residuals (select bound g) g).tail).map SparseMap.cardinal).sum =
      eraseVisits (SparseMap.cardinal g) (select bound g).length := by
  have total := residuals_cardinal_sum bound g
  have balance := scanVisits_eq_add_eraseVisits (SparseMap.cardinal g) (select bound g).length
    (select_length_le_cardinal bound g)
  have head : ((residuals (select bound g) g).map SparseMap.cardinal).sum =
      SparseMap.cardinal g + (((residuals (select bound g) g).tail).map SparseMap.cardinal).sum := by
    cases select bound g <;> simp only [residuals, List.map_cons, List.sum_cons, List.tail_cons,
      List.map_nil, List.sum_nil, Nat.add_zero]
  omega

def candidateVisits (bound : Nat) (g : Graph) : Nat :=
  ((residuals (select bound g) g).map (fun current => KeySet.cardinal (eligible bound current))).sum

theorem eligible_cardinal_of_none (bound : Nat) (g : Graph)
    (chosen : KeySet.choose (eligible bound g) = none) : KeySet.cardinal (eligible bound g) = 0 := by
  rw [← KeySet.observe_card, (KeySet.choose_none_iff_observe_empty _).mp chosen]
  rfl

theorem candidateVisits_none (bound : Nat) (g : Graph)
    (chosen : KeySet.choose (eligible bound g) = none) : candidateVisits bound g = 0 := by
  rw [candidateVisits, select_of_none bound g chosen]
  simp only [residuals, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, eligible_cardinal_of_none bound g chosen]

theorem candidateVisits_some (bound : Nat) (g : Graph) (node : Node)
    (chosen : KeySet.choose (eligible bound g) = some node) :
    candidateVisits bound g = KeySet.cardinal (eligible bound g) +
      candidateVisits bound (removeNode node g) := by
  rw [candidateVisits, select_of_some bound g chosen]
  rfl

def selectionCount (event : Event) (vertices removed candidates : Nat) : Nat :=
  match event with
  | .select | .eligible | .subset | .candidateChoice => removed + 1
  | .predicate | .lowDegree | .degreeCardinality | .comparison => scanVisits vertices removed
  | .candidateInsert => candidates
  | .remove | .mapErase | .valueMap | .selectedCons => removed
  | .adjErase => eraseVisits vertices removed
  | _ => 0

/-- Every event is counted on the actual trajectory, including the terminal scan. -/
theorem selectRun_count (event : Event) (prices : Prices) (bound : Nat) (g : Graph) :
    count event (selectRun prices bound g).2 =
      selectionCount event (SparseMap.cardinal g) (select bound g).length (candidateVisits bound g) := by
  induction g using (measure SparseMap.cardinal).wf.induction with
  | h g ih =>
      cases chosen : KeySet.choose (eligible bound g) with
      | none =>
          rw [selectRun_count_none event prices bound g chosen, select_of_none bound g chosen,
            candidateVisits_none bound g chosen, eligible_cardinal_of_none bound g chosen]
          cases event <;> simp [selectionCount, scanCount, scanVisits_zero, eraseVisits_zero]
      | some node =>
          have tail := ih (removeNode node g) (select_terminates bound g node chosen)
          have cards := (cardinal_removeNode_of_mem node g (chosen_facts bound g chosen).1).symm
          rw [selectRun_count_some event prices bound g node chosen, tail,
            select_of_some bound g chosen, candidateVisits_some bound g node chosen, cards]
          simp only [List.length_cons]
          cases event <;> simp [selectionCount, scanCount, scanVisits_succ, eraseVisits_succ] <;> omega

theorem selectRun_full_counts (prices : Prices) (bound : Nat) (g : Graph)
    (complete : (select bound g).length = SparseMap.cardinal g) :
    count .predicate (selectRun prices bound g).2 = SparseMap.cardinal g * (SparseMap.cardinal g + 1) / 2 ∧
      count .adjErase (selectRun prices bound g).2 = SparseMap.cardinal g * (SparseMap.cardinal g - 1) / 2 := by
  simp only [selectRun_count, selectionCount, complete, scanVisits_full, eraseVisits_full, and_self]

theorem selectRun_residual_cardinal (prices : Prices) (bound : Nat) (g : Graph)
    (index : Nat) (within : index ≤ (selectRun prices bound g).1.length) :
    SparseMap.cardinal (removeNodes ((selectRun prices bound g).1.take index) g) =
      SparseMap.cardinal g - index := by
  simpa only [selectRun_value] using
    cardinal_removeNodes_take bound g index (by simpa only [selectRun_value] using within)

/-- A proof observation of one reached stage; this is not called by `selectRun`. -/
def selectionStageCost (prices : Prices) (bound : Nat) (g : Graph) : Cost :=
  structural 1 + mark .select 1 + (eligibleRun prices bound g).2 +
    (observe .candidateChoice 1 (choose (eligible bound g))).2 +
    (match KeySet.choose (eligible bound g) with
    | none => 0
    | some node => (removeNodeRun node g).2 + structural 1 + mark .selectedCons 1)

theorem selectRun_cost_none (prices : Prices) (bound : Nat) (g : Graph)
    (chosen : KeySet.choose (eligible bound g) = none) :
    (selectRun prices bound g).2 = selectionStageCost prices bound g := by
  rw [selectRun_of_none prices bound g chosen]
  simp only [enter, selectionStageCost, chosen, add_zero, add_assoc]

theorem selectRun_cost_some (prices : Prices) (bound : Nat) (g : Graph) (node : Node)
    (chosen : KeySet.choose (eligible bound g) = some node) :
    (selectRun prices bound g).2 = selectionStageCost prices bound g +
      (selectRun prices bound (removeNode node g)).2 := by
  rw [selectRun_of_some prices bound g node chosen]
  simp only [enter, selectionStageCost, chosen, add_assoc]

theorem selectRun_cost_trajectory (prices : Prices) (bound : Nat) (g : Graph) :
    (selectRun prices bound g).2 =
      ((residuals (select bound g) g).map (selectionStageCost prices bound)).sum := by
  induction g using (measure SparseMap.cardinal).wf.induction with
  | h g ih =>
      cases chosen : KeySet.choose (eligible bound g) with
      | none =>
          rw [selectRun_cost_none prices bound g chosen, select_of_none bound g chosen]
          simp only [residuals, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      | some node =>
          rw [selectRun_cost_some prices bound g node chosen,
            ih (removeNode node g) (select_terminates bound g node chosen), select_of_some bound g chosen]
          rfl

theorem selectRun_projection_trajectory (projection : Cost →+ Nat) (prices : Prices)
    (bound : Nat) (g : Graph) :
    projection (selectRun prices bound g).2 =
      ((residuals (select bound g) g).map (fun current => projection (selectionStageCost prices bound current))).sum := by
  have distribute (xs : List Cost) : projection xs.sum = (xs.map projection).sum := by
    induction xs with
    | nil => exact map_zero projection
    | cons x xs ih => simp only [List.sum_cons, List.map_cons, map_add, ih]
  rw [selectRun_cost_trajectory, distribute, List.map_map]
  rfl

theorem selectionStageCost_structural_eq (prices other : Prices) (bound : Nat) (g : Graph) :
    structuralHom (selectionStageCost prices bound g) = structuralHom (selectionStageCost other bound g) := by
  simp only [selectionStageCost, map_add]
  rw [eligibleRun_structural_eq prices other bound g]

theorem selectRun_structural_eq (prices other : Prices) (bound : Nat) (g : Graph) :
    structuralHom (selectRun prices bound g).2 = structuralHom (selectRun other bound g).2 := by
  rw [selectRun_projection_trajectory, selectRun_projection_trajectory]
  apply congrArg List.sum
  apply List.map_congr_left
  intro current _
  exact selectionStageCost_structural_eq prices other bound current

theorem selectionStageCost_arithmetic (prices : Prices) (bound : Nat) (g : Graph) :
    arithmeticHom (selectionStageCost prices bound g) = scanTariff prices bound g := by
  cases chosen : KeySet.choose (eligible bound g) <;>
    simp only [selectionStageCost, chosen, map_add, arithmeticHom_structural, arithmeticHom_mark,
      eligibleRun_arithmetic, observe_projection, choose_arithmetic, removeNodeRun_arithmetic,
      map_zero, Nat.add_zero, Nat.zero_add]

theorem selectRun_arithmetic (prices : Prices) (bound : Nat) (g : Graph) :
    arithmeticHom (selectRun prices bound g).2 =
      ((residuals (select bound g) g).map (scanTariff prices bound)).sum := by
  rw [selectRun_projection_trajectory]
  simp only [selectionStageCost_arithmetic]

end Resources.Coloring
