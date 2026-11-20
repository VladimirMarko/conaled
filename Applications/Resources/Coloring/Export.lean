import Applications.Resources.Coloring.Construction
import Applications.Resources.Coloring.Bounds

/-!
# Charged exports and the explicit Color pipeline

The decoder returns the accepted numeric observation and retains its declared
input/output fee. This is an abstract conversion tariff, not an intrinsic bound
on the coercion. Enumerations, decoding callbacks, list cells and pairs remain
charged. The pipeline constructs the graph and palette once; parsing and byte
formatting are outside this model.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.Coloring

open Search.PositiveTrie Numerals.PositiveArithmetic Numerals.PositiveKeys Graphs.Coloring
open Resources.PositiveTrie

def decodeRun (price : Node → Nat → Nat) (key : Node) : Measured Nat Cost :=
  (numeric key, structural (price key (numeric key)) + mark .decode 1)

def enumerateSet (set : NodeSet) : Measured (List Node) Cost :=
  reweight (fun cost => structural (Enumeration.Set.outerWork cost)) (Enumeration.Set.run set)

def enumerateMap (f : Assignment) : Measured (List (Node × Node)) Cost :=
  reweight (fun cost => structural (Enumeration.Map.outerWork cost)) (Enumeration.Map.run f)

def decodeKeyStep (price : Node → Nat → Nat) (key : Node) (tail : List Nat) : Measured (List Nat) Cost :=
  bind (decodeRun price key) (fun value => enter .exportCons (pure (value :: tail)))

def decodePairStep (price : Node → Nat → Nat) (entry : Node × Node) (tail : List (Nat × Nat)) :
    Measured (List (Nat × Nat)) Cost :=
  bind (decodeRun price entry.1) (fun key =>
    bind (decodeRun price entry.2) (fun color =>
    bind (enter .exportPair (pure (key, color))) (fun pair =>
    enter .exportCons (pure (pair :: tail)))))

def decodeKeysRun (price : Node → Nat → Nat) (keys : List Node) : Measured (List Nat) Cost :=
  listFold (decodeKeyStep price) keys []

def decodePairsRun (price : Node → Nat → Nat) (entries : List (Node × Node)) :
    Measured (List (Nat × Nat)) Cost := listFold (decodePairStep price) entries []

def domainExportRun (price : Node → Nat → Nat) (g : Graph) : Measured (List Nat) Cost :=
  enter .domainExport (bind (nodesRun g) (fun vertices =>
    bind (enumerateSet vertices) (fun keys => decodeKeysRun price keys)))

def assignmentExportRun (price : Node → Nat → Nat) (f : Assignment) :
    Measured (List (Nat × Nat)) Cost :=
  enter .assignmentExport (bind (enumerateMap f) (fun entries => decodePairsRun price entries))

def pipelineRun (prices : Prices) (decodePrice : Node → Nat → Nat)
    (edges : List (Node × Node)) (colors : List Node) : Measured (List Nat × List (Nat × Nat)) Cost :=
  enter .pipeline (bind (mkGraphRun edges) (fun g =>
    bind (paletteRun colors) (fun palette =>
    bind (colorRun prices palette g) (fun f =>
    bind (domainExportRun decodePrice g) (fun vertices =>
    bind (assignmentExportRun decodePrice f) (fun entries => pure (vertices, entries)))))))

@[simp] theorem decodeRun_value (price : Node → Nat → Nat) (key : Node) :
    (decodeRun price key).1 = numeric key := rfl

@[simp] theorem decodeRun_work (price : Node → Nat → Nat) (key : Node) :
    work (decodeRun price key).2 = price key (numeric key) := by simp [decodeRun]

@[simp] theorem enumerateSet_value (set : NodeSet) : (enumerateSet set).1 = KeySet.elements set :=
  Enumeration.Set.run_value set

@[simp] theorem enumerateMap_value (f : Assignment) : (enumerateMap f).1 = SparseMap.elements f :=
  Enumeration.Map.run_value f

theorem enumerateSet_work (set : NodeSet) : work (enumerateSet set).2 =
    4 * set.numNodes + 2 * KeySet.keyMass set + 1 := by
  simp only [enumerateSet, reweight, work_structural, Enumeration.Set.run,
    Enumeration.Set.runFrom_outer_work, Traversal.reversalMass_one]

theorem enumerateMap_work (f : Assignment) : work (enumerateMap f).2 =
    4 * Traversal.prefixMass f .one + f.numNodes + 2 * Traversal.copiedCells f + SparseMap.cardinal f + 1 := by
  simp only [enumerateMap, reweight, work_structural, Enumeration.Map.run, Enumeration.Map.runFrom_outer_work]

theorem decodeKeyStep_value (price : Node → Nat → Nat) (key : Node) (tail : List Nat) :
    (decodeKeyStep price key tail).1 = numeric key :: tail := rfl

theorem decodePairStep_value (price : Node → Nat → Nat) (entry : Node × Node) (tail : List (Nat × Nat)) :
    (decodePairStep price entry tail).1 = (numeric entry.1, numeric entry.2) :: tail := rfl

theorem decodeKeysRun_value (price : Node → Nat → Nat) (keys : List Node) :
    (decodeKeysRun price keys).1 = keys.map numeric := by
  simp only [decodeKeysRun, listFold_value, decodeKeyStep_value]
  induction keys with
  | nil => rfl
  | cons key rest ih => simpa only [List.foldr_cons, List.map_cons] using congrArg (List.cons (numeric key)) ih

theorem decodePairsRun_value (price : Node → Nat → Nat) (entries : List (Node × Node)) :
    (decodePairsRun price entries).1 = entries.map (fun entry => (numeric entry.1, numeric entry.2)) := by
  simp only [decodePairsRun, listFold_value, decodePairStep_value]
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      simpa only [List.foldr_cons, List.map_cons] using congrArg (List.cons (numeric entry.1, numeric entry.2)) ih

theorem domainExportRun_value (price : Node → Nat → Nat) (g : Graph) :
    (domainExportRun price g).1 = (KeySet.elements (nodes g)).map numeric := by
  simp only [domainExportRun, enter_value, bind_value, nodesRun_value, enumerateSet_value, decodeKeysRun_value]

theorem assignmentExportRun_value (price : Node → Nat → Nat) (f : Assignment) :
    (assignmentExportRun price f).1 =
      (SparseMap.elements f).map (fun entry => (numeric entry.1, numeric entry.2)) := by
  simp only [assignmentExportRun, enter_value, bind_value, enumerateMap_value, decodePairsRun_value]

theorem pipelineRun_value (prices : Prices) (decodePrice : Node → Nat → Nat)
    (edges : List (Node × Node)) (colors : List Node) :
    (pipelineRun prices decodePrice edges colors).1 =
      ((KeySet.elements (nodes (mkGraph edges))).map numeric,
       (SparseMap.elements (color (colors.foldr KeySet.add .nil) (mkGraph edges))).map
         (fun entry => (numeric entry.1, numeric entry.2))) := by
  simp only [pipelineRun, enter_value, bind_value, mkGraphRun_value, paletteRun_value,
    colorRun_value, domainExportRun_value, assignmentExportRun_value, pure]

theorem decodeKeyStep_work (price : Node → Nat → Nat) (key : Node) (tail : List Nat) :
    work (decodeKeyStep price key tail).2 = price key (numeric key) + 1 := by
  simp only [decodeKeyStep, bind_work, decodeRun_work, enter_work, pure, work_zero, Nat.add_zero]

theorem decodePairStep_work (price : Node → Nat → Nat) (entry : Node × Node) (tail : List (Nat × Nat)) :
    work (decodePairStep price entry tail).2 =
      price entry.1 (numeric entry.1) + price entry.2 (numeric entry.2) + 2 := by
  simp only [decodePairStep, bind_work, decodeRun_work, enter_work, pure, work_zero]
  omega

theorem decodeKeysRun_work (price : Node → Nat → Nat) (keys : List Node) :
    work (decodeKeysRun price keys).2 = 3 * keys.length + 1 +
      (keys.map (fun key => price key (numeric key))).sum := by
  rw [decodeKeysRun, listFold_work_eq _ _ (decodeKeyStep_work price)]
  have h : (keys.map (fun key => price key (numeric key) + 1)).sum =
      (keys.map (fun key => price key (numeric key))).sum + keys.length := by
    induction keys with
    | nil => rfl
    | cons key rest ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
  rw [h]
  omega

theorem decodePairsRun_work (price : Node → Nat → Nat) (entries : List (Node × Node)) :
    work (decodePairsRun price entries).2 = 4 * entries.length + 1 +
      (entries.map (fun entry => price entry.1 (numeric entry.1) + price entry.2 (numeric entry.2))).sum := by
  rw [decodePairsRun, listFold_work_eq _ _ (decodePairStep_work price)]
  have h : (entries.map (fun entry => price entry.1 (numeric entry.1) + price entry.2 (numeric entry.2) + 2)).sum =
      (entries.map (fun entry => price entry.1 (numeric entry.1) + price entry.2 (numeric entry.2))).sum +
        2 * entries.length := by
    induction entries with
    | nil => rfl
    | cons entry rest ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
  rw [h]
  omega

theorem domainExportRun_work (price : Node → Nat → Nat) (g : Graph) :
    work (domainExportRun price g).2 = 1 + work (nodesRun g).2 + work (enumerateSet (nodes g)).2 +
      work (decodeKeysRun price (KeySet.elements (nodes g))).2 := by
  simp only [domainExportRun, enter_work, bind_work, nodesRun_value, enumerateSet_value, Nat.add_assoc]

theorem assignmentExportRun_work (price : Node → Nat → Nat) (f : Assignment) :
    work (assignmentExportRun price f).2 = 1 + work (enumerateMap f).2 +
      work (decodePairsRun price (SparseMap.elements f)).2 := by
  simp only [assignmentExportRun, enter_work, bind_work, enumerateMap_value, Nat.add_assoc]

theorem pipelineRun_work (prices : Prices) (decodePrice : Node → Nat → Nat)
    (edges : List (Node × Node)) (colors : List Node) :
    work (pipelineRun prices decodePrice edges colors).2 =
      1 + work (mkGraphRun edges).2 + work (paletteRun colors).2 +
        work (colorRun prices (colors.foldr KeySet.add .nil) (mkGraph edges)).2 +
        work (domainExportRun decodePrice (mkGraph edges)).2 +
        work (assignmentExportRun decodePrice (color (colors.foldr KeySet.add .nil) (mkGraph edges))).2 := by
  simp only [pipelineRun, enter_work, bind_work, mkGraphRun_value, paletteRun_value, colorRun_value,
    pure, work_zero, Nat.add_zero, Nat.add_assoc]

theorem decodeRun_count (event : Event) (price : Node → Nat → Nat) (key : Node) :
    count event (decodeRun price key).2 = if event = .decode then 1 else 0 := by
  simp only [decodeRun, count_add, count_structural, count_mark, Nat.zero_add]

theorem enumerateSet_count (event : Event) (set : NodeSet) : count event (enumerateSet set).2 = 0 := rfl
theorem enumerateMap_count (event : Event) (f : Assignment) : count event (enumerateMap f).2 = 0 := rfl

theorem decodeKeyStep_count (event : Event) (price : Node → Nat → Nat) (key : Node) (tail : List Nat) :
    count event (decodeKeyStep price key tail).2 =
      (if event = .decode then 1 else 0) + (if event = .exportCons then 1 else 0) := by
  simp only [decodeKeyStep, bind_count, decodeRun_count, enter_count, pure, count_zero, Nat.add_zero]

theorem decodePairStep_count (event : Event) (price : Node → Nat → Nat) (entry : Node × Node)
    (tail : List (Nat × Nat)) : count event (decodePairStep price entry tail).2 =
      2 * (if event = .decode then 1 else 0) + (if event = .exportPair then 1 else 0) +
        (if event = .exportCons then 1 else 0) := by
  simp only [decodePairStep, bind_count, decodeRun_count, enter_count, pure, count_zero, Nat.add_zero]
  omega

theorem decodeKeysRun_count (event : Event) (price : Node → Nat → Nat) (keys : List Node) :
    count event (decodeKeysRun price keys).2 =
      (if event = .listEntry then keys.length + 1 else 0) +
      (if event = .listCallback then keys.length else 0) + keys.length *
        ((if event = .decode then 1 else 0) + (if event = .exportCons then 1 else 0)) := by
  have h := run_projection (countHom event) (decodeKeyStep price)
    (fun _ => (if event = .decode then 1 else 0) + (if event = .exportCons then 1 else 0))
    (decodeKeyStep_count event price) keys.reverse []
  change count event _ = _ at h
  simp only [decodeKeysRun, listFold_count, h, List.map_const', List.length_reverse, List.sum_replicate_nat]

theorem decodePairsRun_count (event : Event) (price : Node → Nat → Nat) (entries : List (Node × Node)) :
    count event (decodePairsRun price entries).2 =
      (if event = .listEntry then entries.length + 1 else 0) +
      (if event = .listCallback then entries.length else 0) + entries.length *
        (2 * (if event = .decode then 1 else 0) + (if event = .exportPair then 1 else 0) +
          (if event = .exportCons then 1 else 0)) := by
  have h := run_projection (countHom event) (decodePairStep price)
    (fun _ => 2 * (if event = .decode then 1 else 0) + (if event = .exportPair then 1 else 0) +
      (if event = .exportCons then 1 else 0)) (decodePairStep_count event price) entries.reverse []
  change count event _ = _ at h
  simp only [decodePairsRun, listFold_count, h, List.map_const', List.length_reverse, List.sum_replicate_nat]

theorem domainExportRun_count (event : Event) (price : Node → Nat → Nat) (g : Graph) :
    count event (domainExportRun price g).2 =
      (if event = .domainExport then 1 else 0) + (if event = .nodes then 1 else 0) +
      count event (decodeKeysRun price (KeySet.elements (nodes g))).2 := by
  simp only [domainExportRun, enter_count, bind_count, nodesRun_count, enumerateSet_count,
    nodesRun_value, enumerateSet_value, Nat.zero_add, Nat.add_assoc]

theorem assignmentExportRun_count (event : Event) (price : Node → Nat → Nat) (f : Assignment) :
    count event (assignmentExportRun price f).2 = (if event = .assignmentExport then 1 else 0) +
      count event (decodePairsRun price (SparseMap.elements f)).2 := by
  simp only [assignmentExportRun, enter_count, bind_count, enumerateMap_count,
    enumerateMap_value, Nat.zero_add]

theorem pipelineRun_count (event : Event) (prices : Prices) (decodePrice : Node → Nat → Nat)
    (edges : List (Node × Node)) (colors : List Node) :
    count event (pipelineRun prices decodePrice edges colors).2 =
      (if event = .pipeline then 1 else 0) + count event (mkGraphRun edges).2 + count event (paletteRun colors).2 +
        count event (colorRun prices (colors.foldr KeySet.add .nil) (mkGraph edges)).2 +
        count event (domainExportRun decodePrice (mkGraph edges)).2 +
        count event (assignmentExportRun decodePrice (color (colors.foldr KeySet.add .nil) (mkGraph edges))).2 := by
  simp only [pipelineRun, enter_count, bind_count, mkGraphRun_value, paletteRun_value, colorRun_value,
    pure, count_zero, Nat.add_zero, Nat.add_assoc]

theorem pipelineRun_builds_once (prices : Prices) (decodePrice : Node → Nat → Nat)
    (edges : List (Node × Node)) (colors : List Node) :
    count .mkGraph (pipelineRun prices decodePrice edges colors).2 = 1 ∧
      count .paletteSetup (pipelineRun prices decodePrice edges colors).2 = 1 := by
  simp [pipelineRun_count, mkGraphRun_count, paletteRun_count, colorRun_count,
    selectRun_count, selectionCount, colorListRun_count, paintCount,
    domainExportRun_count, assignmentExportRun_count, decodeKeysRun_count, decodePairsRun_count, edgeCount]

end Resources.Coloring
