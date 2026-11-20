import Applications.Resources.Coloring.Selection

/-!
# The actual measured coloring program

Neighbor lookups consume the current suffix assignment. Every successful lookup
inserts its returned color, including repeated colors. Each coloring step reads
the same original graph, and failed choice preserves the entire input assignment.
The supplied palette is counted once before selection.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.Coloring

open Search.PositiveTrie Numerals.PositiveArithmetic Graphs.Coloring

def colorsStep (f : Assignment) (key : Node) (used : NodeSet) : Measured NodeSet Cost :=
  bind (observe .neighborLookup 1 (lookup key f)) (fun found =>
    match found with
    | none => pure used
    | some color => observe .neighborSuccess 1 (observe .neighborInsert 1 (insertSet color used)))

def colorsOfRun (f : Assignment) (vertices : NodeSet) : Measured NodeSet Cost :=
  enter .colorsOf (setFold (colorsStep f) vertices .nil)

def availableColorsRun (palette : NodeSet) (g : Graph) (key : Node) (f : Assignment) :
    Measured NodeSet Cost :=
  enter .available (bind (adjRun g key) (fun neighbors =>
    bind (colorsOfRun f neighbors) (fun used => observe .difference 1 (difference palette used))))

def color1Run (palette : NodeSet) (g : Graph) (key : Node) (f : Assignment) : Measured Assignment Cost :=
  enter .colorStep (bind (availableColorsRun palette g key f) (fun available =>
    bind (observe .colorChoice 1 (choose available)) (fun chosen =>
      match chosen with
      | none => pure f
      | some color => observe .assignmentWrite 1 (insertMap key color f))))

def colorListRun (palette : NodeSet) (g : Graph) (vertices : List Node) : Measured Assignment Cost :=
  enter .colorList (listFold (color1Run palette g) vertices .nil)

def colorRun (prices : Prices) (palette : NodeSet) (g : Graph) : Measured Assignment Cost :=
  enter .color (bind (observe .paletteCardinality 1 (cardinality prices palette)) (fun bound =>
    bind (selectRun prices bound g) (fun vertices => colorListRun palette g vertices)))

theorem colorsStep_value (f : Assignment) (key : Node) (used : NodeSet) :
    (colorsStep f key used).1 =
      match SparseMap.find key f with
      | none => used
      | some color => KeySet.add color used := by
  cases found : SparseMap.find key f <;>
    simp only [colorsStep, bind_value, observe_value, lookup_value, found, pure, insertSet_value]

@[simp] theorem colorsOfRun_value (f : Assignment) (vertices : NodeSet) :
    (colorsOfRun f vertices).1 = colorsOf f vertices := by
  simp only [colorsOfRun, enter_value, setFold_value, colorsStep_value, colorsOf]
  congr 1
  funext key state
  cases SparseMap.find key f <;> rfl

@[simp] theorem availableColorsRun_value (palette : NodeSet) (g : Graph) (key : Node) (f : Assignment) :
    (availableColorsRun palette g key f).1 = availableColors palette g key f := by
  simp only [availableColorsRun, enter_value, bind_value, adjRun_value, colorsOfRun_value,
    observe_value, difference_value, availableColors]

@[simp] theorem color1Run_value (palette : NodeSet) (g : Graph) (key : Node) (f : Assignment) :
    (color1Run palette g key f).1 = color1 palette g key f := by
  cases chosen : KeySet.choose (availableColors palette g key f) <;>
    simp only [color1Run, enter_value, bind_value, availableColorsRun_value, observe_value,
      choose_value, chosen, pure, insertMap_value, color1]

@[simp] theorem colorListRun_value (palette : NodeSet) (g : Graph) (vertices : List Node) :
    (colorListRun palette g vertices).1 = colorList palette g vertices := by
  simp only [colorListRun, enter_value, listFold_value, color1Run_value, colorList]

@[simp] theorem colorRun_value (prices : Prices) (palette : NodeSet) (g : Graph) :
    (colorRun prices palette g).1 = color palette g := by
  simp only [colorRun, enter_value, bind_value, observe_value, cardinality_value,
    selectRun_value, colorListRun_value, color]

theorem colorsOfRun_valid {bits : Nat} {palette : NodeSet} (valid : SetValid bits palette)
    (f : Assignment) (colors : AllPalette palette f) (vertices : NodeSet) :
    SetValid bits (colorsOfRun f vertices).1 := by
  rw [colorsOfRun_value]
  exact colorsOf_valid valid f colors vertices

theorem availableColorsRun_valid {bits : Nat} {palette : NodeSet} (valid : SetValid bits palette)
    (g : Graph) (key : Node) (f : Assignment) : SetValid bits (availableColorsRun palette g key f).1 := by
  rw [availableColorsRun_value]
  exact availableColors_valid valid g key f

theorem color1Run_valid {bits : Nat} {palette : NodeSet} {f : Assignment}
    (valid : AssignmentValid bits palette f) (g : Graph) (key : Node) (bounded : bitLength key ≤ bits) :
    AssignmentValid bits palette (color1Run palette g key f).1 := by
  rw [color1Run_value]
  exact valid.color1 g key bounded

theorem colorListRun_valid (bits : Nat) (palette : NodeSet) (g : Graph) (vertices : List Node)
    (bounded : ∀ key ∈ vertices, bitLength key ≤ bits) :
    AssignmentValid bits palette (colorListRun palette g vertices).1 := by
  rw [colorListRun_value]
  exact colorList_valid bits palette g vertices bounded

theorem colorRun_valid {bits : Nat} {g : Graph} (valid : GraphValid bits g)
    (prices : Prices) (palette : NodeSet) : AssignmentValid bits palette (colorRun prices palette g).1 := by
  rw [colorRun_value]
  exact color_valid valid palette

theorem colorsStep_work (f : Assignment) (key : Node) (used : NodeSet) :
    work (colorsStep f key used).2 = work (lookup key f).2 +
      (match SparseMap.find key f with | none => 0 | some color => 2 * bitLength color) := by
  cases found : SparseMap.find key f <;>
    simp only [colorsStep, bind_work, observe_work, observe_value, lookup_value, found,
      pure, work_zero, insertSet_work]

theorem colorsOfRun_work (f : Assignment) (vertices : NodeSet) :
    work (colorsOfRun f vertices).2 =
      4 * vertices.numNodes + 2 * KeySet.keyMass vertices + 2 +
        work (Resources.run (colorsStep f) (KeySet.elements vertices) .nil).2 := by
  simp only [colorsOfRun, enter_work, setFold_cost, work_add, work_structural]
  omega

theorem availableColorsRun_work (palette : NodeSet) (g : Graph) (key : Node) (f : Assignment) :
    work (availableColorsRun palette g key f).2 =
      1 + work (adjRun g key).2 + work (colorsOfRun f (adj g key)).2 +
        work (difference palette (colorsOf f (adj g key))).2 := by
  simp only [availableColorsRun, enter_work, bind_work, adjRun_value, colorsOfRun_value,
    observe_work, Nat.add_assoc]

theorem color1Run_work (palette : NodeSet) (g : Graph) (key : Node) (f : Assignment) :
    work (color1Run palette g key f).2 =
      1 + work (availableColorsRun palette g key f).2 +
        work (choose (availableColors palette g key f)).2 +
        (if (KeySet.choose (availableColors palette g key f)).isSome then 2 * bitLength key else 0) := by
  cases chosen : KeySet.choose (availableColors palette g key f) <;>
    simp only [color1Run, enter_work, bind_work, availableColorsRun_value, observe_work,
      observe_value, choose_value, chosen, pure, work_zero, insertMap_work,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Nat.add_assoc]

theorem colorRun_work (prices : Prices) (palette : NodeSet) (g : Graph) :
    work (colorRun prices palette g).2 = 1 + work (cardinality prices palette).2 +
      work (selectRun prices (KeySet.cardinal palette) g).2 +
      work (colorListRun palette g (select (KeySet.cardinal palette) g)).2 := by
  simp only [colorRun, enter_work, bind_work, observe_work, observe_value, cardinality_value,
    selectRun_value, Nat.add_assoc]

def successfulNeighbors (f : Assignment) (vertices : NodeSet) : Nat :=
  ((KeySet.elements vertices).map (fun key => if (SparseMap.find key f).isSome then 1 else 0)).sum

theorem colorsStep_count (event : Event) (f : Assignment) (key : Node) (used : NodeSet) :
    count event (colorsStep f key used).2 = (if event = .neighborLookup then 1 else 0) +
      (if (SparseMap.find key f).isSome then
        (if event = .neighborSuccess then 1 else 0) + (if event = .neighborInsert then 1 else 0) else 0) := by
  cases found : SparseMap.find key f <;>
    simp only [colorsStep, bind_count, observe_count, lookup_count, observe_value,
      lookup_value, found, pure, count_zero, insertSet_count, Option.isSome_none,
      Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

theorem colorsOfRun_count (event : Event) (f : Assignment) (vertices : NodeSet) :
    count event (colorsOfRun f vertices).2 = (if event = .colorsOf then 1 else 0) +
      KeySet.cardinal vertices * (if event = .neighborLookup then 1 else 0) +
      successfulNeighbors f vertices *
        ((if event = .neighborSuccess then 1 else 0) + (if event = .neighborInsert then 1 else 0)) := by
  have h := run_projection (countHom event) (colorsStep f)
    (fun key => (if event = .neighborLookup then 1 else 0) +
      (if (SparseMap.find key f).isSome then
        (if event = .neighborSuccess then 1 else 0) + (if event = .neighborInsert then 1 else 0) else 0))
    (fun key used => colorsStep_count event f key used) (KeySet.elements vertices) .nil
  change count event _ = _ at h
  simp only [colorsOfRun, enter_count, setFold_count, h]
  cases event <;> simp [successfulNeighbors, List.map_const', KeySet.elements_length]

theorem availableColorsRun_count (event : Event) (palette : NodeSet) (g : Graph) (key : Node)
    (f : Assignment) :
    count event (availableColorsRun palette g key f).2 =
      (if event = .available then 1 else 0) + count event (adjRun g key).2 +
      count event (colorsOfRun f (adj g key)).2 + (if event = .difference then 1 else 0) := by
  simp only [availableColorsRun, enter_count, bind_count, adjRun_value, colorsOfRun_value,
    observe_count, difference_count, Nat.add_zero, Nat.add_assoc]

theorem color1Run_count (event : Event) (palette : NodeSet) (g : Graph) (key : Node) (f : Assignment) :
    count event (color1Run palette g key f).2 = (if event = .colorStep then 1 else 0) +
      count event (availableColorsRun palette g key f).2 + (if event = .colorChoice then 1 else 0) +
      (if (KeySet.choose (availableColors palette g key f)).isSome then
        (if event = .assignmentWrite then 1 else 0) else 0) := by
  cases chosen : KeySet.choose (availableColors palette g key f) <;>
    simp only [color1Run, enter_count, bind_count, availableColorsRun_value, observe_count,
      choose_count, observe_value, choose_value, chosen, pure, count_zero, insertMap_count,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.add_assoc]

theorem color1Run_writes (palette : NodeSet) (g : Graph) (key : Node) (f : Assignment) :
    count .assignmentWrite (color1Run palette g key f).2 =
      if (KeySet.choose (availableColors palette g key f)).isSome then 1 else 0 := by
  simp only [color1Run_count, availableColorsRun_count, adjRun_count, colorsOfRun_count,
    reduceCtorEq, ite_true, ite_false, Nat.mul_zero, Nat.add_zero, Nat.zero_add]

theorem color1Run_writes_le (palette : NodeSet) (g : Graph) (key : Node) (f : Assignment) :
    count .assignmentWrite (color1Run palette g key f).2 ≤ 1 := by
  rw [color1Run_writes]
  split_ifs <;> omega

theorem colorListRun_work_nil (palette : NodeSet) (g : Graph) :
    work (colorListRun palette g []).2 = 2 := rfl

theorem colorRun_nil_work (prices : Prices) (palette : NodeSet) :
    work (colorRun prices palette .nil).2 = work (cardinality prices palette).2 + 8 := by
  rw [colorRun_work, selectRun_nil_work, select_of_none (KeySet.cardinal palette) .nil rfl,
    colorListRun_work_nil]
  omega

theorem colorListRun_work_cons (palette : NodeSet) (g : Graph) (key : Node) (rest : List Node) :
    work (colorListRun palette g (key :: rest)).2 = 2 + work (colorListRun palette g rest).2 +
      work (color1Run palette g key (colorList palette g rest)).2 := by
  have value : (listFold (color1Run palette g) rest .nil).1 = colorList palette g rest := by
    simp only [listFold_value, color1Run_value, colorList]
  simp only [colorListRun, enter_work, listFold_work_cons, value]
  omega

/-- Successful lookups at each actual suffix assignment, retaining repeated colors. -/
def neighborInsertions (palette : NodeSet) (g : Graph) : List Node → Nat
  | [] => 0
  | key :: rest => successfulNeighbors (colorList palette g rest) (adj g key) +
      neighborInsertions palette g rest

/-- Success indicators for actual choices; generic lists need not succeed. -/
def successfulChoices (palette : NodeSet) (g : Graph) : List Node → Nat
  | [] => 0
  | key :: rest =>
      (if (KeySet.choose (availableColors palette g key (colorList palette g rest))).isSome then 1 else 0) +
      successfulChoices palette g rest

def storedOccurrences (g : Graph) (vertices : List Node) : Nat :=
  (vertices.map (fun key => if (SparseMap.find key g).isSome then 1 else 0)).sum

def paintCount (event : Event) (vertices neighbors successes writes stored : Nat) : Nat :=
  match event with
  | .listEntry => vertices + 1
  | .listCallback | .colorStep | .available | .adj | .colorsOf | .difference | .colorChoice => vertices
  | .neighborLookup => neighbors
  | .neighborSuccess | .neighborInsert => successes
  | .assignmentWrite => writes
  | .adjFound => stored
  | _ => 0

theorem colorListRun_count (event : Event) (palette : NodeSet) (g : Graph) (vertices : List Node) :
    count event (colorListRun palette g vertices).2 = (if event = .colorList then 1 else 0) +
      paintCount event vertices.length (vertices.map (degree g)).sum
        (neighborInsertions palette g vertices) (successfulChoices palette g vertices)
        (storedOccurrences g vertices) := by
  have bare : count event (listFold (color1Run palette g) vertices .nil).2 =
      paintCount event vertices.length (vertices.map (degree g)).sum
        (neighborInsertions palette g vertices) (successfulChoices palette g vertices)
        (storedOccurrences g vertices) := by
    induction vertices with
    | nil => rw [listFold_count_nil]; cases event <;> rfl
    | cons key rest ih =>
        have value : (listFold (color1Run palette g) rest .nil).1 = colorList palette g rest := by
          simp only [listFold_value, color1Run_value, colorList]
        rw [listFold_count_cons, value, ih, color1Run_count, availableColorsRun_count,
          adjRun_count, colorsOfRun_count]
        simp only [List.length_cons, List.map_cons, List.sum_cons, neighborInsertions,
          successfulChoices, storedOccurrences]
        cases event <;> simp [paintCount, degree] <;> (try split_ifs) <;> omega
  simp only [colorListRun, enter_count, bare]

theorem successfulChoices_le (palette : NodeSet) (g : Graph) (vertices : List Node) :
    successfulChoices palette g vertices ≤ vertices.length := by
  induction vertices with
  | nil => exact Nat.le_refl 0
  | cons key rest ih =>
      rw [successfulChoices, List.length_cons]
      split_ifs <;> omega

theorem colorListRun_writes_le (palette : NodeSet) (g : Graph) (vertices : List Node) :
    count .assignmentWrite (colorListRun palette g vertices).2 ≤ vertices.length := by
  rw [colorListRun_count]
  simp only [paintCount, reduceCtorEq, ite_false, Nat.zero_add]
  exact successfulChoices_le palette g vertices

theorem successfulChoices_suffix (palette : NodeSet) (g : Graph) (vertices before : List Node)
    (selected : select (KeySet.cardinal palette) g = before ++ vertices) :
    successfulChoices palette g vertices = vertices.length := by
  induction vertices generalizing before with
  | nil => rfl
  | cons key rest ih =>
      obtain ⟨color, chosen⟩ := exists_color_after_suffix palette g before rest key selected
      have tail := ih (before ++ [key]) (by simpa only [List.append_assoc, List.singleton_append] using selected)
      simp only [successfulChoices, chosen, Option.isSome_some, ↓reduceIte, tail, List.length_cons]
      omega

theorem colorListRun_writes_suffix (palette : NodeSet) (g : Graph) (vertices before : List Node)
    (selected : select (KeySet.cardinal palette) g = before ++ vertices) :
    count .assignmentWrite (colorListRun palette g vertices).2 = vertices.length := by
  rw [colorListRun_count]
  simp only [paintCount, reduceCtorEq, ite_false, Nat.zero_add]
  exact successfulChoices_suffix palette g vertices before selected

theorem colorRun_count (event : Event) (prices : Prices) (palette : NodeSet) (g : Graph) :
    count event (colorRun prices palette g).2 = (if event = .color then 1 else 0) +
      (if event = .paletteCardinality then 1 else 0) +
      count event (selectRun prices (KeySet.cardinal palette) g).2 +
      count event (colorListRun palette g (select (KeySet.cardinal palette) g)).2 := by
  simp only [colorRun, enter_count, bind_count, observe_count, cardinality_count,
    observe_value, cardinality_value, selectRun_value, Nat.add_zero, Nat.add_assoc]

/-- Every actual selected suffix writes once per vertex, without graph-validity hypotheses. -/
theorem colorRun_writes (prices : Prices) (palette : NodeSet) (g : Graph) :
    count .assignmentWrite (colorRun prices palette g).2 = (select (KeySet.cardinal palette) g).length := by
  rw [colorRun_count, selectRun_count]
  simp only [selectionCount, reduceCtorEq, ite_false, Nat.zero_add]
  exact colorListRun_writes_suffix palette g (select (KeySet.cardinal palette) g) [] rfl

theorem colorsStep_arithmetic (f : Assignment) (key : Node) (used : NodeSet) :
    arithmeticHom (colorsStep f key used).2 = 0 := by
  cases found : SparseMap.find key f <;>
    simp only [colorsStep, bind_projection, observe_projection, arithmeticHom_mark, lookup_arithmetic,
      observe_value, lookup_value, found, pure, map_zero, insertSet_arithmetic, Nat.zero_add]

theorem colorsOfRun_arithmetic (f : Assignment) (vertices : NodeSet) :
    arithmeticHom (colorsOfRun f vertices).2 = 0 := by
  simp only [colorsOfRun, enter_projection, arithmeticHom_structural, arithmeticHom_mark,
    setFold_arithmetic_zero _ (colorsStep_arithmetic f), Nat.zero_add]

theorem availableColorsRun_arithmetic (palette : NodeSet) (g : Graph) (key : Node) (f : Assignment) :
    arithmeticHom (availableColorsRun palette g key f).2 = 0 := by
  simp only [availableColorsRun, enter_projection, bind_projection, observe_projection,
    arithmeticHom_structural, arithmeticHom_mark, adjRun_arithmetic, colorsOfRun_arithmetic,
    difference_arithmetic, Nat.zero_add]

theorem color1Run_arithmetic (palette : NodeSet) (g : Graph) (key : Node) (f : Assignment) :
    arithmeticHom (color1Run palette g key f).2 = 0 := by
  cases chosen : KeySet.choose (availableColors palette g key f) <;>
    simp only [color1Run, enter_projection, bind_projection, observe_projection,
      arithmeticHom_structural, arithmeticHom_mark, availableColorsRun_arithmetic,
      availableColorsRun_value, choose_arithmetic, observe_value, choose_value,
      chosen, pure, map_zero, insertMap_arithmetic, Nat.zero_add]

theorem colorListRun_arithmetic (palette : NodeSet) (g : Graph) (vertices : List Node) :
    arithmeticHom (colorListRun palette g vertices).2 = 0 := by
  simp only [colorListRun, enter_projection, arithmeticHom_structural, arithmeticHom_mark,
    listFold_arithmetic_zero _ (color1Run_arithmetic palette g), Nat.zero_add]

theorem colorRun_structural_eq (prices other : Prices) (palette : NodeSet) (g : Graph) :
    structuralHom (colorRun prices palette g).2 = structuralHom (colorRun other palette g).2 := by
  simp only [colorRun, enter_projection, bind_projection, observe_projection,
    structuralHom_structural, structuralHom_mark, cardinality_structural,
    observe_value, cardinality_value, selectRun_value]
  rw [selectRun_structural_eq prices other]

/-- The explicit sum of prices at the arithmetic operands actually reached. -/
def arithmeticTariff (prices : Prices) (palette : NodeSet) (g : Graph) : Nat :=
  Resources.PositiveTrie.Cardinality.arithmeticWork id prices.addition palette +
    ((residuals (select (KeySet.cardinal palette) g) g).map (scanTariff prices (KeySet.cardinal palette))).sum

theorem colorRun_arithmetic (prices : Prices) (palette : NodeSet) (g : Graph) :
    arithmeticHom (colorRun prices palette g).2 = arithmeticTariff prices palette g := by
  simp only [colorRun, enter_projection, bind_projection, observe_projection,
    arithmeticHom_structural, arithmeticHom_mark, cardinality_arithmetic,
    observe_value, cardinality_value, selectRun_value, selectRun_arithmetic,
    colorListRun_arithmetic, Nat.add_zero, Nat.zero_add, arithmeticTariff]

theorem arithmeticTariff_unit (palette : NodeSet) (g : Graph) :
    arithmeticTariff unitPrices palette g = palette.numNodes + KeySet.cardinal palette +
      ((residuals (select (KeySet.cardinal palette) g) g).map (fun current =>
        ((SparseMap.elements current).map (fun entry => entry.2.numNodes + KeySet.cardinal entry.2 + 1)).sum)).sum := by
  have scans : scanTariff unitPrices (KeySet.cardinal palette) =
      (fun current => ((SparseMap.elements current).map
        (fun entry => entry.2.numNodes + KeySet.cardinal entry.2 + 1)).sum) := by
    funext current
    simp only [scanTariff, unitPrices,
      Resources.PositiveTrie.Cardinality.arithmeticWork_unit,
      Resources.PositiveTrie.Cardinality.occupiedCount_id]
  rw [arithmeticTariff, scans]
  simp only [unitPrices,
    Resources.PositiveTrie.Cardinality.arithmeticWork_unit,
    Resources.PositiveTrie.Cardinality.occupiedCount_id]

/-- No subtraction or positivity of prices is needed to change arithmetic tariffs. -/
theorem colorRun_reprice (prices other : Prices) (palette : NodeSet) (g : Graph) :
    work (colorRun prices palette g).2 + arithmeticTariff other palette g =
      work (colorRun other palette g).2 + arithmeticTariff prices palette g := by
  have structural := colorRun_structural_eq prices other palette g
  have left := colorRun_arithmetic prices palette g
  have right := colorRun_arithmetic other palette g
  change (colorRun prices palette g).2.1.1 = (colorRun other palette g).2.1.1 at structural
  change (colorRun prices palette g).2.1.2 = arithmeticTariff prices palette g at left
  change (colorRun other palette g).2.1.2 = arithmeticTariff other palette g at right
  unfold work
  omega

end Resources.Coloring
