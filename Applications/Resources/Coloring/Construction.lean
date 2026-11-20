import Applications.Resources.Coloring.Helpers
import Mathlib.Tactic.Linarith

/-!
# Measured graph and palette construction

Both endpoint reads consume the old graph. The two returned adjacency sets are
inserted before the second endpoint and then the first endpoint are written.
The shared right fold executes every occurrence, including duplicate self-edges.
Construction is separate from the supplied-input coloring program.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.Coloring

open Search.PositiveTrie Numerals.PositiveArithmetic Graphs.Coloring

def addEdgeRun (edge : Node × Node) (g : Graph) : Measured Graph Cost :=
  enter .addEdge (bind (observe .edgeRead 1 (adjRun g edge.1)) (fun left =>
    bind (observe .edgeRead 1 (adjRun g edge.2)) (fun right =>
    bind (observe .edgeSetInsert 1 (insertSet edge.2 left)) (fun leftAdded =>
    bind (observe .edgeSetInsert 1 (insertSet edge.1 right)) (fun rightAdded =>
    bind (observe .edgeMapWrite 1 (insertMap edge.2 rightAdded g)) (fun second =>
    observe .edgeMapWrite 1 (insertMap edge.1 leftAdded second)))))))

def mkGraphRun (edges : List (Node × Node)) : Measured Graph Cost :=
  enter .mkGraph (listFold addEdgeRun edges .nil)

def paletteRun (colors : List Node) : Measured NodeSet Cost :=
  enter .paletteSetup (listFold (fun key state => observe .paletteInsert 1 (insertSet key state))
    colors .nil)

@[simp] theorem addEdgeRun_value (edge : Node × Node) (g : Graph) :
    (addEdgeRun edge g).1 = addEdge edge g := by
  simp only [addEdgeRun, enter_value, bind_value, observe_value, adjRun_value,
    insertSet_value, insertMap_value, addEdge]

@[simp] theorem mkGraphRun_value (edges : List (Node × Node)) :
    (mkGraphRun edges).1 = mkGraph edges := by
  simp only [mkGraphRun, enter_value, listFold_value, addEdgeRun_value, mkGraph]

@[simp] theorem paletteRun_value (colors : List Node) :
    (paletteRun colors).1 = colors.foldr KeySet.add .nil := by
  simp only [paletteRun, enter_value, listFold_value, observe_value, insertSet_value]

theorem addEdgeRun_valid {bits : Nat} {g : Graph} (valid : GraphValid bits g)
    (edge : Node × Node) (left : bitLength edge.1 ≤ bits) (right : bitLength edge.2 ≤ bits) :
    GraphValid bits (addEdgeRun edge g).1 := by
  rw [addEdgeRun_value]
  exact valid.addEdge edge left right

theorem mkGraphRun_valid (bits : Nat) (edges : List (Node × Node))
    (bounded : ∀ edge ∈ edges, bitLength edge.1 ≤ bits ∧ bitLength edge.2 ≤ bits) :
    GraphValid bits (mkGraphRun edges).1 := by
  rw [mkGraphRun_value]
  exact mkGraph_valid bits edges bounded

theorem mkGraphRun_keys (edges : List (Node × Node)) (key : Node) :
    key ∈ SparseMap.keys (mkGraphRun edges).1 ↔
      ∃ edge ∈ edges, key = edge.1 ∨ key = edge.2 := by
  rw [mkGraphRun_value]
  exact mem_keys_mkGraph edges key

theorem paletteRun_valid (bits : Nat) (colors : List Node)
    (bounded : ∀ key ∈ colors, bitLength key ≤ bits) : SetValid bits (paletteRun colors).1 := by
  rw [paletteRun_value]
  induction colors with
  | nil => exact SetValid.nil bits
  | cons key rest ih =>
      exact (ih (fun color member => bounded color (List.mem_cons_of_mem key member))).add key
        (bounded key (List.mem_cons_self))

theorem addEdgeRun_work (edge : Node × Node) (g : Graph) :
    work (addEdgeRun edge g).2 =
      1 + work (adjRun g edge.1).2 + work (adjRun g edge.2).2 +
        4 * (bitLength edge.1 + bitLength edge.2) := by
  simp only [addEdgeRun, enter_work, bind_work, observe_work, insertSet_work, insertMap_work]
  omega

theorem addEdgeRun_work_le (edge : Node × Node) (g : Graph) :
    work (addEdgeRun edge g).2 ≤ 5 * (bitLength edge.1 + bitLength edge.2) + 3 := by
  rw [addEdgeRun_work]
  have left := adjRun_work_le g edge.1
  have right := adjRun_work_le g edge.2
  omega

theorem mkGraphRun_work_nil : work (mkGraphRun []).2 = 2 := rfl

theorem mkGraphRun_work_cons (edge : Node × Node) (edges : List (Node × Node)) :
    work (mkGraphRun (edge :: edges)).2 =
      2 + work (mkGraphRun edges).2 + work (addEdgeRun edge (mkGraph edges)).2 := by
  have value : (listFold addEdgeRun edges .nil).1 = mkGraph edges := by
    simp only [listFold_value, addEdgeRun_value, mkGraph]
  simp only [mkGraphRun, enter_work, listFold_work_cons, value]
  omega

def edgeCount (event : Event) : Nat :=
  match event with
  | .addEdge => 1
  | .adj | .edgeRead | .edgeSetInsert | .edgeMapWrite => 2
  | _ => 0

theorem addEdgeRun_count (event : Event) (edge : Node × Node) (g : Graph) :
    count event (addEdgeRun edge g).2 = edgeCount event +
      (if event = .adjFound then
        (if (SparseMap.find edge.1 g).isSome then 1 else 0) +
        (if (SparseMap.find edge.2 g).isSome then 1 else 0) else 0) := by
  simp only [addEdgeRun, enter_count, bind_count, observe_count, adjRun_count,
    insertSet_count, insertMap_count]
  cases event <;> simp [edgeCount]

theorem mkGraphRun_count (event : Event) (notFound : event ≠ .adjFound)
    (edges : List (Node × Node)) :
    count event (mkGraphRun edges).2 = (if event = .mkGraph then 1 else 0) +
      (if event = .listEntry then edges.length + 1 else 0) +
      (if event = .listCallback then edges.length else 0) + edges.length * edgeCount event := by
  have h := run_projection (countHom event) addEdgeRun (fun _ => edgeCount event)
    (fun edge g => by
      change count event (addEdgeRun edge g).2 = _
      rw [addEdgeRun_count, ite_eq_right notFound, Nat.add_zero]) edges.reverse .nil
  change count event _ = _ at h
  simp only [mkGraphRun, enter_count, listFold_count, h, List.map_const',
    List.length_reverse, List.sum_replicate_nat]
  omega

def endpointMass (edges : List (Node × Node)) : Nat :=
  (edges.map (fun edge => bitLength edge.1 + bitLength edge.2)).sum

theorem mkGraphRun_work_le_mass (edges : List (Node × Node)) :
    work (mkGraphRun edges).2 ≤ 5 * endpointMass edges + 5 * edges.length + 2 := by
  have h := listFold_work_le_sum addEdgeRun (fun _ => True) (fun _ => True)
    (fun edge => 5 * (bitLength edge.1 + bitLength edge.2) + 3)
    (fun _ _ _ _ => trivial) (fun edge g _ _ => addEdgeRun_work_le edge g)
    edges (fun _ _ => trivial) .nil trivial
  have sum : (edges.map (fun edge => 5 * (bitLength edge.1 + bitLength edge.2) + 3)).sum =
      5 * endpointMass edges + 3 * edges.length := by
    clear h
    induction edges with
    | nil => rfl
    | cons edge rest ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, endpointMass] at ih ⊢
        rw [ih]
        ring
  rw [sum] at h
  rw [mkGraphRun, enter_work]
  omega

theorem mkGraphRun_work_le (bits : Nat) (positive : 1 ≤ bits) (edges : List (Node × Node))
    (bounded : ∀ edge ∈ edges, bitLength edge.1 ≤ bits ∧ bitLength edge.2 ≤ bits) :
    work (mkGraphRun edges).2 ≤ 15 * edges.length * bits + 2 := by
  have mass : endpointMass edges ≤ 2 * edges.length * bits := by
    induction edges with
    | nil => simp [endpointMass]
    | cons edge rest ih =>
        have head := bounded edge (List.mem_cons_self)
        have tail := ih (fun e member => bounded e (List.mem_cons_of_mem edge member))
        simp only [endpointMass, List.map_cons, List.sum_cons, List.length_cons] at tail ⊢
        nlinarith
  have h := mkGraphRun_work_le_mass edges
  have lengthBound := Nat.mul_le_mul_left edges.length positive
  nlinarith

theorem paletteRun_count (event : Event) (colors : List Node) :
    count event (paletteRun colors).2 = (if event = .paletteSetup then 1 else 0) +
      (if event = .listEntry then colors.length + 1 else 0) +
      (if event = .listCallback then colors.length else 0) +
      (if event = .paletteInsert then colors.length else 0) := by
  have h := run_projection (countHom event)
    (fun key state => observe .paletteInsert 1 (insertSet key state))
    (fun _ => if event = .paletteInsert then 1 else 0)
    (fun key state => by
      change count event (observe .paletteInsert 1 (insertSet key state)).2 = _
      simp only [observe_count, insertSet_count, Nat.add_zero]) colors.reverse .nil
  change count event _ = _ at h
  simp only [paletteRun, enter_count, listFold_count, h, List.map_const',
    List.length_reverse, List.sum_replicate_nat]
  split_ifs <;> omega

theorem paletteRun_work (colors : List Node) :
    work (paletteRun colors).2 = 2 * colors.length + 2 + 2 * (colors.map bitLength).sum := by
  have h : work (listFold (fun key state => observe .paletteInsert 1 (insertSet key state))
      colors .nil).2 = 2 * colors.length + 1 + 2 * (colors.map bitLength).sum := by
    induction colors with
    | nil => rfl
    | cons key rest ih =>
        rw [listFold_work_cons, observe_work, insertSet_work, ih]
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        omega
  rw [paletteRun, enter_work, h]
  omega

end Resources.Coloring
