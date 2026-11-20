import Applications.Graphs.Coloring.Graph
import Mathlib.Data.List.Nodup

/-!
# Source vertex selection and residual graphs

Selection keeps its degree bound fixed and stops at the first empty candidate
set, including on nonempty graphs. Termination uses occupied cardinality as
proof data. No graph validity or normalization premise is required.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Graphs.Coloring

open Search.PositiveTrie

def eligible (bound : Nat) (g : Graph) : NodeSet := subsetNodes (lowDegree bound) g

theorem mem_eligible (bound : Nat) (g : Graph) (node : Node) :
    KeySet.mem node (eligible bound g) = true ↔
      ∃ value, SparseMap.find node g = some value ∧ KeySet.cardinal value < bound := by
  simp only [eligible, mem_subsetNodes, lowDegree_eq_true]

theorem chosen_facts (bound : Nat) (g : Graph) {node : Node}
    (chosen : KeySet.choose (eligible bound g) = some node) :
    node ∈ SparseMap.keys g ∧ KeySet.cardinal (adj g node) < bound := by
  obtain ⟨value, found, small⟩ := (mem_eligible bound g node).mp (KeySet.choose_mem _ chosen)
  exact ⟨(SparseMap.mem_keys node g).mpr ⟨value, found⟩, by rwa [adj_of_find_some found]⟩

theorem select_terminates (bound : Nat) (g : Graph) (node : Node)
    (chosen : KeySet.choose (eligible bound g) = some node) :
    SparseMap.cardinal (removeNode node g) < SparseMap.cardinal g :=
  cardinal_removeNode_lt node g (chosen_facts bound g chosen).1

def select (bound : Nat) (g : Graph) : List Node :=
  match _chosen : KeySet.choose (eligible bound g) with
  | none => []
  | some node => node :: select bound (removeNode node g)
termination_by SparseMap.cardinal g
decreasing_by exact select_terminates bound g node _chosen

theorem select_of_none (bound : Nat) (g : Graph)
    (chosen : KeySet.choose (eligible bound g) = none) : select bound g = [] := by
  rw [select, chosen]

theorem select_of_some (bound : Nat) (g : Graph) {node : Node}
    (chosen : KeySet.choose (eligible bound g) = some node) :
    select bound g = node :: select bound (removeNode node g) := by
  rw [select, chosen]

theorem select_nil_iff (bound : Nat) (g : Graph) :
    select bound g = [] ↔ KeySet.choose (eligible bound g) = none := by
  constructor
  · intro empty
    cases chosen : KeySet.choose (eligible bound g) with
    | none => rfl
    | some node => rw [select_of_some bound g chosen] at empty; cases empty
  · exact select_of_none bound g

theorem select_cons_iff (bound : Nat) (g : Graph) (node : Node) (tail : List Node) :
    select bound g = node :: tail ↔ KeySet.choose (eligible bound g) = some node ∧
      select bound (removeNode node g) = tail := by
  constructor
  · intro selected
    cases chosen : KeySet.choose (eligible bound g) with
    | none => rw [select_of_none bound g chosen] at selected; cases selected
    | some first =>
        have same := List.cons.inj ((select_of_some bound g chosen).symm.trans selected)
        rcases same with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩
  · rintro ⟨chosen, tailEq⟩
    rw [select_of_some bound g chosen, tailEq]

theorem select_properties (bound : Nat) (g : Graph) :
    (∀ node ∈ select bound g, node ∈ SparseMap.keys g) ∧
      (select bound g).Nodup ∧ (select bound g).length ≤ SparseMap.cardinal g := by
  induction g using (measure SparseMap.cardinal).wf.induction with
  | h g ih =>
      cases chosen : KeySet.choose (eligible bound g) with
      | none => rw [select_of_none bound g chosen]; simp
      | some node =>
          have present := (chosen_facts bound g chosen).1
          have previous := ih (removeNode node g) (select_terminates bound g node chosen)
          rw [select_of_some bound g chosen]
          refine ⟨?_, ?_, ?_⟩
          · intro query member
            rcases List.mem_cons.mp member with same | member
            · simpa only [same] using present
            · have key := previous.1 query member
              rw [keys_removeNode] at key
              exact (Finset.mem_erase.mp key).2
          · apply List.nodup_cons.mpr
            refine ⟨?_, previous.2.1⟩
            intro member
            have key := previous.1 node member
            rw [keys_removeNode] at key
            exact (Finset.mem_erase.mp key).1 rfl
          · have cards := cardinal_removeNode_of_mem node g present
            have lengthBound := previous.2.2
            simp only [List.length_cons]
            omega

theorem mem_select (bound : Nat) (g : Graph) {node : Node}
    (member : node ∈ select bound g) : node ∈ SparseMap.keys g :=
  (select_properties bound g).1 node member

theorem select_nodup (bound : Nat) (g : Graph) : (select bound g).Nodup :=
  (select_properties bound g).2.1

theorem select_length_le_cardinal (bound : Nat) (g : Graph) :
    (select bound g).length ≤ SparseMap.cardinal g := (select_properties bound g).2.2

def removeNodes (removed : List Node) (g : Graph) : Graph :=
  removed.foldl (fun current node => removeNode node current) g

@[simp] theorem removeNodes_nil (g : Graph) : removeNodes [] g = g := rfl

theorem removeNodes_cons (node : Node) (removed : List Node) (g : Graph) :
    removeNodes (node :: removed) g = removeNodes removed (removeNode node g) := rfl

theorem removeNodes_append (first second : List Node) (g : Graph) :
    removeNodes (first ++ second) g = removeNodes second (removeNodes first g) :=
  List.foldl_append

theorem keys_removeNodes (removed : List Node) (g : Graph) :
    SparseMap.keys (removeNodes removed g) = SparseMap.keys g \ removed.toFinset := by
  induction removed generalizing g with
  | nil => simp
  | cons node removed ih =>
      rw [removeNodes_cons, ih, keys_removeNode]
      ext query
      simp [Finset.mem_sdiff, Finset.mem_erase, and_assoc, and_left_comm, and_comm]

theorem adjacent_removeNodes (removed : List Node) (g : Graph) (left right : Node) :
    Adjacent (removeNodes removed g) left right ↔
      left ∉ removed ∧ right ∉ removed ∧ Adjacent g left right := by
  induction removed generalizing g with
  | nil => simp
  | cons node removed ih =>
      rw [removeNodes_cons, ih, adjacent_removeNode]
      simp [and_assoc, and_left_comm]

theorem neighbors_removeNodes (removed : List Node) (g : Graph) (node : Node) :
    neighbors (removeNodes removed g) node =
      if node ∈ removed then ∅ else neighbors g node \ removed.toFinset := by
  ext query
  rw [mem_neighbors, adjacent_removeNodes]
  by_cases present : node ∈ removed <;>
    simp [present, Finset.mem_sdiff, mem_neighbors, and_comm]

theorem undirected_removeNodes {g : Graph} (symmetric : Undirected g) (removed : List Node) :
    Undirected (removeNodes removed g) := by
  induction removed generalizing g with
  | nil => exact symmetric
  | cons node removed ih => exact ih (undirected_removeNode symmetric node)

theorem noSelfLoop_removeNodes {g : Graph} (loopless : NoSelfLoop g) (removed : List Node) :
    NoSelfLoop (removeNodes removed g) := by
  induction removed generalizing g with
  | nil => exact loopless
  | cons node removed ih => exact ih (noSelfLoop_removeNode loopless node)

theorem select_removeNodes_of_append (bound : Nat) (g : Graph) (before after : List Node)
    (selected : select bound g = before ++ after) :
    select bound (removeNodes before g) = after := by
  induction before generalizing g with
  | nil => simpa only [removeNodes_nil, List.nil_append] using selected
  | cons node before ih =>
      obtain ⟨_, remaining⟩ := (select_cons_iff bound g node (before ++ after)).mp selected
      rw [removeNodes_cons]
      exact ih (removeNode node g) remaining

theorem select_removeNodes_take (bound : Nat) (g : Graph) (count : Nat) :
    select bound (removeNodes ((select bound g).take count) g) =
      (select bound g).drop count :=
  select_removeNodes_of_append bound g _ _ (List.take_append_drop count _).symm

theorem select_removeNodes_all (bound : Nat) (g : Graph) :
    select bound (removeNodes (select bound g) g) = [] :=
  select_removeNodes_of_append bound g _ [] (List.append_nil _).symm

theorem choose_after_prefix (bound : Nat) (g : Graph) (before after : List Node) (node : Node)
    (selected : select bound g = before ++ node :: after) :
    KeySet.choose (eligible bound (removeNodes before g)) = some node :=
  ((select_cons_iff bound (removeNodes before g) node after).mp
    (select_removeNodes_of_append bound g before (node :: after) selected)).1

theorem current_vertex (bound : Nat) (g : Graph) (before after : List Node) (node : Node)
    (selected : select bound g = before ++ node :: after) :
    node ∈ SparseMap.keys (removeNodes before g) ∧
      KeySet.cardinal (adj (removeNodes before g) node) < bound :=
  chosen_facts bound _ (choose_after_prefix bound g before after node selected)

theorem select_nil_iff_degrees (bound : Nat) (g : Graph) :
    select bound g = [] ↔ ∀ node value, SparseMap.find node g = some value →
      bound ≤ KeySet.cardinal value := by
  rw [select_nil_iff, KeySet.choose_none_iff]
  constructor
  · intro empty node value found
    by_contra notLarge
    have small : KeySet.cardinal value < bound := by omega
    have member := (mem_eligible bound g node).mpr ⟨value, found, small⟩
    rw [empty node] at member
    cases member
  · intro large node
    cases member : KeySet.mem node (eligible bound g) with
    | false => rfl
    | true =>
        obtain ⟨value, found, small⟩ := (mem_eligible bound g node).mp member
        have lower := large node value found
        omega

@[simp] theorem select_zero (g : Graph) : select 0 g = [] :=
  (select_nil_iff_degrees 0 g).mpr (fun _ _ _ => Nat.zero_le _)

theorem terminal_choose_none (bound : Nat) (g : Graph) :
    KeySet.choose (eligible bound (removeNodes (select bound g) g)) = none :=
  (select_nil_iff bound _).mp (select_removeNodes_all bound g)

theorem terminal_degree (bound : Nat) (g : Graph) (node : Node) (value : NodeSet)
    (found : SparseMap.find node (removeNodes (select bound g) g) = some value) :
    bound ≤ KeySet.cardinal value :=
  (select_nil_iff_degrees bound _).mp (select_removeNodes_all bound g) node value found

theorem cardinal_removeNodes_of_append (bound : Nat) (g : Graph) (before after : List Node)
    (selected : select bound g = before ++ after) :
    SparseMap.cardinal (removeNodes before g) = SparseMap.cardinal g - before.length := by
  have distinct : (before ++ after).Nodup := selected ▸ select_nodup bound g
  have supported : before.toFinset ⊆ SparseMap.keys g := by
    intro node member
    apply mem_select bound g
    rw [selected]
    exact List.mem_append_left after (List.mem_toFinset.mp member)
  calc
    SparseMap.cardinal (removeNodes before g)
        = (SparseMap.keys (removeNodes before g)).card := (SparseMap.keys_card _).symm
    _ = (SparseMap.keys g \ before.toFinset).card := by rw [keys_removeNodes]
    _ = (SparseMap.keys g).card - before.toFinset.card :=
      Finset.card_sdiff_of_subset supported
    _ = SparseMap.cardinal g - before.length := by
      rw [SparseMap.keys_card, List.toFinset_card_of_nodup distinct.of_append_left]

theorem cardinal_removeNodes_take (bound : Nat) (g : Graph) (count : Nat)
    (within : count ≤ (select bound g).length) :
    SparseMap.cardinal (removeNodes ((select bound g).take count) g) =
      SparseMap.cardinal g - count := by
  rw [cardinal_removeNodes_of_append bound g _ _ (List.take_append_drop count _).symm,
    List.length_take_of_le within]

/-- Only original neighbors lying in the later suffix are bounded here. -/
theorem later_neighbors_card_lt (bound : Nat) (g : Graph)
    (before after : List Node) (node : Node)
    (selected : select bound g = before ++ node :: after) :
    (neighbors g node ∩ after.toFinset).card < bound := by
  have distinct : (before ++ node :: after).Nodup := selected ▸ select_nodup bound g
  obtain ⟨nodeNotBefore, separated⟩ :=
    List.disjoint_cons_right.mp distinct.disjoint
  have contained : neighbors g node ∩ after.toFinset ⊆
      neighbors (removeNodes before g) node := by
    intro query member
    obtain ⟨edge, later⟩ := Finset.mem_inter.mp member
    rw [mem_neighbors, adjacent_removeNodes]
    exact ⟨nodeNotBefore, fun prior => separated prior (List.mem_toFinset.mp later),
      (mem_neighbors g node query).mp edge⟩
  calc
    (neighbors g node ∩ after.toFinset).card
        ≤ (neighbors (removeNodes before g) node).card := Finset.card_le_card contained
    _ = KeySet.cardinal (adj (removeNodes before g) node) := neighbors_card _ _
    _ < bound := (current_vertex bound g before after node selected).2

/-- Totality is conditional on progress of the supplied removal-closed class. -/
theorem select_covers_of_progress (bound : Nat) (property : Graph → Prop)
    (closed : ∀ g node, property g → node ∈ SparseMap.keys g →
      property (removeNode node g))
    (progress : ∀ g, property g → (SparseMap.keys g).Nonempty →
      ∃ node, KeySet.mem node (eligible bound g) = true)
    (g : Graph) (valid : property g) : (select bound g).toFinset = SparseMap.keys g := by
  induction g using (measure SparseMap.cardinal).wf.induction with
  | h g ih =>
      cases chosen : KeySet.choose (eligible bound g) with
      | none =>
          have empty : SparseMap.keys g = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro node member
            obtain ⟨candidate, eligibleNode⟩ := progress g valid ⟨node, member⟩
            have absent := (KeySet.choose_none_iff _).mp chosen candidate
            rw [absent] at eligibleNode
            cases eligibleNode
          rw [select_of_none bound g chosen, empty]
          rfl
      | some node =>
          have present := (chosen_facts bound g chosen).1
          have remaining := ih (removeNode node g) (select_terminates bound g node chosen)
            (closed g node valid present)
          rw [select_of_some bound g chosen, List.toFinset_cons, remaining, keys_removeNode,
            Finset.insert_erase present]

theorem eligible_observe_congr (bound : Nat) {g h : Graph} (same : observe g = observe h) :
    KeySet.observe (eligible bound g) = KeySet.observe (eligible bound h) :=
  subsetNodes_observe_congr (lowDegree bound) (lowDegree_congr bound) same

theorem choose_eligible_congr (bound : Nat) {g h : Graph} (same : observe g = observe h) :
    KeySet.choose (eligible bound g) = KeySet.choose (eligible bound h) := by
  apply KeySet.choose_ext
  intro node
  apply Bool.eq_iff_iff.mpr
  rw [← KeySet.mem_observe, ← KeySet.mem_observe, eligible_observe_congr bound same]

theorem select_observe_congr (bound : Nat) {g h : Graph} (same : observe g = observe h) :
    select bound g = select bound h := by
  induction g using (measure SparseMap.cardinal).wf.induction generalizing h with
  | h g ih =>
      have choices := choose_eligible_congr bound same
      cases chosen : KeySet.choose (eligible bound g) with
      | none =>
          have other := choices.symm.trans chosen
          rw [select_of_none bound g chosen, select_of_none bound h other]
      | some node =>
          have other := choices.symm.trans chosen
          rw [select_of_some bound g chosen, select_of_some bound h other]
          exact congrArg (List.cons node)
            (ih (removeNode node g) (select_terminates bound g node chosen)
              (observe_removeNode_congr same node))

end Graphs.Coloring
