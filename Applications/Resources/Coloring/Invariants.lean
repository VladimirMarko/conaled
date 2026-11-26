import Applications.Graphs.Coloring.Construction
import Applications.Graphs.Coloring.Support
import Applications.Search.PositiveTrie.Normalized
import Applications.Resources.WorkloadBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Representation invariants and degree mass for Color

Normalization and bit bounds are resource premises, separate from the raw
semantic theorem. Neighbor bounds include dangling keys. The finite sums in
this owner are proof observations and introduce no execution into Color.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.Coloring

open Search.PositiveTrie Numerals.PositiveArithmetic Graphs.Coloring
open scoped BigOperators

structure SetValid (bits : Nat) (set : NodeSet) : Prop where
  normal : KeySet.Normalized set
  bounded : ∀ key, KeySet.mem key set = true → bitLength key ≤ bits

structure GraphValid (bits : Nat) (g : Graph) : Prop where
  normal : SparseMap.Normalized g
  bitLength_le : ∀ key value, SparseMap.find key g = some value → bitLength key ≤ bits
  payload : ∀ key value, SparseMap.find key g = some value → SetValid bits value

structure AssignmentValid (bits : Nat) (palette : NodeSet) (f : Assignment) : Prop where
  normal : SparseMap.Normalized f
  bitLength_le : ∀ key value, SparseMap.find key f = some value → bitLength key ≤ bits
  paletteValued : PaletteValued palette f

theorem SetValid.nil (bits : Nat) : SetValid bits .nil := by
  refine ⟨KeySet.normalized_nil, ?_⟩
  intro key member
  simp only [KeySet.mem_nil, Bool.false_eq_true] at member

theorem SetValid.add {bits : Nat} {set : NodeSet} (valid : SetValid bits set)
    (key : Node) (bounded : bitLength key ≤ bits) : SetValid bits (KeySet.add key set) := by
  refine ⟨KeySet.normalized_add key valid.normal, ?_⟩
  intro query member
  simp only [KeySet.mem_add, Bool.or_eq_true, decide_eq_true_eq] at member
  rcases member with rfl | old
  · exact bounded
  · exact valid.bounded query old

theorem SetValid.erase {bits : Nat} {set : NodeSet} (valid : SetValid bits set)
    (key : Node) : SetValid bits (KeySet.erase key set) := by
  refine ⟨KeySet.normalized_erase key valid.normal, ?_⟩
  intro query member
  by_cases same : query = key
  · simp only [same, KeySet.mem_erase_same, Bool.false_eq_true] at member
  · rw [KeySet.mem_erase_other key query set same] at member
    exact valid.bounded query member

theorem SetValid.diff {bits : Nat} {set : NodeSet} (valid : SetValid bits set)
    (other : NodeSet) : SetValid bits (KeySet.diff set other) := by
  refine ⟨KeySet.normalized_diff valid.normal other, ?_⟩
  intro query member
  simp only [KeySet.mem_diff, Bool.and_eq_true] at member
  exact valid.bounded query member.1

theorem SetValid.nodes_le {bits : Nat} {set : NodeSet} (valid : SetValid bits set) :
    set.numNodes ≤ KeySet.cardinal set * bits :=
  KeySet.numNodes_le_cardinal_mul valid.normal bits valid.bounded

theorem GraphValid.nil (bits : Nat) : GraphValid bits .nil := by
  refine ⟨SparseMap.normalized_nil, ?_, ?_⟩ <;> intro key value found <;>
    simp only [SparseMap.find_nil, reduceCtorEq] at found

theorem GraphValid.adj {bits : Nat} {g : Graph} (valid : GraphValid bits g) (key : Node) :
    SetValid bits (adj g key) := by
  cases found : SparseMap.find key g with
  | none => rw [adj_of_find_none found]; exact SetValid.nil bits
  | some value => rw [adj_of_find_some found]; exact valid.payload key value found

theorem GraphValid.mem_bits {bits : Nat} {g : Graph} (valid : GraphValid bits g)
    {key : Node} (member : key ∈ SparseMap.keys g) : bitLength key ≤ bits := by
  obtain ⟨value, found⟩ := (SparseMap.mem_keys key g).mp member
  exact valid.bitLength_le key value found

theorem GraphValid.add {bits : Nat} {g : Graph} (valid : GraphValid bits g)
    (key : Node) (value : NodeSet) (keyBound : bitLength key ≤ bits) (payload : SetValid bits value) :
    GraphValid bits (SparseMap.add key value g) := by
  refine ⟨SparseMap.normalized_add key value valid.normal, ?_, ?_⟩
  · intro query result found
    rw [SparseMap.find_add] at found
    split_ifs at found with same
    · simpa only [same] using keyBound
    · exact valid.bitLength_le query result found
  · intro query result found
    rw [SparseMap.find_add] at found
    split_ifs at found with same
    · cases found
      exact payload
    · exact valid.payload query result found

theorem GraphValid.remove {bits : Nat} {g : Graph} (valid : GraphValid bits g) (erased : Node) :
    GraphValid bits (removeNode erased g) := by
  have original (query : Node) (value : NodeSet)
      (found : SparseMap.find query (removeNode erased g) = some value) :
      ∃ old, SparseMap.find query g = some old ∧ value = KeySet.erase erased old := by
    by_cases same : query = erased
    · simp only [find_removeNode, same, ite_true, reduceCtorEq] at found
    · rw [find_removeNode, ite_eq_right same] at found
      cases oldFound : SparseMap.find query g with
      | none => simp [oldFound] at found
      | some old =>
          simp only [oldFound, Option.map_some, Option.some.injEq] at found
          exact ⟨old, rfl, found.symm⟩
  refine ⟨SparseMap.normalized_map _ (SparseMap.normalized_erase erased valid.normal), ?_, ?_⟩
  · intro query value found
    obtain ⟨old, oldFound, _⟩ := original query value found
    exact valid.bitLength_le query old oldFound
  · intro query value found
    obtain ⟨old, oldFound, rfl⟩ := original query value found
    exact (valid.payload query old oldFound).erase erased

theorem GraphValid.erase {bits : Nat} {g : Graph} (valid : GraphValid bits g) (erased : Node) :
    GraphValid bits (SparseMap.erase erased g) := by
  have original (query : Node) (value : NodeSet)
      (found : SparseMap.find query (SparseMap.erase erased g) = some value) :
      SparseMap.find query g = some value := by
    by_cases same : query = erased
    · simp only [SparseMap.find_erase, same, ite_true, reduceCtorEq] at found
    · simpa only [SparseMap.find_erase, ite_eq_right same] using found
  exact ⟨SparseMap.normalized_erase erased valid.normal,
    fun query value found => valid.bitLength_le query value (original query value found),
    fun query value found => valid.payload query value (original query value found)⟩

theorem GraphValid.removeNodes {bits : Nat} {g : Graph} (valid : GraphValid bits g)
    (removed : List Node) : GraphValid bits (removeNodes removed g) := by
  induction removed generalizing g with
  | nil => exact valid
  | cons key rest ih => exact ih (valid.remove key)

theorem GraphValid.addEdge {bits : Nat} {g : Graph} (valid : GraphValid bits g)
    (edge : Node × Node) (left : bitLength edge.1 ≤ bits) (right : bitLength edge.2 ≤ bits) :
    GraphValid bits (addEdge edge g) :=
  (valid.add edge.2 _ right ((valid.adj edge.2).add edge.1 left)).add edge.1 _ left
    ((valid.adj edge.1).add edge.2 right)

theorem mkGraph_valid (bits : Nat) (edges : List (Node × Node))
    (bounded : ∀ edge ∈ edges, bitLength edge.1 ≤ bits ∧ bitLength edge.2 ≤ bits) :
    GraphValid bits (mkGraph edges) := by
  induction edges with
  | nil => exact GraphValid.nil bits
  | cons edge edges ih =>
      have hb := bounded edge (List.mem_cons_self)
      exact (ih (fun e he => bounded e (List.mem_cons_of_mem edge he))).addEdge edge hb.1 hb.2

theorem GraphValid.nodes_le {bits : Nat} {g : Graph} (valid : GraphValid bits g) :
    g.numNodes ≤ SparseMap.cardinal g * bits :=
  SparseMap.numNodes_le_cardinal_mul valid.normal bits valid.bitLength_le

theorem GraphValid.eq_nil_of_cardinal_zero {bits : Nat} {g : Graph} (valid : GraphValid bits g)
    (empty : SparseMap.cardinal g = 0) : g = .nil :=
  (SparseMap.cardinal_eq_zero_iff_of_normalized valid.normal).mp empty

theorem subsetNodes_valid {bits : Nat} {g : Graph} (valid : GraphValid bits g)
    (predicate : Node → NodeSet → Bool) : SetValid bits (subsetNodes predicate g) := by
  let step (entry : Node × NodeSet) (state : NodeSet) : Measured NodeSet Nat :=
    (if predicate entry.1 entry.2 then KeySet.add entry.1 state else state, 0)
  have h := Resources.run_invariant_on step
    (fun entry => SparseMap.find entry.1 g = some entry.2) (SetValid bits)
    (fun entry state found hs => by
      dsimp only [step]
      split_ifs
      · exact hs.add entry.1 (valid.bitLength_le entry.1 entry.2 found)
      · exact hs)
    (SparseMap.elements g)
    (fun entry member => (SparseMap.mem_elements entry.1 entry.2 g).mp member)
    .nil (SetValid.nil bits)
  rw [Resources.run_state] at h
  simpa only [step, subsetNodes, SparseMap.fold_eq] using h

theorem eligible_valid {bits : Nat} {g : Graph} (valid : GraphValid bits g) (bound : Nat) :
    SetValid bits (eligible bound g) := subsetNodes_valid valid (lowDegree bound)

theorem nodes_valid {bits : Nat} {g : Graph} (valid : GraphValid bits g) : SetValid bits (nodes g) :=
  subsetNodes_valid valid (fun _ _ => true)

def degree (g : Graph) (key : Node) : Nat := KeySet.cardinal (adj g key)

def degreeMass (g : Graph) : Nat := ∑ key ∈ SparseMap.keys g, degree g key

/-- Each ordered entry is a unique stored key with exactly its lookup payload. -/
theorem sum_entries (weight : Node → NodeSet → Nat) (g : Graph) :
    (∑ key ∈ SparseMap.keys g, weight key (adj g key)) =
      ((SparseMap.elements g).map (fun entry => weight entry.1 entry.2)).sum := by
  rw [SparseMap.keys, List.sum_toFinset _ (SparseMap.keys_nodup g), List.map_map]
  congr 1
  apply List.map_congr_left
  intro entry member
  exact congrArg (weight entry.1) (adj_of_find_some ((SparseMap.mem_elements entry.1 entry.2 g).mp member))

theorem sum_payloads (weight : NodeSet → Nat) (g : Graph) :
    (∑ key ∈ SparseMap.keys g, weight (adj g key)) =
      ((SparseMap.elements g).map (fun entry => weight entry.2)).sum :=
  sum_entries (fun _ => weight) g

theorem subsetNodes_observe_filter (predicate : Node → NodeSet → Bool) (g : Graph) :
    KeySet.observe (subsetNodes predicate g) =
      (SparseMap.keys g).filter (fun key => predicate key (adj g key) = true) := by
  ext key
  rw [KeySet.mem_observe, mem_subsetNodes, Finset.mem_filter, SparseMap.mem_keys]
  constructor
  · rintro ⟨value, found, accepted⟩
    exact ⟨⟨value, found⟩, by rwa [adj_of_find_some found]⟩
  · rintro ⟨⟨value, found⟩, accepted⟩
    exact ⟨value, found, by rwa [adj_of_find_some found] at accepted⟩

theorem subsetNodes_cardinal (predicate : Node → NodeSet → Bool) (g : Graph) :
    KeySet.cardinal (subsetNodes predicate g) =
      ((SparseMap.elements g).map (fun entry => if predicate entry.1 entry.2 then 1 else 0)).sum := by
  have h := Finset.sum_boole (R := Nat)
    (fun key => predicate key (adj g key) = true) (SparseMap.keys g)
  simp only [Nat.cast_id] at h
  rw [← KeySet.observe_card, subsetNodes_observe_filter, ← h]
  exact sum_entries (fun key value => if predicate key value then 1 else 0) g

theorem eligible_cardinal_le (bound : Nat) (g : Graph) :
    KeySet.cardinal (eligible bound g) ≤ SparseMap.cardinal g := by
  rw [← KeySet.observe_card, eligible, subsetNodes_observe_filter, ← SparseMap.keys_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem degreeMass_entries (g : Graph) :
    degreeMass g = ((SparseMap.elements g).map (fun entry => KeySet.cardinal entry.2)).sum :=
  sum_payloads KeySet.cardinal g

theorem sum_degree_weight (a c : Nat) (g : Graph) :
    ((SparseMap.elements g).map (fun entry => a * KeySet.cardinal entry.2 + c)).sum =
      a * degreeMass g + SparseMap.cardinal g * c := by
  rw [← sum_payloads (fun value => a * KeySet.cardinal value + c) g]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul, SparseMap.keys_card, degreeMass, degree, Nat.cast_id]

theorem degree_remove_le (erased key : Node) (g : Graph) :
    degree (removeNode erased g) key ≤ degree g key := by
  unfold degree
  rw [adj_removeNode]
  split_ifs
  · exact Nat.zero_le _
  · have h := KeySet.cardinal_erase_add erased (adj g key)
    omega

theorem degreeMass_remove_le (erased : Node) (g : Graph) :
    degreeMass (removeNode erased g) ≤ degreeMass g := by
  unfold degreeMass
  rw [keys_removeNode]
  exact (Finset.sum_le_sum (fun key _ => degree_remove_le erased key g)).trans
    (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))

theorem degreeMass_removeNodes_le (removed : List Node) (g : Graph) :
    degreeMass (removeNodes removed g) ≤ degreeMass g := by
  induction removed generalizing g with
  | nil => exact Nat.le_refl _
  | cons key rest ih => exact (ih (removeNode key g)).trans (degreeMass_remove_le key g)

theorem selected_degrees_le (bound : Nat) (g : Graph) :
    ((select bound g).map (degree g)).sum ≤ degreeMass g := by
  rw [← List.sum_toFinset (degree g) (select_nodup bound g)]
  apply Finset.sum_le_sum_of_subset
  intro key member
  exact mem_select bound g (List.mem_toFinset.mp member)

theorem GraphValid.adjacency_nodes_le {bits : Nat} {g : Graph} (valid : GraphValid bits g) :
    (∑ key ∈ SparseMap.keys g, (Graphs.Coloring.adj g key).numNodes) ≤ degreeMass g * bits := by
  calc
    _ ≤ ∑ key ∈ SparseMap.keys g, degree g key * bits :=
      Finset.sum_le_sum (fun key _ => (valid.adj key).nodes_le)
    _ = degreeMass g * bits := (Finset.sum_mul _ _ _).symm

theorem AssignmentValid.nil (bits : Nat) (palette : NodeSet) : AssignmentValid bits palette .nil := by
  refine ⟨SparseMap.normalized_nil, ?_, paletteValued_nil palette⟩
  intro key value found
  simp only [SparseMap.find_nil, reduceCtorEq] at found

theorem AssignmentValid.add {bits : Nat} {palette : NodeSet} {f : Assignment}
    (valid : AssignmentValid bits palette f) (key color : Node)
    (bounded : bitLength key ≤ bits) (member : KeySet.mem color palette = true) :
    AssignmentValid bits palette (SparseMap.add key color f) := by
  refine ⟨SparseMap.normalized_add key color valid.normal, ?_, ?_⟩
  · intro query value found
    by_cases same : query = key
    · simpa only [same] using bounded
    · exact valid.bitLength_le query value (by rwa [SparseMap.find_add_other key query color f same] at found)
  · intro query value found
    by_cases same : query = key
    · subst query
      rw [SparseMap.find_add_same] at found
      cases found
      exact member
    · exact valid.paletteValued query value (by rwa [SparseMap.find_add_other key query color f same] at found)

theorem AssignmentValid.color1 {bits : Nat} {palette : NodeSet} {f : Assignment}
    (valid : AssignmentValid bits palette f) (g : Graph) (key : Node)
    (bounded : bitLength key ≤ bits) : AssignmentValid bits palette (color1 palette g key f) := by
  cases chosen : KeySet.choose (availableColors palette g key f) with
  | none => rwa [color1_of_none chosen]
  | some color =>
      rw [color1_of_some chosen]
      exact valid.add key color bounded (chosen_color_facts chosen).1

theorem colorList_valid (bits : Nat) (palette : NodeSet) (g : Graph) (vertices : List Node)
    (bounded : ∀ key ∈ vertices, bitLength key ≤ bits) :
    AssignmentValid bits palette (colorList palette g vertices) := by
  induction vertices with
  | nil => exact AssignmentValid.nil bits palette
  | cons key vertices ih =>
      exact (ih (fun v hv => bounded v (List.mem_cons_of_mem key hv))).color1 g key
        (bounded key (List.mem_cons_self))

theorem color_valid {bits : Nat} {g : Graph} (valid : GraphValid bits g) (palette : NodeSet) :
    AssignmentValid bits palette (color palette g) :=
  colorList_valid bits palette g (select (KeySet.cardinal palette) g)
    (fun _key member => valid.mem_bits (mem_select _ _ member))

theorem colorsOf_valid {bits : Nat} {palette : NodeSet} (valid : SetValid bits palette)
    (f : Assignment) (colors : PaletteValued palette f) (vertices : NodeSet) :
    SetValid bits (colorsOf f vertices) := by
  let step (key : Node) (state : NodeSet) : Measured NodeSet Nat :=
    (match SparseMap.find key f with
      | some color => KeySet.add color state
      | none => state, 0)
  have h := Resources.run_invariant_on step (fun _ => True) (SetValid bits)
    (fun key state _ hs => by
      dsimp only [step]
      cases found : SparseMap.find key f with
      | none => exact hs
      | some color => exact hs.add color (valid.bounded color (colors key color found)))
    (KeySet.elements vertices) (fun _ _ => True.intro) .nil (SetValid.nil bits)
  have value : (Resources.run step (KeySet.elements vertices) .nil).1 = colorsOf f vertices := by
    rw [Resources.run_state, colorsOf, KeySet.fold_eq]
    congr 1
  exact value ▸ h

theorem availableColors_valid {bits : Nat} {palette : NodeSet} (valid : SetValid bits palette)
    (g : Graph) (key : Node) (f : Assignment) : SetValid bits (availableColors palette g key f) :=
  valid.diff (colorsOf f (adj g key))

end Resources.Coloring
