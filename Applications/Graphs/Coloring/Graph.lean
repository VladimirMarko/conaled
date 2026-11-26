import Applications.Search.PositiveTrie.Enumeration

/-!
# Raw finite graphs for source graph coloring

Optional bindings retain stored isolated vertices. Adjacency alone uses an
empty default; the finite map observation retains the explicit domain as well.
All operation laws admit arbitrary raw tries, including padding and dangling
neighbors. Source correspondence is maintained in docs/research/vfa-color.md.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Graphs.Coloring

open Search.PositiveTrie

universe u

abbrev Node := PosNum
abbrev NodeSet := KeySet
abbrev NodeMap (α : Type u) := SparseMap α
abbrev Graph := NodeMap NodeSet

def adj (g : Graph) (node : Node) : NodeSet := (SparseMap.find node g).getD .nil

def Adjacent (g : Graph) (left right : Node) : Prop := KeySet.mem right (adj g left) = true

def Undirected (g : Graph) : Prop := ∀ left right, Adjacent g left right → Adjacent g right left

def NoSelfLoop (g : Graph) : Prop := ∀ node, ¬ Adjacent g node node

def nodes (g : Graph) : NodeSet := SparseMap.domain g

def neighbors (g : Graph) (node : Node) : Finset Node := KeySet.observe (adj g node)

/-- Finite observation preserves absence versus a stored empty adjacency set. -/
def observe (g : Graph) : Finmap (fun _ : Node => Finset Node) :=
  SparseMap.observe (SparseMap.map KeySet.observe g)

@[simp] theorem observe_lookup (g : Graph) (node : Node) :
    (observe g).lookup node = (SparseMap.find node g).map KeySet.observe := by
  rw [observe, SparseMap.observe_lookup, SparseMap.find_map]

@[simp] theorem observe_keys (g : Graph) : (observe g).keys = SparseMap.keys g := by
  rw [observe, SparseMap.observe_keys, SparseMap.keys_map]

@[simp] theorem mem_neighbors (g : Graph) (left right : Node) :
    right ∈ neighbors g left ↔ Adjacent g left right := KeySet.mem_observe right _

theorem neighbors_card (g : Graph) (node : Node) :
    (neighbors g node).card = KeySet.cardinal (adj g node) := KeySet.observe_card _

theorem mem_nodes (g : Graph) (node : Node) :
    KeySet.mem node (nodes g) = true ↔ ∃ value, SparseMap.find node g = some value :=
  SparseMap.mem_domain node g

theorem observe_nodes (g : Graph) : KeySet.observe (nodes g) = SparseMap.keys g :=
  SparseMap.observe_domain g

theorem cardinal_nodes (g : Graph) : KeySet.cardinal (nodes g) = SparseMap.cardinal g :=
  SparseMap.cardinal_domain g

theorem adj_of_find_some {g : Graph} {node : Node} {value : NodeSet}
    (found : SparseMap.find node g = some value) : adj g node = value := by
  rw [adj, found]
  rfl

theorem adj_of_find_none {g : Graph} {node : Node}
    (absent : SparseMap.find node g = none) : adj g node = .nil := by
  rw [adj, absent]
  rfl

theorem adj_ext (g : Graph) {left right : Node} (same : left = right) :
    adj g left = adj g right := congrArg (adj g) same

theorem exists_find_of_adjacent {g : Graph} {left right : Node}
    (edge : Adjacent g left right) : ∃ value, SparseMap.find left g = some value := by
  cases found : SparseMap.find left g with
  | none => simp [Adjacent, adj, found, KeySet.mem_nil] at edge
  | some value => exact ⟨value, rfl⟩

theorem left_mem_keys_of_adjacent {g : Graph} {left right : Node}
    (edge : Adjacent g left right) : left ∈ SparseMap.keys g :=
  (SparseMap.mem_keys left g).mpr (exists_find_of_adjacent edge)

theorem neighbor_mem_keys {g : Graph} (symmetric : Undirected g) {left right : Node}
    (edge : Adjacent g left right) : right ∈ SparseMap.keys g :=
  left_mem_keys_of_adjacent (symmetric left right edge)

theorem keys_congr {g h : Graph} (same : observe g = observe h) :
    SparseMap.keys g = SparseMap.keys h := by
  simpa only [observe_keys] using congrArg Finmap.keys same

theorem neighbors_congr {g h : Graph} (same : observe g = observe h) (node : Node) :
    neighbors g node = neighbors h node := by
  have lookup := congrArg (fun view => view.lookup node) same
  simp only [observe_lookup] at lookup
  cases hg : SparseMap.find node g <;> cases hh : SparseMap.find node h <;>
    simp_all [neighbors, adj, KeySet.observe_nil]

theorem observe_ext {g h : Graph} (domains : SparseMap.keys g = SparseMap.keys h)
    (adjacencies : ∀ node, neighbors g node = neighbors h node) : observe g = observe h := by
  apply Finmap.ext_lookup
  intro node
  have present : (∃ value, SparseMap.find node g = some value) ↔
      ∃ value, SparseMap.find node h = some value := by
    rw [← SparseMap.mem_keys, ← SparseMap.mem_keys, domains]
  have same := adjacencies node
  cases hg : SparseMap.find node g <;> cases hh : SparseMap.find node h <;>
    simp_all [observe_lookup, neighbors, adj, KeySet.observe_nil]

theorem observe_eq_iff (g h : Graph) :
    observe g = observe h ↔ SparseMap.keys g = SparseMap.keys h ∧
      ∀ node, neighbors g node = neighbors h node :=
  ⟨fun same => ⟨keys_congr same, neighbors_congr same⟩,
   fun same => observe_ext same.1 same.2⟩

/-- Source subset_nodes traverses the original bindings in map-fold order. -/
def subsetNodes (predicate : Node → NodeSet → Bool) (g : Graph) : NodeSet :=
  SparseMap.fold (fun node value acc => if predicate node value then KeySet.add node acc else acc)
    g .nil

theorem mem_subset_fold (predicate : Node → NodeSet → Bool)
    (entries : List (Node × NodeSet)) (seed : NodeSet) (query : Node) :
    KeySet.mem query (entries.foldl
      (fun acc entry => if predicate entry.1 entry.2 then KeySet.add entry.1 acc else acc) seed) =
      true ↔ KeySet.mem query seed = true ∨
        ∃ entry ∈ entries, query = entry.1 ∧ predicate entry.1 entry.2 = true := by
  induction entries generalizing seed with
  | nil => simp
  | cons entry entries ih =>
      rw [List.foldl_cons, ih]
      cases accepted : predicate entry.1 entry.2 <;>
        simp [accepted, KeySet.mem_add, or_assoc, or_left_comm]

theorem mem_subsetNodes (predicate : Node → NodeSet → Bool) (g : Graph) (query : Node) :
    KeySet.mem query (subsetNodes predicate g) = true ↔
      ∃ value, SparseMap.find query g = some value ∧ predicate query value = true := by
  rw [subsetNodes, SparseMap.fold_eq, mem_subset_fold]
  simp only [KeySet.mem_nil, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨⟨key, value⟩, present, same, accepted⟩
    dsimp at same
    subst key
    exact ⟨value, (SparseMap.mem_elements query value g).mp present, accepted⟩
  · rintro ⟨value, found, accepted⟩
    exact ⟨(query, value), (SparseMap.mem_elements query value g).mpr found, rfl, accepted⟩

theorem subsetNodes_subset_nodes (predicate : Node → NodeSet → Bool) (g : Graph)
    (query : Node) (present : KeySet.mem query (subsetNodes predicate g) = true) :
    KeySet.mem query (nodes g) = true := by
  obtain ⟨value, found, _⟩ := (mem_subsetNodes predicate g query).mp present
  exact (mem_nodes g query).mpr ⟨value, found⟩

theorem choose_subsetNodes (predicate : Node → NodeSet → Bool) (g : Graph) {node : Node}
    (chosen : KeySet.choose (subsetNodes predicate g) = some node) :
    ∃ value, SparseMap.find node g = some value ∧ predicate node value = true :=
  (mem_subsetNodes predicate g node).mp (KeySet.choose_mem _ chosen)

theorem subsetNodes_mem_of_observe_eq (predicate : Node → NodeSet → Bool)
    (compatible : ∀ node left right, KeySet.observe left = KeySet.observe right →
      predicate node left = predicate node right) {g h : Graph}
    (same : observe g = observe h) (query : Node)
    (present : KeySet.mem query (subsetNodes predicate g) = true) :
    KeySet.mem query (subsetNodes predicate h) = true := by
  obtain ⟨left, foundLeft, accepted⟩ := (mem_subsetNodes predicate g query).mp present
  have keyPresent : query ∈ SparseMap.keys h := by
    rw [← keys_congr same]
    exact (SparseMap.mem_keys query g).mpr ⟨left, foundLeft⟩
  obtain ⟨right, foundRight⟩ := (SparseMap.mem_keys query h).mp keyPresent
  have values : KeySet.observe left = KeySet.observe right := by
    simpa only [neighbors, adj_of_find_some foundLeft, adj_of_find_some foundRight] using
      neighbors_congr same query
  exact (mem_subsetNodes predicate h query).mpr
    ⟨right, foundRight, (compatible query left right values).symm.trans accepted⟩

theorem subsetNodes_observe_congr (predicate : Node → NodeSet → Bool)
    (compatible : ∀ node left right, KeySet.observe left = KeySet.observe right →
      predicate node left = predicate node right) {g h : Graph}
    (same : observe g = observe h) :
    KeySet.observe (subsetNodes predicate g) = KeySet.observe (subsetNodes predicate h) := by
  ext query
  simp only [KeySet.mem_observe]
  exact ⟨subsetNodes_mem_of_observe_eq predicate compatible same query,
    subsetNodes_mem_of_observe_eq predicate compatible same.symm query⟩

def lowDegree (bound : Nat) (_node : Node) (value : NodeSet) : Bool :=
  decide (KeySet.cardinal value < bound)

@[simp] theorem lowDegree_eq_true (bound : Nat) (node : Node) (value : NodeSet) :
    lowDegree bound node value = true ↔ KeySet.cardinal value < bound := by
  simp [lowDegree]

theorem lowDegree_congr (bound : Nat) (node : Node) (left right : NodeSet)
    (same : KeySet.observe left = KeySet.observe right) :
    lowDegree bound node left = lowDegree bound node right := by
  have cards : KeySet.cardinal left = KeySet.cardinal right := by
    simpa only [KeySet.observe_card] using congrArg Finset.card same
  simp only [lowDegree, cards]

/-- Erase the binding, then erase the vertex from every remaining payload. -/
def removeNode (node : Node) (g : Graph) : Graph :=
  SparseMap.map (KeySet.erase node) (SparseMap.erase node g)

@[simp] theorem find_removeNode (erased query : Node) (g : Graph) :
    SparseMap.find query (removeNode erased g) =
      if query = erased then none else (SparseMap.find query g).map (KeySet.erase erased) := by
  rw [removeNode, SparseMap.find_map, SparseMap.find_erase]
  by_cases same : query = erased <;> simp [same]

theorem adj_removeNode (erased query : Node) (g : Graph) :
    adj (removeNode erased g) query =
      if query = erased then .nil else KeySet.erase erased (adj g query) := by
  by_cases same : query = erased
  · simp [adj, find_removeNode, same]
  · cases found : SparseMap.find query g <;>
      simp [adj, find_removeNode, same, found, KeySet.erase]

@[simp] theorem adjacent_removeNode (erased : Node) (g : Graph) (left right : Node) :
    Adjacent (removeNode erased g) left right ↔
      left ≠ erased ∧ right ≠ erased ∧ Adjacent g left right := by
  by_cases hl : left = erased <;> by_cases hr : right = erased <;>
    simp [Adjacent, adj_removeNode, hl, hr, KeySet.mem_erase, KeySet.mem_nil]

theorem neighbors_removeNode (erased : Node) (g : Graph) (query : Node) :
    neighbors (removeNode erased g) query =
      if query = erased then ∅ else (neighbors g query).erase erased := by
  by_cases same : query = erased <;>
    simp [neighbors, adj_removeNode, same, KeySet.observe_nil, KeySet.observe_erase]

@[simp] theorem keys_removeNode (node : Node) (g : Graph) :
    SparseMap.keys (removeNode node g) = (SparseMap.keys g).erase node := by
  rw [removeNode, SparseMap.keys_map, SparseMap.keys_erase]

theorem cardinal_removeNode (node : Node) (g : Graph) :
    SparseMap.cardinal (removeNode node g) = SparseMap.cardinal (SparseMap.erase node g) :=
  SparseMap.cardinal_map _ _

theorem cardinal_removeNode_add (node : Node) (g : Graph) :
    SparseMap.cardinal (removeNode node g) +
      (if (SparseMap.find node g).isSome then 1 else 0) = SparseMap.cardinal g := by
  rw [cardinal_removeNode]
  exact SparseMap.cardinal_erase_add node g

theorem cardinal_removeNode_of_mem (node : Node) (g : Graph)
    (present : node ∈ SparseMap.keys g) :
    SparseMap.cardinal (removeNode node g) + 1 = SparseMap.cardinal g := by
  obtain ⟨value, found⟩ := (SparseMap.mem_keys node g).mp present
  rw [cardinal_removeNode]
  exact SparseMap.cardinal_erase_of_some node g value found

theorem cardinal_removeNode_lt (node : Node) (g : Graph)
    (present : node ∈ SparseMap.keys g) :
    SparseMap.cardinal (removeNode node g) < SparseMap.cardinal g := by
  rw [cardinal_removeNode]
  exact SparseMap.cardinal_erase_lt_of_mem node g present

theorem cardinal_removeNode_of_none (node : Node) (g : Graph)
    (absent : SparseMap.find node g = none) :
    SparseMap.cardinal (removeNode node g) = SparseMap.cardinal g := by
  rw [cardinal_removeNode]
  exact SparseMap.cardinal_erase_of_none node g absent

theorem undirected_removeNode {g : Graph} (symmetric : Undirected g) (node : Node) :
    Undirected (removeNode node g) := by
  intro left right edge
  obtain ⟨hl, hr, original⟩ := (adjacent_removeNode node g left right).mp edge
  exact (adjacent_removeNode node g right left).mpr ⟨hr, hl, symmetric left right original⟩

theorem noSelfLoop_removeNode {g : Graph} (loopless : NoSelfLoop g) (node : Node) :
    NoSelfLoop (removeNode node g) := by
  intro query edge
  exact loopless query ((adjacent_removeNode node g query query).mp edge).2.2

theorem observe_removeNode_congr {g h : Graph} (same : observe g = observe h) (node : Node) :
    observe (removeNode node g) = observe (removeNode node h) := by
  apply observe_ext
  · rw [keys_removeNode, keys_removeNode, keys_congr same]
  · intro query
    rw [neighbors_removeNode, neighbors_removeNode, neighbors_congr same]

end Graphs.Coloring
