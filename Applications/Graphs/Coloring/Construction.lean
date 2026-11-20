import Applications.Graphs.Coloring.Graph

/-!
# Source graph construction

Both adjacency reads in `addEdge` use the original graph. The outer write is
at the first endpoint, including when the two endpoints coincide. Construction
is the source right fold; finite observations preserve stored endpoints.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Graphs.Coloring

open Search.PositiveTrie

def addEdge (edge : Node × Node) (g : Graph) : Graph :=
  SparseMap.add edge.1 (KeySet.add edge.2 (adj g edge.1))
    (SparseMap.add edge.2 (KeySet.add edge.1 (adj g edge.2)) g)

def mkGraph (edges : List (Node × Node)) : Graph := edges.foldr addEdge .nil

theorem adj_addEdge (edge : Node × Node) (g : Graph) (query : Node) :
    adj (addEdge edge g) query =
      if query = edge.1 then KeySet.add edge.2 (adj g edge.1)
      else if query = edge.2 then KeySet.add edge.1 (adj g edge.2)
      else adj g query := by
  simp only [adj, addEdge, SparseMap.find_add]
  split_ifs <;> rfl

theorem adjacent_addEdge (edge : Node × Node) (g : Graph) (left right : Node) :
    Adjacent (addEdge edge g) left right ↔ Adjacent g left right ∨
      (left = edge.1 ∧ right = edge.2) ∨ (left = edge.2 ∧ right = edge.1) := by
  by_cases first : left = edge.1 <;> by_cases second : left = edge.2 <;>
    simp_all [Adjacent, adj_addEdge, KeySet.mem_add, or_comm]

theorem keys_addEdge (edge : Node × Node) (g : Graph) :
    SparseMap.keys (addEdge edge g) =
      Insert.insert edge.1 (Insert.insert edge.2 (SparseMap.keys g)) := by
  rw [addEdge, SparseMap.keys_add, SparseMap.keys_add]

theorem undirected_addEdge {g : Graph} (symmetric : Undirected g) (edge : Node × Node) :
    Undirected (addEdge edge g) := by
  intro left right adjacent
  rcases (adjacent_addEdge edge g left right).mp adjacent with original | forward | backward
  · exact (adjacent_addEdge edge g right left).mpr (Or.inl (symmetric left right original))
  · exact (adjacent_addEdge edge g right left).mpr (Or.inr (Or.inr forward.symm))
  · exact (adjacent_addEdge edge g right left).mpr (Or.inr (Or.inl backward.symm))

theorem noSelfLoop_addEdge {g : Graph} (loopless : NoSelfLoop g) (edge : Node × Node)
    (distinct : edge.1 ≠ edge.2) : NoSelfLoop (addEdge edge g) := by
  intro node adjacent
  rcases (adjacent_addEdge edge g node node).mp adjacent with original | forward | backward
  · exact loopless node original
  · exact distinct (forward.1.symm.trans forward.2)
  · exact distinct (backward.2.symm.trans backward.1)

theorem adjacent_addEdge_self (g : Graph) (node : Node) :
    Adjacent (addEdge (node, node) g) node node :=
  (adjacent_addEdge (node, node) g node node).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem observe_addEdge_congr {g h : Graph} (same : observe g = observe h)
    (edge : Node × Node) : observe (addEdge edge g) = observe (addEdge edge h) := by
  apply observe_ext
  · rw [keys_addEdge, keys_addEdge, keys_congr same]
  · intro node
    ext query
    have original : Adjacent g node query ↔ Adjacent h node query := by
      rw [← mem_neighbors, ← mem_neighbors, neighbors_congr same]
    simp only [mem_neighbors, adjacent_addEdge, original]

theorem observe_addEdge_duplicate (edge : Node × Node) (g : Graph) :
    observe (addEdge edge (addEdge edge g)) = observe (addEdge edge g) := by
  apply observe_ext
  · simp only [keys_addEdge]
    ext query
    simp only [Finset.mem_insert]
    tauto
  · intro node
    ext query
    simp only [mem_neighbors, adjacent_addEdge]
    tauto

theorem observe_addEdge_reverse (left right : Node) (g : Graph) :
    observe (addEdge (left, right) g) = observe (addEdge (right, left) g) := by
  apply observe_ext
  · simp only [keys_addEdge, Finset.insert_comm]
  · intro node
    ext query
    simp only [mem_neighbors, adjacent_addEdge, or_comm]

@[simp] theorem mkGraph_nil : mkGraph [] = .nil := rfl

theorem mkGraph_cons (edge : Node × Node) (edges : List (Node × Node)) :
    mkGraph (edge :: edges) = addEdge edge (mkGraph edges) := rfl

theorem mem_keys_mkGraph (edges : List (Node × Node)) (node : Node) :
    node ∈ SparseMap.keys (mkGraph edges) ↔
      ∃ edge ∈ edges, node = edge.1 ∨ node = edge.2 := by
  induction edges with
  | nil => simp [SparseMap.mem_keys]
  | cons edge edges ih =>
      rw [mkGraph_cons, keys_addEdge]
      simp [ih, or_assoc]

theorem adjacent_mkGraph (edges : List (Node × Node)) (left right : Node) :
    Adjacent (mkGraph edges) left right ↔ (left, right) ∈ edges ∨ (right, left) ∈ edges := by
  induction edges with
  | nil => simp [Adjacent, adj, SparseMap.find_nil, KeySet.mem_nil]
  | cons edge edges ih =>
      rcases edge with ⟨first, second⟩
      rw [mkGraph_cons, adjacent_addEdge, ih]
      simp only [List.mem_cons, Prod.mk.injEq]
      tauto

theorem undirected_mkGraph (edges : List (Node × Node)) : Undirected (mkGraph edges) := by
  intro left right adjacent
  exact (adjacent_mkGraph edges right left).mpr ((adjacent_mkGraph edges left right).mp adjacent).symm

theorem noSelfLoop_mkGraph (edges : List (Node × Node))
    (distinct : ∀ edge ∈ edges, edge.1 ≠ edge.2) : NoSelfLoop (mkGraph edges) := by
  intro node adjacent
  have member := (adjacent_mkGraph edges node node).mp adjacent
  exact distinct (node, node) (member.elim id id) rfl

end Graphs.Coloring
