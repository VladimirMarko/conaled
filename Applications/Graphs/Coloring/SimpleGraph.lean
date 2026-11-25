import Applications.Graphs.Coloring.Support
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Finite supported colorings as SimpleGraph colorings

The graph observation retains its stored domain alongside the simple graph.
Only successful coloring keys become vertices of the colored restriction;
their actual lookup values give total colors in the finite palette subtype.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Graphs.Coloring

open Search.PositiveTrie

def simpleGraph (g : Graph) (symmetric : Undirected g) (loopless : NoSelfLoop g) :
    SimpleGraph Node where
  Adj := Adjacent g
  symm := ⟨symmetric⟩
  loopless := ⟨loopless⟩

/-- Explicit stored domain prevents loss of isolated vertices in the observation. -/
def simpleObservation (g : Graph) (symmetric : Undirected g) (loopless : NoSelfLoop g) :
    Finset Node × SimpleGraph Node := (SparseMap.keys g, simpleGraph g symmetric loopless)

theorem simpleObservation_eq_iff (g h : Graph)
    (symmetricG : Undirected g) (looplessG : NoSelfLoop g)
    (symmetricH : Undirected h) (looplessH : NoSelfLoop h) :
    simpleObservation g symmetricG looplessG = simpleObservation h symmetricH looplessH ↔
      observe g = observe h := by
  constructor
  · intro same
    apply observe_ext (congrArg Prod.fst same)
    intro node
    ext neighbor
    rw [mem_neighbors, mem_neighbors]
    have graphs := congrArg Prod.snd same
    exact Iff.of_eq (congrArg (fun graph => graph.Adj node neighbor) graphs)
  · intro same
    apply Prod.ext (keys_congr same)
    ext left right
    change Adjacent g left right ↔ Adjacent h left right
    rw [← mem_neighbors, ← mem_neighbors, neighbors_congr same]

def coloredGraph (g : Graph) (symmetric : Undirected g) (loopless : NoSelfLoop g)
    (f : Assignment) : SimpleGraph {node // node ∈ SparseMap.keys f} :=
  (simpleGraph g symmetric loopless).induce {node | node ∈ SparseMap.keys f}

theorem coloredGraph_adj (g : Graph) (symmetric : Undirected g) (loopless : NoSelfLoop g)
    (f : Assignment) (left right : {node // node ∈ SparseMap.keys f}) :
    (coloredGraph g symmetric loopless f).Adj left right ↔ Adjacent g left.val right.val :=
  Iff.rfl

theorem colored_vertex_count (f : Assignment) :
    Fintype.card {node // node ∈ SparseMap.keys f} = SparseMap.cardinal f := by
  rw [Fintype.card_coe, SparseMap.keys_card]

theorem palette_value_count (palette : NodeSet) :
    Fintype.card {value // value ∈ KeySet.observe palette} = KeySet.cardinal palette := by
  rw [Fintype.card_coe, KeySet.observe_card]

def paletteValue (palette : NodeSet) (f : Assignment) (paletteOnly : PaletteValued palette f)
    (node : {n // n ∈ SparseMap.keys f}) : {value // value ∈ KeySet.observe palette} :=
  ⟨valueAt f node, (KeySet.mem_observe _ _).mpr
    (paletteOnly node.val _ (find_valueAt f node))⟩

theorem paletteValue_lookup (palette : NodeSet) (f : Assignment)
    (paletteOnly : PaletteValued palette f) (node : {n // n ∈ SparseMap.keys f}) :
    SparseMap.find node.val f = some (paletteValue palette f paletteOnly node).val :=
  find_valueAt f node

def properColoring (palette : NodeSet) (g : Graph)
    (symmetric : Undirected g) (loopless : NoSelfLoop g) (f : Assignment)
    (compatible : EdgeColoringCompatible palette g f) (paletteOnly : PaletteValued palette f) :
    (coloredGraph g symmetric loopless f).Coloring {value // value ∈ KeySet.observe palette} := by
  apply SimpleGraph.Coloring.mk (paletteValue palette f paletteOnly)
  intro left right edge same
  exact (compatible left.val right.val edge).2 _ _
    (find_valueAt f left) (find_valueAt f right) (congrArg Subtype.val same)

theorem properColoring_lookup (palette : NodeSet) (g : Graph)
    (symmetric : Undirected g) (loopless : NoSelfLoop g) (f : Assignment)
    (compatible : EdgeColoringCompatible palette g f) (paletteOnly : PaletteValued palette f)
    (node : {n // n ∈ SparseMap.keys f}) :
    SparseMap.find node.val f =
      some ((properColoring palette g symmetric loopless f compatible paletteOnly) node).val :=
  find_valueAt f node

def producedColoring (palette : NodeSet) (g : Graph)
    (symmetric : Undirected g) (loopless : NoSelfLoop g) :
    (coloredGraph g symmetric loopless (color palette g)).Coloring
      {value // value ∈ KeySet.observe palette} :=
  properColoring palette g symmetric loopless (color palette g)
    (color_correct palette loopless symmetric) (paletteValued_color palette g)

theorem producedColoring_lookup (palette : NodeSet) (g : Graph)
    (symmetric : Undirected g) (loopless : NoSelfLoop g)
    (node : {n // n ∈ SparseMap.keys (color palette g)}) :
    SparseMap.find node.val (color palette g) =
      some ((producedColoring palette g symmetric loopless) node).val :=
  find_valueAt (color palette g) node

end Graphs.Coloring
