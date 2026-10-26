import Applications.Connectivity.Realizations
import Applications.Sorting.Sort

set_option autoImplicit false
set_option warningAsError true

/-!
Chapter 9: the actual disjoint-set Kruskal executor.  The official extraction
uses first-name list union, a stable weight sort, a recursive skip of internal
edges, and n-1 successful applications.  Option totalizes exhausted edges and
failed lookups; it does not repair malformed states.  Selected edges are consed,
so their returned order reverses their order of acceptance.

The graph predicates below quantify over independent edge lists.  Parallel
edges, loops, signed weights and repeated input occurrences are not excluded.
No operation count, lazy-demand or machine-runtime claim is made here.
-/

namespace Kruskal

open Connectivity.ListPartition
  (findDS lookupDS unionDS startDS FirstAssoc FirstContaining IsPartitionOf
   SameBlock IsName Connected)

abbrev Vertex := Connectivity.ListPartition.Vertex
abbrev Name := Connectivity.ListPartition.Name
abbrev DS := Connectivity.ListPartition.DS
abbrev Weight := Int
abbrev Edge := Vertex × Vertex × Weight
abbrev Graph := List Vertex × List Edge
abbrev Tree := Graph
abbrev StateDS := DS × List Edge × List Edge

def nodes (g : Graph) : List Vertex := g.1
def edges (g : Graph) : List Edge := g.2
def source (e : Edge) : Vertex := e.1
def target (e : Edge) : Vertex := e.2.1
def weight (e : Edge) : Weight := e.2.2
def components (s : StateDS) : DS := s.1
def selected (s : StateDS) : List Edge := s.2.1
def remaining (s : StateDS) : List Edge := s.2.2
def costMCST (t : Tree) : Int := ((edges t).map weight).sum
def sortEdges (es : List Edge) : List Edge :=
  Applications.Sorting.sortOn weight es

def gstepK2 : StateDS → Option StateDS
  | (_, _, []) => none
  | (ds, fs, e :: es) =>
    match findDS ds (source e), findDS ds (target e) with
    | some a, some b =>
      if a ≠ b then (unionDS a b ds).map (fun out => (out, e :: fs, es))
      else gstepK2 (ds, fs, es)
    | _, _ => none
termination_by s => (remaining s).length
decreasing_by simp [remaining]

def applyK : Nat → StateDS → Option StateDS
  | 0, s => some s
  | k + 1, s => (applyK k s).bind gstepK2

def startK (g : Graph) : StateDS :=
  (startDS (Int.ofNat (nodes g).length), [], sortEdges (edges g))

def kruskalState (g : Graph) : Option StateDS :=
  if nodes g = [] then none else applyK ((nodes g).length - 1) (startK g)

def kruskal (g : Graph) : Option Tree :=
  (kruskalState g).map (fun s => (nodes g, selected s))

def StableWeightSort (input out : List Edge) : Prop :=
  out.Perm input ∧ out.Pairwise (fun e f => weight e ≤ weight f) ∧
  ∀ w : Int, out.filter (fun e => decide (weight e = w)) =
    input.filter (fun e => decide (weight e = w))

def EndpointsIn (vs : List Vertex) (es : List Edge) : Prop :=
  ∀ e ∈ es, source e ∈ vs ∧ target e ∈ vs

def Reach (vs : List Vertex) (es : List Edge) (u v : Vertex) : Prop :=
  Connected vs (es.map (fun e => (source e, target e))) u v

def EdgeForest (vs : List Vertex) (es : List Edge) : Prop :=
  vs.Nodup ∧ EndpointsIn vs es ∧ es.Nodup ∧
  ∀ e ∈ es, ¬ Reach vs (es.erase e) (source e) (target e)

def SpanningEdges (vs : List Vertex) (es : List Edge) : Prop :=
  vs ≠ [] ∧ EdgeForest vs es ∧ ∀ u ∈ vs, ∀ v ∈ vs, Reach vs es u v

def SpanningTree (g t : Graph) : Prop :=
  nodes t = nodes g ∧ edges t ⊆ edges g ∧ SpanningEdges (nodes g) (edges t)

def MinimumSpanningTree (g t : Graph) : Prop :=
  SpanningTree g t ∧ ∀ other : Graph,
    SpanningTree g other → costMCST t ≤ costMCST other

def NumberedGraph (g : Graph) : Prop :=
  nodes g ≠ [] ∧
  (nodes g).Perm (Connectivity.ListPartition.vertices (Int.ofNat (nodes g).length)) ∧
  EndpointsIn (nodes g) (edges g)

def ConnectedGraph (g : Graph) : Prop :=
  ∀ u ∈ nodes g, ∀ v ∈ nodes g, Reach (nodes g) (edges g) u v

inductive SourceStep : StateDS → StateDS → Prop
  | take {ds : DS} {fs es : List Edge} {e : Edge} {a b : Name}
      {xs ys : List Vertex} :
      FirstContaining ds (source e) a → FirstContaining ds (target e) b → a ≠ b →
      FirstAssoc ds a xs → FirstAssoc ds b ys →
      SourceStep (ds, fs, e :: es)
        ((a, xs ++ ys) :: ds.filter (fun block => !([a, b].contains block.1)),
          e :: fs, es)
  | skip {ds : DS} {fs es : List Edge} {e : Edge} {a : Name} {out : StateDS} :
      FirstContaining ds (source e) a → FirstContaining ds (target e) a →
      SourceStep (ds, fs, es) out → SourceStep (ds, fs, e :: es) out

inductive SourceRun : Nat → StateDS → StateDS → Prop
  | zero (s : StateDS) : SourceRun 0 s s
  | succ {k : Nat} {s middle out : StateDS} :
      SourceRun k s middle → SourceStep middle out → SourceRun (k + 1) s out

def SourceResult (g t : Graph) : Prop :=
  nodes g ≠ [] ∧ ∃ sorted s, StableWeightSort (edges g) sorted ∧
    SourceRun ((nodes g).length - 1)
      (startDS (Int.ofNat (nodes g).length), [], sorted) s ∧
    t = (nodes g, selected s)

inductive Walk (vs : List Vertex) (es : List Edge) :
    Vertex → List Edge → Vertex → Prop
  | nil {u : Vertex} : u ∈ vs → Walk vs es u [] u
  | cons {u w v : Vertex} {e : Edge} {path : List Edge} :
      e ∈ es → u ∈ vs → w ∈ vs →
      ((u = source e ∧ w = target e) ∨ (u = target e ∧ w = source e)) →
      Walk vs es w path v → Walk vs es u (e :: path) v

def StateRep (vs : List Vertex) (s : StateDS) : Prop :=
  IsPartitionOf vs (components s) ∧ EdgeForest vs (selected s) ∧
  ∀ u v, SameBlock (components s) u v ↔ Reach vs (selected s) u v

def KInvariant (g : Graph) (s : StateDS) : Prop :=
  StateRep (nodes g) s ∧ ∃ pre, sortEdges (edges g) = pre ++ remaining s ∧
    (selected s).reverse.Sublist pre ∧
    ∀ e ∈ pre, Reach (nodes g) (selected s) (source e) (target e)

def ExchangeInv (g : Graph) (fs : List Edge) : Prop :=
  ∀ t : Graph, SpanningTree g t → ∃ replacement : Graph,
    SpanningTree g replacement ∧ fs ⊆ edges replacement ∧
    costMCST replacement ≤ costMCST t

/-- The graph observation is exactly the accepted finite-carrier equivalence closure. -/
theorem reach_partition_iff (vs : List Vertex) (es : List Edge) (u v : Vertex) :
    Reach vs es u v ↔ Connectivity.Connected vs.toFinset
      (es.map (fun e => (source e, target e))) u v :=
  Connectivity.sourceConnected_iff vs _ u v

theorem reach_observe_iff (vs : List Vertex) (es : List Edge) (u v : Vertex) :
    Connectivity.observe vs.toFinset (es.map (fun e => (source e, target e))) u v = some true ↔
      Reach vs es u v :=
  (Connectivity.observe_true_iff ..).trans (reach_partition_iff ..).symm

end Kruskal
