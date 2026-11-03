import Applications.Kruskal.Basic
import Applications.Kruskal.AllMinima

set_option autoImplicit false
set_option warningAsError true

/-!
The literal nested-forest Kruskal programs, preserving component vertex order,
component edge order and unused-edge order. Undefined source cases are Option
failures. The corrected all-edge scan is separate from the printed MCSF wrapper.
-/
namespace ForestKruskalSource
open Kruskal (Vertex Edge Graph Tree nodes edges source target weight costMCST sortEdges)

namespace Occurrences
variable {α : Type*}
def picks : List α → List (α × List α)
  | [] => []
  | x :: xs => (x, xs) :: (picks xs).map (fun p => (p.1, x :: p.2))

theorem mem_picks_iff (xs : List α) (x : α) (ys : List α) :
    (x, ys) ∈ picks xs ↔ ∃ front back, xs = front ++ x :: back ∧ ys = front ++ back := by
  induction xs generalizing ys with
  | nil => simp [picks]
  | cons z zs ih =>
    constructor
    · intro h
      rcases List.mem_cons.mp h with h | h
      · cases h
        exact ⟨[], zs, rfl, rfl⟩
      · rcases List.mem_map.mp h with ⟨⟨y, ws⟩, hw, heq⟩
        cases heq
        rcases (ih ws).mp hw with ⟨front, back, hzs, hws⟩
        exact ⟨z :: front, back, by simp [hzs], by simp [hws]⟩
    · rintro ⟨front, back, hxs, hys⟩
      cases front with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hxs hys
        rcases hxs with ⟨rfl, rfl⟩
        subst ys
        exact List.mem_cons_self
      | cons a front =>
        simp only [List.cons_append, List.cons.injEq] at hxs
        rcases hxs with ⟨rfl, hzs⟩
        rw [hys]
        exact List.mem_cons_of_mem _ (List.mem_map.mpr
          ⟨(x, front ++ back), (ih _).mpr ⟨front, back, hzs, rfl⟩, rfl⟩)

theorem picks_fst (xs : List α) : (picks xs).map Prod.fst = xs := by
  induction xs <;> simp_all [picks, List.map_map, Function.comp_def]

end Occurrences

abbrev Forest := List Tree
abbrev State := Forest × List Edge

def find (ts : Forest) (v : Vertex) : Option Tree :=
  (ts.filter (fun t => (nodes t).contains v)).head?

def safeEdge (e : Edge) (ts : Forest) : Bool :=
  match find ts (source e), find ts (target e) with
  | some t, some u => decide (t ≠ u)
  | _, _ => false

def merge (e : Edge) (ts : Forest) (t u : Tree) : Forest :=
  (nodes t ++ nodes u, e :: edges t ++ edges u) ::
    ts.filter (fun v => decide (v ≠ t ∧ v ≠ u))

def add (e : Edge) (ts : Forest) : Option Forest := do
  let t ← find ts (source e)
  let u ← find ts (target e)
  pure (merge e ts t u)

def start (g : Graph) : State :=
  ((nodes g).map (fun v => ([v], [])), edges g)

def startSorted (g : Graph) : State :=
  ((nodes g).map (fun v => ([v], [])), sortEdges (edges g))

def done (s : State) : Bool := s.1.length == 1

def extract (s : State) : Option Tree :=
  match s.1 with
  | [t] => some t
  | _ => none

def steps (s : State) : List State :=
  (Occurrences.picks s.2).flatMap (fun p =>
    if safeEdge p.1 s.1 then (add p.1 s.1).toList.map (fun ts => (ts,p.2)) else [])

/-- The tails revision in Answer9.6, including its literal residual suffix. -/
def suffixPicks : List Edge → List (Edge × List Edge)
  | [] => []
  | e :: es => (e,es) :: suffixPicks es

def stepsDiscard (s : State) : List State :=
  (suffixPicks s.2).flatMap (fun p =>
    if safeEdge p.1 s.1 then (add p.1 s.1).toList.map (fun ts => (ts,p.2)) else [])

def gstep : State → Option State
  | (_,[]) => none
  | (ts,e::es) =>
      match find ts (source e), find ts (target e) with
      | some t, some u =>
          if t ≠ u then some (merge e ts t u,es) else gstep (ts,es)
      | _,_ => none
termination_by s => s.2.length

def apply : Nat → State → Option State
  | 0,s => some s
  | k+1,s => (apply k s).bind gstep

def untilRun : Nat → State → Option State
  | 0,s => if done s then some s else none
  | k+1,s => if done s then some s else (gstep s).bind (untilRun k)

def kruskal1 (g : Graph) : Option Tree :=
  (apply ((nodes g).length-1) (startSorted g)).bind extract

def kruskal0 (g : Graph) : Option Tree :=
  (untilRun ((nodes g).length-1) (startSorted g)).bind extract

/-- The literal Answer9.7 wrapper. Recursive gstep may exhaust internal edges
before returning, so testing null only outside gstep does not repair partiality. -/
def mcsfLiteralRun : Nat → State → Option Forest
  | 0,s => if s.2=[] then some s.1 else none
  | k+1,s => if s.2=[] then some s.1 else (gstep s).bind (mcsfLiteralRun k)

def mcsfLiteral (g : Graph) : Option Forest :=
  mcsfLiteralRun (edges g).length (startSorted g)

/-- Corrected one-edge scan: an internal edge is consumed and returns a state. -/
def scanStep : State → Option State
  | (ts,[]) => some (ts,[])
  | (ts,e::es) =>
      match find ts (source e), find ts (target e) with
      | some t,some u =>
          some (if t ≠ u then merge e ts t u else ts,es)
      | _,_ => none

def scan : Forest → List Edge → Option Forest
  | ts,[] => some ts
  | ts,e::es =>
      match find ts (source e),find ts (target e) with
      | some t,some u => scan (if t ≠ u then merge e ts t u else ts) es
      | _,_ => none

def mcsf (g : Graph) : Option Forest := scan (start g).1 (sortEdges (edges g))

def stateCost (s : State) : Int := (s.1.map costMCST).sum

def minima (ss : List State) : List State :=
  ss.filter (fun s => ss.all (fun t => decide (stateCost s ≤ stateCost t)))

/-- The reconstructed filter is exactly the source scored fold, including ties. -/
theorem minima_eq_source (ss : List State) :
    minima ss = AllMinima.minsWith stateCost ss :=
  (AllMinima.minsWith_eq_filter stateCost ss).symm

/-- All optimum occurrences in input order, including repeated states. -/
theorem minima_mem_iff (ss : List State) (s : State) :
    s ∈ minima ss ↔ s ∈ Optimization.minimizers {t | t ∈ ss} stateCost := by
  simp [minima, Optimization.minimizers, isMinOn_iff]

theorem minima_sublist (ss : List State) : (minima ss).Sublist ss :=
  List.filter_sublist


inductive SourceStep : State → State → Prop
  | take {ts : Forest} {e : Edge} {es : List Edge} {t u : Tree} :
      find ts (source e)=some t → find ts (target e)=some u → t≠u →
      SourceStep (ts,e::es) (merge e ts t u,es)
  | skip {ts : Forest} {e : Edge} {es : List Edge} {t : Tree} {out : State} :
      find ts (source e)=some t → find ts (target e)=some t →
      SourceStep (ts,es) out → SourceStep (ts,e::es) out

theorem gstep_nil (ts : Forest) : gstep (ts,[])=none := by rw [gstep]

theorem gstep_take (ts : Forest) (e : Edge) (es : List Edge) (t u : Tree)
    (ht : find ts (source e)=some t) (hu : find ts (target e)=some u) (hne : t≠u) :
    gstep (ts,e::es)=some (merge e ts t u,es) := by simp [gstep,ht,hu,hne]

theorem gstep_skip (ts : Forest) (e : Edge) (es : List Edge) (t : Tree)
    (ht : find ts (source e)=some t) (hu : find ts (target e)=some t) :
    gstep (ts,e::es)=gstep (ts,es) := by simp [gstep,ht,hu]

theorem sourceStep_value {s out : State} (h : SourceStep s out) : gstep s=some out := by
  induction h with
  | take ht hu hn => exact gstep_take _ _ _ _ _ ht hu hn
  | skip ht hu _ ih => rw [gstep_skip _ _ _ _ ht hu];exact ih

theorem gstep_source_iff (s out : State) : gstep s=some out ↔ SourceStep s out := by
  refine ⟨?_,sourceStep_value⟩
  rcases s with ⟨ts,es⟩
  induction es with
  | nil => simp [gstep]
  | cons e es ih =>
      intro h
      rw [gstep] at h
      cases ht : find ts (source e) with
      | none => simp [ht] at h
      | some t =>
          cases hu : find ts (target e) with
          | none => simp [ht,hu] at h
          | some u =>
              simp only [ht,hu] at h
              by_cases hn : t≠u
              · simp only [ite_eq_left hn,Option.some.injEq] at h
                subst out
                exact .take ht hu hn
              · have he : t=u := by simpa using hn
                subst u
                simp only [ne_eq,not_true_eq_false,ite_false] at h
                exact .skip ht hu (ih h)

theorem find_mem (ts : Forest) (v : Vertex) (t : Tree) (h : find ts v=some t) :
    t∈ts ∧ v∈nodes t := by
  have hm := List.mem_of_head? h
  simpa [find] using (List.mem_filter.mp hm)

theorem safeEdge_spec (e : Edge) (ts : Forest) : safeEdge e ts=true ↔
    ∃t u,find ts (source e)=some t ∧ find ts (target e)=some u ∧ t≠u := by
  cases ht : find ts (source e) <;> cases hu : find ts (target e) <;>
    simp [safeEdge,ht,hu]

theorem steps_spec (s out : State) : out∈steps s ↔
    ∃e rest ts, (e,rest)∈Occurrences.picks s.2 ∧ safeEdge e s.1=true ∧
      add e s.1=some ts ∧ out=(ts,rest) := by
  simp only [steps,List.mem_flatMap]
  constructor
  · rintro ⟨⟨e,rest⟩,hp,ho⟩
    by_cases hs : safeEdge e s.1=true
    · simp only [hs,ite_true,List.mem_map] at ho
      obtain ⟨ts,ht,rfl⟩ := ho
      exact ⟨e,rest,ts,hp,hs,by simpa using ht,rfl⟩
    · simp [hs] at ho
  · rintro ⟨e,rest,ts,hp,hs,ht,rfl⟩
    exact ⟨(e,rest),hp,by simp [hs,ht]⟩

theorem suffixPicks_spec (es : List Edge) (e : Edge) (rest : List Edge) :
    (e,rest)∈suffixPicks es ↔ ∃pre,es=pre++e::rest := by
  induction es with
  | nil => simp [suffixPicks]
  | cons f fs ih =>
      simp only [suffixPicks,List.mem_cons,Prod.mk.injEq,ih]
      constructor
      · rintro (⟨rfl,rfl⟩ | ⟨pre,rfl⟩)
        · exact ⟨[],rfl⟩
        · exact ⟨f::pre,rfl⟩
      · rintro ⟨pre,h⟩
        cases pre with
        | nil => exact Or.inl (by simpa using h.symm)
        | cons a pre =>
            simp only [List.cons_append,List.cons.injEq] at h
            exact Or.inr ⟨pre,h.2⟩

theorem suffixPicks_fst (es : List Edge) : (suffixPicks es).map Prod.fst=es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [suffixPicks,ih]

theorem stepsDiscard_same_forests (s : State) :
    (stepsDiscard s).map Prod.fst=(steps s).map Prod.fst := by
  have helper (ps : List (Edge×List Edge)) :
      (ps.flatMap (fun p => if safeEdge p.1 s.1 then
        (add p.1 s.1).toList.map (fun ts => (ts,p.2)) else [])).map Prod.fst =
      (ps.map Prod.fst).flatMap (fun e => if safeEdge e s.1 then (add e s.1).toList else []) := by
    induction ps with
    | nil => rfl
    | cons p ps ih =>
        simp only [List.flatMap_cons,List.map_append,List.map_cons,ih]
        by_cases h : safeEdge p.1 s.1
        · simp [h,List.map_map,Function.comp_def]
        · simp [h]
  rw [stepsDiscard,steps,helper,helper,suffixPicks_fst,Occurrences.picks_fst]

theorem stepsDiscard_residual_subset (s out : State) (ho : out∈stepsDiscard s) :
    ∃full,full∈steps s ∧ out.1=full.1 ∧ out.2.Sublist full.2 := by
  obtain ⟨⟨e,rest⟩,hp,hm⟩ := List.mem_flatMap.mp ho
  by_cases hs : safeEdge e s.1=true
  · simp only [hs,ite_true,List.mem_map] at hm
    obtain ⟨ts,ht,rfl⟩ := hm
    obtain ⟨pre,hpre⟩ := (suffixPicks_spec s.2 e rest).mp hp
    refine ⟨(ts,pre++rest),(steps_spec _ _).mpr ?_,rfl,?_⟩
    · exact ⟨e,pre++rest,ts,(Occurrences.mem_picks_iff _ _ _).mpr ⟨pre,rest,hpre,rfl⟩,
        hs,by simpa using ht,rfl⟩
    · exact List.sublist_append_right pre rest
  · simp [hs] at hm

/-- The exact source regression case in the official test driver. -/
def statePropertyGraph : Graph := ([1,2,3,4],
  [(1,2,2),(1,3,4),(1,4,2),(2,3,4),(2,4,3),(3,4,3)])

def statePropertyBefore : State :=
  ([([1,2,4],[(1,4,2),(1,2,2)]),([3],[])],
    [(2,4,3),(3,4,3),(1,3,4),(2,3,4)])

def statePropertyAfter : State :=
  ([([3,1,2,4],[(3,4,3),(1,4,2),(1,2,2)])],[(1,3,4),(2,3,4)])

theorem full_state_property_counterexample :
    apply 2 (startSorted statePropertyGraph)=some statePropertyBefore ∧
    gstep statePropertyBefore=some statePropertyAfter ∧
    statePropertyAfter∈minima [statePropertyAfter] ∧
    statePropertyAfter∉minima (steps statePropertyBefore) := by
  have hs : sortEdges (edges statePropertyGraph)=
      [(1,2,2),(1,4,2),(2,4,3),(3,4,3),(1,3,4),(2,3,4)] := by
    simp +decide [sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, edges, statePropertyGraph, List.mergeSort, weight]
  refine ⟨?_,?_,?_,?_⟩
  · simp only [apply,startSorted,hs]
    simp [statePropertyGraph,statePropertyBefore,gstep,find,merge,nodes,edges,source,target]
  · simp [statePropertyBefore,statePropertyAfter,gstep,find,merge,nodes,edges,source,target]
  · decide
  · have hn : statePropertyAfter∉steps statePropertyBefore := by decide
    exact fun h => hn ((minima_sublist (steps statePropertyBefore)).subset h)

def triangle : Graph := ([1,2,3],[(1,2,1),(2,3,2),(1,3,3)])

theorem literal_mcsf_boundary :
    mcsfLiteral triangle=none ∧
    mcsf triangle=some [([1,2,3],[(2,3,2),(1,2,1)])] := by
  have hs : sortEdges (edges triangle)=[(1,2,1),(2,3,2),(1,3,3)] := by
    simp +decide [sortEdges, Applications.Sorting.sortOn, Applications.Sorting.sortBy, edges, triangle, List.mergeSort, weight]
  simp only [mcsfLiteral,mcsf,startSorted,hs]
  simp [mcsfLiteralRun,triangle,start,scan,gstep,find,merge,nodes,edges,source,target]

theorem empty_boundaries : kruskal0 ([],[])=none ∧ kruskal1 ([],[])=none ∧
    mcsfLiteral ([],[])=some [] ∧ mcsf ([],[])=some [] := by
  simp [kruskal0,kruskal1,untilRun,apply,startSorted,extract,done,mcsfLiteral,
    mcsfLiteralRun,mcsf,start,scan,nodes,edges,sortEdges,Applications.Sorting.sortOn, Applications.Sorting.sortBy]

theorem singleton_boundaries (v : Vertex) :
    kruskal0 ([v],[])=some ([v],[]) ∧ kruskal1 ([v],[])=some ([v],[]) := by
  simp [kruskal0,kruskal1,untilRun,apply,startSorted,extract,done,nodes]

end ForestKruskalSource
