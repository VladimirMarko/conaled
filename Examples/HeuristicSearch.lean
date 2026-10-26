import Applications.Search.Interpretation
import Applications.Search.HeuristicTermination
import Applications.Search.HeuristicSemantics
import Applications.Search.PrioritySearchQueue

/-!
# Exact source graph examples and heuristic boundaries

Fin-indexed vertices retain the displayed names 1=A,...,6=F. Additional unused
index 0 has no outgoing edges. The Figure16.1 answer is ACBD, correcting the
printed p409 prose ABCD; its displayed trace and official source already use
ACBD. Equal-priority queue traces depend on the concrete queue tie policy.
-/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.HeuristicSearch
open Search.Heuristic Search

abbrev TreeQueue (V : Type) := PriorityInterface.leftist (π := Nat) (Path.vertex (V := V))

def g4 : Graph (Fin 5)
  | 1 => [(2,5),(3,2)]
  | 2 => [(4,5)]
  | 3 => [(2,2)]
  | _ => []

def h4 : Heuristic (Fin 5)
  | 1 => 9 | 2 => 1 | 3 => 5 | _ => 0

def remaining4 : Heuristic (Fin 5)
  | 1 => 9 | 2 => 5 | 3 => 7 | _ => 0

def goal4 (v : Fin 5) : Bool := v == 4

def g4cycle (v : Fin 5) : List (Fin 5 × Nat) := if v = 2 then [(1,5)] else g4 v

def g6 : Graph (Fin 7)
  | 1 => [(2,3),(3,10),(4,20),(5,20)]
  | 2 => [(1,3),(3,5),(4,8),(5,20)]
  | 3 => [(1,10),(2,5),(4,2),(5,10)]
  | 4 => [(1,20),(2,8),(3,2),(5,6)]
  | 5 => [(1,20),(2,20),(3,10),(4,6),(6,1)]
  | _ => []

def h6 : Heuristic (Fin 7)
  | 1 => 10 | 2 => 10 | 3 => 5 | 4 => 5 | _ => 0

def goal6 (v : Fin 7) : Bool := v == 6

def monotonicCheck {V : Type} (g : Graph V) (h : Heuristic V) (domain : List V) : Bool :=
  domain.all (fun u => (g u).all (fun (v,d) => decide (h u ≤ d+h v)))

theorem monotonicCheck_sound {V : Type} (g : Graph V) (h : Heuristic V)
    (domain : List V) (complete : ∀ v,v ∈ domain) (hc : monotonicCheck g h domain = true) :
    Monotonic g h := by
  intro u v d he
  have hu := List.all_eq_true.mp hc u (complete u)
  have hh := List.all_eq_true.mp hu (v,d) he
  exact of_decide_eq_true hh

theorem remaining4_monotonic : Monotonic g4 remaining4 :=
  monotonicCheck_sound g4 remaining4 (List.finRange 5) List.mem_finRange (by decide +kernel)

theorem h4_optimistic : Optimistic g4 h4 goal4 := by
  have hz : ∀ v,goal4 v = true → remaining4 v = 0 := by decide +kernel
  have hbound : ∀ v,h4 v ≤ remaining4 v := by decide +kernel
  intro u t c hw ht
  exact Nat.le_trans (hbound u) (monotonic_optimistic remaining4_monotonic hz u t c hw ht)

theorem h4_not_monotonic : ¬Monotonic g4 h4 := by
  intro h
  have hh := h 3 2 2 (by decide)
  contradiction

theorem h6_monotonic : Monotonic g6 h6 :=
  monotonicCheck_sound g6 h6 (List.finRange 7) List.mem_finRange (by decide +kernel)

theorem h6_goal_zero : ∀ v,goal6 v = true → h6 v = 0 := by decide +kernel

theorem prop_graph_tstar :
    tstar g4 h4 goal4 1 8 = some (some ([1,3,2,4],9)) := by decide +kernel

theorem prop_graph_astar :
    astar g4 h4 goal4 1 8 = some (some ([1,3,2,4],9)) := by decide +kernel

theorem prop_graph_astar2 : astar g4cycle h4 goal4 1 10 = some none := by decide +kernel

theorem prop_graph_mstar :
    mstar g6 h6 goal6 1 12 = some (some ([1,2,3,4,5,6],17)) := by decide +kernel

theorem prop_graph_mstar2 :
    search (PrioritySearchQueue.keyed (Path.vertex (V := Fin 7))) .closed g6 h6 goal6 1 12 =
      some (some ([1,2,3,4,5,6],17)) := by decide +kernel

theorem mstar_nonmonotonic :
    mstar g4 h4 goal4 1 8 = some (some ([1,2,4],10)) := by decide +kernel

def optimum4 : Path (Fin 5) := ⟨4,[2,3,1],9⟩
def optimum6 : Path (Fin 7) := ⟨6,[5,4,3,2,1],17⟩

theorem optimum4_global : Minimum g4 goal4 1 optimum4 :=
  astar_correct (TreeQueue (Fin 5)) g4 h4 goal4 1 h4_optimistic 8 (out := some optimum4) (by decide +kernel)

theorem optimum6_global : Minimum g6 goal6 1 optimum6 :=
  mstar_correct (TreeQueue (Fin 7)) g6 h6 goal6 1 h6_monotonic h6_goal_zero 12 (out := some optimum6) (by decide +kernel)

theorem cyclic4_no_goal : NoGoal g4cycle goal4 1 :=
  astar_correct (TreeQueue (Fin 5)) g4cycle (fun _ => 0) goal4 1
    (zero_optimistic g4cycle goal4) 10 (out := none) (by decide +kernel)

/-- The illustrated queue order on p414 is allowed by abstract minimum priority;
the literal leftist implementation inserts a newly tied path before an old one. -/
theorem literal_leftist_tie :
    let Q := TreeQueue (Fin 5)
    let old : Path (Fin 5) := ⟨3,[1],10⟩
    let new : Path (Fin 5) := ⟨4,[3,2,1],10⟩
    (Q.remove (Q.add [(new,15)] (Q.add [(old,15)] Q.empty))).map (fun z => z.1.1) = some new := by
  decide +kernel

/-- The source's nonempty reverse-path extraction is chronological. -/
theorem printed_path_correction :
    extract optimum4 = ([1,3,2,4],9) ∧ extract optimum4 ≠ ([1,2,3,4],9) := by decide +kernel

/-- Exercise16.4: priority h alone chooses AC=5 before the better ABC=4. -/
def greedyGraph : Graph (Fin 3)
  | 0 => [(2,5),(1,2)] | 1 => [(2,2)] | _ => []
def greedyHeuristic : Heuristic (Fin 3)
  | 0 => 4 | 1 => 2 | _ => 0

def greedySuccs {V : Type} (g : Graph V) (h : Heuristic V) (p : Path V) : List (Path V × Nat) :=
  (g p.vertex).map (fun (v,d) => (extend p v d,h v))

def greedyRun {V : Type} (g : Graph V) (h : Heuristic V) (goal : V → Bool) :
    Nat → Search.LeftistQueue.PQ (Path V) Nat → Option (Option (Path V))
  | 0,_ => none
  | fuel+1,q => match Search.LeftistQueue.deleteQ q with
    | none => some none
    | some (e,r) => if goal e.1.vertex then some (some e.1)
      else greedyRun g h goal fuel (Search.LeftistQueue.addListQ (greedySuccs g h e.1) r)

theorem heuristic_only_failure :
    (greedyRun greedyGraph greedyHeuristic (fun v => v == 2) 3
      (start (TreeQueue (Fin 3)) greedyHeuristic 0)).map (Option.map extract) =
      some (some ([0,2],5)) ∧ Walk greedyGraph 0 2 4 := by
  refine ⟨by decide +kernel,?_⟩
  exact Walk.cons (v := 1) (d := 2) (by decide) (Walk.cons (v := 2) (d := 2) (by decide) (.nil 2))

theorem constant_positive_not_optimistic (c : Nat) (hc : 0 < c) :
    ¬Optimistic (fun _ : Unit => []) (fun _ => c) (fun _ => true) := by
  intro h
  have hh := h () () 0 (.nil ()) rfl
  change c ≤ 0 at hh
  omega

theorem zero_heuristic_priorities {V : Type} (g : Graph V) (p : Path V) :
    succs g (fun _ => 0) p = (g p.vertex).map (fun (v,d) => (extend p v d,p.cost+d)) := by
  simp [succs,estimate,extend]

/-- Natural goal costs have a least element whenever one is attainable. This
statement does not assume that an infinite nonintegral-cost graph has a minimum. -/
theorem nat_goal_minimum_exists {V : Type} (g : Graph V) (goal : V → Bool) (s : V)
    (reachable : ∃ t c,Walk g s t c ∧ goal t = true) :
    ∃ t c,Walk g s t c ∧ goal t = true ∧ ∀ u d,Walk g s u d → goal u = true → c ≤ d := by
  classical
  have least : ∀ n,(∃ t,Walk g s t n ∧ goal t = true) →
      ∃ t c,Walk g s t c ∧ goal t = true ∧ ∀ u d,Walk g s u d → goal u = true → c ≤ d := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases lower : ∃ d,n > d ∧ ∃ t,Walk g s t d ∧ goal t = true
      · obtain ⟨d,hd,ht⟩ := lower
        exact ih d hd ht
      · obtain ⟨t,ht,hg⟩ := hn
        refine ⟨t,n,ht,hg,?_⟩
        intro u d hd hgoal
        have hh : ¬d<n := by intro hlt; exact lower ⟨d,hlt,u,hd,hgoal⟩
        omega
  obtain ⟨t,c,hw,hg⟩ := reachable
  exact least c ⟨t,hw,hg⟩

theorem finite_completion4 : Nonempty (Completed (TreeQueue (Fin 5)) g4 h4 goal4 1) :=
  completed_exists _ _ _ _ (List.finRange 5) 1 (List.mem_finRange _)
    (fun _ _ v _ _ => List.mem_finRange v)

def completed4 : Completed (TreeQueue (Fin 5)) g4 h4 goal4 1 := ⟨8, by decide +kernel⟩

theorem interpreted_distance4 : DistanceResult g4 goal4 1 (some 9) := by
  have he : (distanceSquare (TreeQueue (Fin 5)) g4 h4 goal4 1 h4_optimistic).impl completed4 = some 9 := by
    change Option.map Path.cost ((run (TreeQueue (Fin 5)) .reopen g4 h4 goal4 8 []
      (start (TreeQueue (Fin 5)) h4 1)).get completed4.property) = some 9
    decide +kernel
  rw [← he]
  exact distanceSquare_correct _ _ _ _ _ _ _

def keyed6 := PrioritySearchQueue.keyed (π := Nat) (Path.vertex (V := Fin 7))
def completed6 : Completed keyed6 g6 h6 goal6 1 := ⟨20, by decide +kernel⟩

theorem interpreted_distance6 : DistanceResult g6 goal6 1 (some 17) := by
  have he : (distanceSquare keyed6 g6 h6 goal6 1
      (monotonic_optimistic h6_monotonic h6_goal_zero)).impl completed6 = some 17 := by
    change Option.map Path.cost ((run keyed6 .reopen g6 h6 goal6 20 []
      (start keyed6 h6 1)).get completed6.property) = some 17
    decide +kernel
  rw [← he]
  exact distanceSquare_correct _ _ _ _ _ _ _

/-- Exhausting a zero budget is distinct from completed cyclic no-goal. -/
theorem exhaustion_is_not_no_goal :
    astar g4cycle h4 goal4 1 0 = none ∧ astar g4cycle h4 goal4 1 10 = some none :=
  ⟨rfl, prop_graph_astar2⟩

end Examples.HeuristicSearch
