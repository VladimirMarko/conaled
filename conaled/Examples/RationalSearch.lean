import Applications.Search.RationalCost
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Aesop
import Mathlib.Tactic.Convert

/-! Two finite rational graphs. The diamond has two paths of cost one; a
blocked direct edge must not become a zero-cost shortcut. The second graph
has a reachable vertex at cost 3/4 and an unreachable vertex behind infinity. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.RationalSearch
open Search.RationalCost

def scale6 : Scale := ⟨6, by decide +kernel⟩
def diamond : Graph (Fin 4)
  | 0 => [(3,⊤),(1,(1/2 : ℚ)),(2,(1/3 : ℚ))]
  | 1 => [(3,(1/2 : ℚ))]
  | 2 => [(3,(2/3 : ℚ))]
  | _ => []
def estimate : Fin 4 → ℚ
  | 0 => 1 | 1 => 1/2 | 2 => 2/3 | _ => 0

theorem diamond_values (u v : Fin 4) (d : ℚ) (he : Edge diamond u v d) :
    d = 1/2 ∨ d = 1/3 ∨ d = 2/3 := by
  fin_cases u <;> simp [Edge, diamond] at he <;> aesop

theorem diamond_finite : FiniteCosts scale6 diamond estimate where
  values := by
    refine ⟨[0,1,1/2,1/3,2/3], ?_, ?_, ?_⟩
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num [Scale.Fits, Scale.encode, scale6]
    · intro u v d he
      rcases diamond_values u v d he with rfl | rfl | rfl <;> simp
    · intro u; fin_cases u <;> simp [estimate]
  positive := by
    intro u v d he
    rcases diamond_values u v d he with rfl | rfl | rfl <;> norm_num

theorem diamond_compatible : Compatible scale6 diamond estimate := diamond_finite.compatible

theorem diamond_adjacency : adjacency scale6 diamond = fun (u : Fin 4) =>
    match u with | 0 => [(1,3),(2,2)] | 1 => [(3,3)] | 2 => [(3,4)] | _ => [] := by
  funext u; fin_cases u <;> decide +kernel

theorem diamond_monotonic : Monotonic diamond estimate := by
  intro u v d he
  fin_cases u <;> simp [Edge, diamond] at he
  · rcases he with ⟨rfl,hd⟩ | ⟨rfl,hd⟩ <;> subst d <;> norm_num [estimate]
  · rcases he with ⟨rfl,hd⟩; subst d; norm_num [estimate]
  · rcases he with ⟨rfl,hd⟩; subst d; norm_num [estimate]

def goal3 (v : Fin 4) : Bool := v == 3

theorem diamond_optimistic : Optimistic diamond estimate goal3 := by
  apply (optimistic_iff diamond_compatible goal3).mp
  apply Search.Heuristic.monotonic_optimistic ((monotonic_iff diamond_compatible).mpr diamond_monotonic)
  intro v hv
  have : v = 3 := by simpa [goal3] using hv
  subst v
  decide +kernel

abbrev queue (V : Type) [DecidableEq V] :=
  Search.PriorityInterface.leftist (π := Nat) (Search.Heuristic.Path.vertex (V := V))

def diamond_budget : Search.Heuristic.Completed (queue (Fin 4)) (adjacency scale6 diamond)
    (scale6.encode ∘ estimate) goal3 0 := ⟨8, by decide +kernel⟩

theorem diamond_distance : DistanceResult diamond goal3 0 (some 1) := by
  have h := distanceSquare_correct (queue (Fin 4)) diamond_compatible goal3 0
    diamond_optimistic diamond_budget
  have he : (distanceSquare (queue (Fin 4)) diamond_compatible goal3 0
      diamond_optimistic).impl diamond_budget = some 1 := by
    rw [distanceSquare_apply]
    change @Eq (Option ℚ) _ _
    decide +kernel
  rwa [he] at h

/-- Both equal-cost alternatives use the general walk correspondence. -/
theorem diamond_left : Walk diamond 0 3 1 := by
  have hw : Search.Heuristic.Walk (adjacency scale6 diamond) 0 3 6 := by
    rw [diamond_adjacency]
    exact .cons (v := 1) (d := 3) (by decide +kernel)
      (.cons (d := 3) (by decide +kernel) (.nil 3))
  convert walk_from_nat diamond_compatible hw using 1; decide +kernel

theorem diamond_right : Walk diamond 0 3 1 := by
  have hw : Search.Heuristic.Walk (adjacency scale6 diamond) 0 3 6 := by
    rw [diamond_adjacency]
    exact .cons (v := 2) (d := 2) (by decide +kernel)
      (.cons (d := 4) (by decide +kernel) (.nil 3))
  convert walk_from_nat diamond_compatible hw using 1; decide +kernel

theorem diamond_blocked : ∀ d, ¬ Edge diamond 0 3 d := by simp [Edge, diamond]

def scale4 : Scale := ⟨4, by decide +kernel⟩
def cycle : Graph (Fin 3)
  | 0 => [(1,(3/4 : ℚ)),(2,⊤)]
  | 1 => [(0,(1/4 : ℚ))]
  | _ => []

theorem cycle_values (u v : Fin 3) (d : ℚ) (he : Edge cycle u v d) :
    d = 3/4 ∨ d = 1/4 := by
  fin_cases u <;> simp [Edge, cycle] at he <;> aesop

theorem cycle_finite : FiniteCosts scale4 cycle (fun _ => 0) where
  values := by
    refine ⟨[0,3/4,1/4], ?_, ?_, ?_⟩
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> norm_num [Scale.Fits, Scale.encode, scale4]
    · intro u v d he
      rcases cycle_values u v d he with rfl | rfl <;> simp
    · simp
  positive := by
    intro u v d he
    rcases cycle_values u v d he with rfl | rfl <;> norm_num

theorem cycle_compatible : Compatible scale4 cycle (fun _ => 0) := cycle_finite.compatible

theorem cycle_zero_optimistic (goal : Fin 3 → Bool) :
    Optimistic cycle (fun _ => 0) goal :=
by
  apply (optimistic_iff cycle_compatible goal).mp
  simpa [Function.comp_def] using Search.Heuristic.zero_optimistic (adjacency scale4 cycle) goal

def goal1 (v : Fin 3) : Bool := v == 1
def goal2 (v : Fin 3) : Bool := v == 2

def cycle_budget (goal : Fin 3 → Bool) (hgoal : goal = goal1 ∨ goal = goal2) :
    Search.Heuristic.Completed (queue (Fin 3)) (adjacency scale4 cycle) (scale4.encode ∘ (fun _ => 0)) goal 0 :=
  ⟨8, by rcases hgoal with rfl | rfl <;> decide +kernel⟩

theorem cycle_distance : DistanceResult cycle goal1 0 (some (3/4)) := by
  have h := distanceSquare_correct (queue (Fin 3)) cycle_compatible goal1 0
    (cycle_zero_optimistic goal1) (cycle_budget goal1 (Or.inl rfl))
  have he : (distanceSquare (queue (Fin 3)) cycle_compatible goal1 0
      (cycle_zero_optimistic goal1)).impl (cycle_budget goal1 (Or.inl rfl)) = some (3/4) := by
    rw [distanceSquare_apply]
    change @Eq (Option ℚ) _ _
    decide +kernel
  rwa [he] at h

theorem cycle_unreachable : DistanceResult cycle goal2 0 none := by
  have h := distanceSquare_correct (queue (Fin 3)) cycle_compatible goal2 0
    (cycle_zero_optimistic goal2) (cycle_budget goal2 (Or.inr rfl))
  have he : (distanceSquare (queue (Fin 3)) cycle_compatible goal2 0
      (cycle_zero_optimistic goal2)).impl (cycle_budget goal2 (Or.inr rfl)) = none := by
    rw [distanceSquare_apply]
    change @Eq (Option ℚ) _ _
    decide +kernel
  rwa [he] at h

/-- The finite domain excludes vertex 2; a blocked destination needs no closure. -/
theorem cycle_terminates : Nonempty (Search.Heuristic.Completed (queue (Fin 3))
    (adjacency scale4 cycle) (scale4.encode ∘ (fun _ => 0)) goal2 0) := by
  apply completed_exists (queue (Fin 3)) scale4 cycle (fun _ => 0) goal2 [0,1] 0 (by simp)
  intro u hu v d he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl <;> simp [Edge, cycle] at he <;> aesop

/-- Signed heuristics are normalized before encoding, preserving the premises. -/
theorem signed_optimistic : Optimistic cycle (fun _ => (-1/3)) goal1 := by
  intro u t c hw _
  have hc := walk_nonnegative (fun u v d he => le_of_lt (cycle_finite.positive u v d he)) hw
  linarith

theorem signed_normalized_optimistic :
    Search.Heuristic.Optimistic (adjacency scale4 cycle) (scale4.encode ∘ normalize (fun _ => (-1/3))) goal1 := by
  have hn := normalize_optimistic
    (fun u v d he => le_of_lt (cycle_finite.positive u v d he)) signed_optimistic
  have he : normalize (fun _ : Fin 3 => (-1/3 : ℚ)) = (fun _ => 0) := by
    funext u; norm_num [Search.RationalCost.normalize]
  rw [he] at hn ⊢
  exact (optimistic_iff cycle_compatible goal1).mpr hn

/-- A new denominator is not automatically covered by a previously valid scale. -/
theorem fifth_not_supported : ¬ scale4.Fits (1/5) := by
  unfold Scale.Fits
  decide +kernel

theorem diamond_terminates : Nonempty (Search.Heuristic.Completed (queue (Fin 4))
    (adjacency scale6 diamond) (scale6.encode ∘ estimate) goal3 0) := by
  apply completed_exists (queue (Fin 4)) scale6 diamond estimate goal3
    (List.finRange 4) 0 (List.mem_finRange 0)
  intro u _ v _ _
  exact List.mem_finRange v

theorem diamond_priority_tie :
    3 + scale6.encode (estimate 1) = 2 + scale6.encode (estimate 2) := by
  apply (priority_eq_iff 1 2 3 2 (diamond_compatible.heuristic_fits 1)
    (diamond_compatible.heuristic_fits 2)).mpr
  norm_num [Scale.decode, scale6, estimate]

theorem empty_walk_scaling : ∃ n, Search.Heuristic.Walk (adjacency scale6 diamond) 0 0 n ∧
    (n : ℚ) = 0 * scale6.denominator :=
  (walk_scaled diamond_compatible 0 0 0).mp (.nil 0)

theorem signed_normalized_monotonic :
    Monotonic cycle (normalize (fun _ => (-1/3))) := by
  apply normalize_monotonic (fun u v d he => le_of_lt (cycle_finite.positive u v d he))
  intro u v d he
  have hd := cycle_finite.positive u v d he
  linarith

end Examples.RationalSearch
