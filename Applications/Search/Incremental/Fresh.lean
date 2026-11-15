import Applications.Search.Incremental.Bellman
import Applications.Search.PrioritySearchQueue
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! A fresh closed-list A* comparator. Each query constructs its own exact
scale and materializes the encoded graph and heuristic before searching. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental.Fresh
variable {n : Nat}

def values (w : Graph n) (h : Fin n → ℚ) : List ℚ :=
  (List.finRange n).flatMap (fun u => (List.finRange n).filterMap (fun v => w u v)) ++
    (List.finRange n).map h

def denominator (qs : List ℚ) : Nat := (qs.map Rat.den).prod

theorem denominator_pos (qs : List ℚ) : 0 < denominator qs := by
  induction qs with
  | nil => decide
  | cons q qs ih => exact Nat.mul_pos q.den_pos ih

def scale (qs : List ℚ) : RationalCost.Scale := ⟨denominator qs,denominator_pos qs⟩

theorem scale_fits (qs : List ℚ) (q : ℚ) (hq : q ∈ qs) (hn : 0 ≤ q) : (scale qs).Fits q := by
  apply RationalCost.Scale.fits_of_integral
  obtain ⟨k,hk⟩ := List.dvd_prod (List.mem_map.mpr ⟨q,hq,rfl⟩ : q.den ∈ qs.map Rat.den)
  refine ⟨q.num.natAbs*k,?_⟩
  have numerator : (q.num.natAbs : ℚ) = q.num := by
    simpa only [Int.cast_natCast] using congrArg (fun z : Int => (z : ℚ))
      (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hn))
  have den : q * (q.den : ℚ) = q.num := by
    exact ((div_eq_iff (by exact_mod_cast q.den_ne_zero)).mp q.num_div_den).symm
  change q * (denominator qs : ℚ) = _
  change denominator qs = q.den*k at hk
  rw [hk,Nat.cast_mul,← mul_assoc,den,Nat.cast_mul,numerator]

theorem edge_mem_values (w : Graph n) (h : Fin n → ℚ) (u v : Fin n) (d : ℚ)
    (he : w u v = (d : Cost)) : d ∈ values w h := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨u,by simp,?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨v,by simp,he⟩

theorem heuristic_mem_values (w : Graph n) (h : Fin n → ℚ) (u : Fin n) : h u ∈ values w h := by
  exact List.mem_append_right _ (List.mem_map.mpr ⟨u,by simp,rfl⟩)

theorem compatible {w : Graph n} (hw : Positive w) {goal : Fin n}
    {h : Fin n → ℚ} (hh : ConsistentHeuristic w goal h) :
    RationalCost.Compatible (scale (values w h)) (adjacency w) h := by
  constructor
  · intro u v d edge
    have he := (edge_iff w u v d).mp edge
    apply scale_fits _ _ (edge_mem_values w h u v d he)
    have pos := hw u v
    rw [he] at pos
    exact le_of_lt (WithTop.coe_lt_coe.mp pos)
  · intro u
    exact scale_fits _ _ (heuristic_mem_values w h u) (hh.1 u)

structure Prepared (n : Nat) where
  scale : RationalCost.Scale
  rows : Vector (List (Fin n × Nat)) n
  heuristic : Vector Nat n

def prepare (w : Graph n) (h : Fin n → ℚ) : Prepared n :=
  let S := scale (values w h)
  ⟨S,Vector.ofFn (RationalCost.adjacency S (adjacency w)),Vector.ofFn (S.encode ∘ h)⟩

def Prepared.graph (p : Prepared n) : Heuristic.Graph (Fin n) := fun u => p.rows[u.val]

def Prepared.estimate (p : Prepared n) : Fin n → Nat := fun u => p.heuristic[u.val]

@[simp] theorem prepare_graph (w : Graph n) (h : Fin n → ℚ) :
    (prepare w h).graph = RationalCost.adjacency (scale (values w h)) (adjacency w) := by
  funext u
  simp [prepare,Prepared.graph]

@[simp] theorem prepare_estimate (w : Graph n) (h : Fin n → ℚ) :
    (prepare w h).estimate = (scale (values w h)).encode ∘ h := by
  funext u
  simp [prepare,Prepared.estimate]

def frontier (n : Nat) : Heuristic.Frontier (Fin n) :=
  PrioritySearchQueue.keyed Heuristic.Path.vertex

def budget (n : Nat) : Nat := Heuristic.closedBudget (List.finRange n) n

def run (p : Prepared n) (start goal : Fin n) : Option (Option (Heuristic.Path (Fin n))) :=
  Heuristic.run (frontier n) .closed p.graph p.estimate (fun v => decide (v=goal))
    (budget n) [] (Heuristic.start (frontier n) p.estimate start)

theorem run_total (w : Graph n) (h : Fin n → ℚ) (start goal : Fin n) :
    ∃ out, run (prepare w h) start goal = some out := by
  apply Heuristic.mstar_terminates (frontier n) (prepare w h).graph (prepare w h).estimate
    (fun v => decide (v=goal)) (List.finRange n) n start (by simp)
  · intro u hu v d edge
    simp
  · intro u hu
    rw [prepare_graph]
    unfold RationalCost.adjacency
    calc
      _ ≤ ((adjacency w) u).length := List.length_filterMap_le _ _
      _ = n := by simp [adjacency]

def result (w : Graph n) (h : Fin n → ℚ) (start goal : Fin n) : Cost :=
  let p := prepare w h
  let completed := (run p start goal).get (by
    obtain ⟨out,eq⟩ := run_total w h start goal
    rw [eq]
    rfl)
  completed.map (fun path => p.scale.decode path.cost)

theorem rational_monotonic {w : Graph n} {goal : Fin n} {h : Fin n → ℚ}
    (hh : ConsistentHeuristic w goal h) : RationalCost.Monotonic (adjacency w) h := by
  intro u v d edge
  have bound := hh.2.2 u v
  rw [(edge_iff w u v d).mp edge,← WithTop.coe_add] at bound
  exact WithTop.coe_le_coe.mp bound

theorem result_correct {w : Graph n} (hw : Positive w) {goal : Fin n} {h : Fin n → ℚ}
    (hh : ConsistentHeuristic w goal h) (start : Fin n) :
    DistanceResult w start goal (result w h start goal) := by
  obtain ⟨out,eq⟩ := run_total w h start goal
  have exactScale := compatible hw hh
  have monotonic : Heuristic.Monotonic (prepare w h).graph (prepare w h).estimate := by
    rw [prepare_graph,prepare_estimate]
    exact (RationalCost.monotonic_iff exactScale).mpr (rational_monotonic hh)
  have zero : ∀ v, decide (v=goal) = true → (prepare w h).estimate v = 0 := by
    intro v hv
    have vg : v=goal := by simpa using hv
    subst v
    simp [prepare_estimate,hh.2.1]
  have correct := Heuristic.mstar_correct (frontier n) (prepare w h).graph (prepare w h).estimate
    (fun v => decide (v=goal)) start monotonic zero (budget n) eq
  have distance : Heuristic.DistanceResult (prepare w h).graph (fun v => decide (v=goal)) start
      (out.map Heuristic.Path.cost) :=
    (Heuristic.observeDistance _ _ _).preserves (s := ()) correct
  rw [prepare_graph] at distance
  have transported := (RationalCost.distance_iff exactScale (fun v => decide (v=goal)) start
    (out.map Heuristic.Path.cost)).mp distance
  simp only [result,eq,Option.get_some]
  simpa only [DistanceResult,prepare,Option.map_map,Function.comp_def] using transported

end Search.Incremental.Fresh
