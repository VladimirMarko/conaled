import Applications.Search.Incremental.Correctness

/-! Ordered edge assignments retain labels and refresh only changed destinations.
Heuristic consistency is required of the final graph, not intermediate writes. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental
variable {n : Nat}

structure Assignment (n : Nat) where
  source : Fin n
  target : Fin n
  cost : Cost

abbrev Batch (n : Nat) := List (Assignment n)

def assign (w : Graph n) (e : Assignment n) : Graph n :=
  Function.update w e.source (Function.update (w e.source) e.target e.cost)

def applyBatch (w : Graph n) (es : Batch n) : Graph n := es.foldl assign w

def PositiveBatch (es : Batch n) : Prop := ∀ e ∈ es, 0 < e.cost

@[simp] theorem assign_apply (w : Graph n) (e : Assignment n) (u v : Fin n) :
    assign w e u v = if u = e.source ∧ v = e.target then e.cost else w u v := by
  by_cases hu : u = e.source <;> by_cases hv : v = e.target <;> simp [assign, hu, hv]

theorem assign_positive (w : Graph n) (hw : Positive w) (e : Assignment n) (he : 0 < e.cost) :
    Positive (assign w e) := by
  intro u v
  rw [assign_apply]
  split
  · exact he
  · exact hw u v

theorem applyBatch_positive (w : Graph n) (hw : Positive w) (es : Batch n)
    (he : PositiveBatch es) : Positive (applyBatch w es) := by
  induction es generalizing w with
  | nil => exact hw
  | cons e es ih =>
    exact ih (assign w e) (assign_positive w hw e (he e List.mem_cons_self))
      (fun a ha => he a (List.mem_cons_of_mem e ha))

theorem applyBatch_append (w : Graph n) (xs ys : Batch n) :
    applyBatch w (xs ++ ys) = applyBatch (applyBatch w xs) ys := List.foldl_append

theorem assign_last (w : Graph n) (u v : Fin n) (a b : Cost) :
    assign (assign w ⟨u,v,a⟩) ⟨u,v,b⟩ = assign w ⟨u,v,b⟩ := by
  funext x y
  simp only [assign_apply]
  split <;> rfl

theorem rhsValue_assign_other (w : Graph n) (start : Fin n) (g : Labels n)
    (e : Assignment n) (v : Fin n) (hv : v ≠ e.target) :
    rhsValue (assign w e) start g v = rhsValue w start g v := by
  apply rhsValue_congr_inputs
  intro u
  simp [hv]

def applyAssignment (start : Fin n) (p : Graph n × State n) (e : Assignment n) : Graph n × State n :=
  let w' := assign p.1 e
  (w', refresh w' start p.2 e.target)

def applyUpdates (start : Fin n) (w : Graph n) (s : State n) (es : Batch n) : Graph n × State n :=
  es.foldl (applyAssignment start) (w,s)

theorem applyAssignment_valid (w : Graph n) (start : Fin n) (s : State n)
    (hs : Valid w start s) (e : Assignment n) :
    Valid (assign w e) start (refresh (assign w e) start s e.target) := by
  apply (valid_iff_ready _ _ _).mpr
  refine ⟨?_, refresh_nodup _ _ _ _ hs.2.1, hs.2.2.2⟩
  intro v
  by_cases hv : v = e.target
  · subst v; exact refresh_ready _ _ _ _
  · apply refresh_ready_of_ne _ _ _ _ _ hv
    refine ⟨?_, hs.2.2.1 v⟩
    rw [rhsValue_assign_other w start s.g e v hv]
    exact congrFun hs.1 v

theorem applyUpdates_graph (start : Fin n) (w : Graph n) (s : State n) (es : Batch n) :
    (applyUpdates start w s es).1 = applyBatch w es := by
  induction es generalizing w s with
  | nil => rfl
  | cons e es ih => exact ih (assign w e) (refresh (assign w e) start s e.target)

theorem applyUpdates_g (start : Fin n) (w : Graph n) (s : State n) (es : Batch n) :
    (applyUpdates start w s es).2.g = s.g := by
  induction es generalizing w s with
  | nil => rfl
  | cons e es ih => exact ih (assign w e) (refresh (assign w e) start s e.target)

theorem applyUpdates_valid (start : Fin n) (w : Graph n) (s : State n)
    (hs : Valid w start s) (es : Batch n) :
    Valid (applyUpdates start w s es).1 start (applyUpdates start w s es).2 := by
  induction es generalizing w s with
  | nil => exact hs
  | cons e es ih => exact ih _ _ (applyAssignment_valid w start s hs e)

theorem applyUpdates_append (start : Fin n) (w : Graph n) (s : State n) (xs ys : Batch n) :
    applyUpdates start w s (xs ++ ys) =
      applyUpdates start (applyUpdates start w s xs).1 (applyUpdates start w s xs).2 ys := by
  simp only [applyUpdates, List.foldl_append]

/-- Initialize once; subsequent repairs retain the complete state. -/
def initializeState (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (hh : ConsistentHeuristic w goal h) : State n :=
  complete w hw start goal h hh.2.2 (initial start) (initial_valid w start)

def repair (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (s : State n) (hs : Valid w start s)
    (es : Batch n) (hp : PositiveBatch es) (hh : ConsistentHeuristic (applyBatch w es) goal h) : State n :=
  let p := applyUpdates start w s es
  complete p.1 (by rw [applyUpdates_graph]; exact applyBatch_positive w hw es hp)
    start goal h (by rw [applyUpdates_graph]; exact hh.2.2)
    p.2 (applyUpdates_valid start w s hs es)

theorem initializeState_correct (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (hh : ConsistentHeuristic w goal h) :
    Valid w start (initializeState w hw start goal h hh) ∧
      DistanceResult w start goal ((initializeState w hw start goal h hh).g goal) :=
  complete_correct w hw start goal h hh.2.2 _ _

theorem repair_correct (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (s : State n) (hs : Valid w start s)
    (es : Batch n) (hp : PositiveBatch es) (hh : ConsistentHeuristic (applyBatch w es) goal h) :
    Valid (applyBatch w es) start (repair w hw start goal h s hs es hp hh) ∧
      DistanceResult (applyBatch w es) start goal ((repair w hw start goal h s hs es hp hh).g goal) := by
  have hc := complete_correct (applyUpdates start w s es).1
    (by rw [applyUpdates_graph]; exact applyBatch_positive w hw es hp) start goal h
    (by rw [applyUpdates_graph]; exact hh.2.2) (applyUpdates start w s es).2
    (applyUpdates_valid start w s hs es)
  simpa only [repair, applyUpdates_graph] using hc

theorem zero_heuristic {w : Graph n} (hw : Positive w) (goal : Fin n) :
    ConsistentHeuristic w goal (fun _ => 0) := by
  refine ⟨fun _ => le_rfl, rfl, ?_⟩
  intro u v
  simpa using le_of_lt (hw u v)

/-- A retained graph with fixed endpoints and heuristic. Proof fields erase. -/
structure Session (n : Nat) (start goal : Fin n) (h : Fin n → ℚ) where
  graph : Graph n
  positive : Positive graph
  state : State n
  valid : Valid graph start state

def Session.begin (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (hh : ConsistentHeuristic w goal h) : Session n start goal h :=
  ⟨w, hw, initializeState w hw start goal h hh, (initializeState_correct w hw start goal h hh).1⟩

def Session.advance {start goal : Fin n} {h : Fin n → ℚ} (p : Session n start goal h)
    (es : Batch n) (hp : PositiveBatch es)
    (hh : ConsistentHeuristic (applyBatch p.graph es) goal h) : Session n start goal h :=
  ⟨applyBatch p.graph es, applyBatch_positive p.graph p.positive es hp,
    repair p.graph p.positive start goal h p.state p.valid es hp hh,
    (repair_correct p.graph p.positive start goal h p.state p.valid es hp hh).1⟩

def Session.observe {start goal : Fin n} {h : Fin n → ℚ} (p : Session n start goal h) : Cost := p.state.g goal

theorem Session.begin_correct (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (hh : ConsistentHeuristic w goal h) :
    DistanceResult w start goal (Session.begin w hw start goal h hh).observe :=
  (initializeState_correct w hw start goal h hh).2

theorem Session.advance_correct {start goal : Fin n} {h : Fin n → ℚ} (p : Session n start goal h)
    (es : Batch n) (hp : PositiveBatch es)
    (hh : ConsistentHeuristic (applyBatch p.graph es) goal h) :
    DistanceResult (applyBatch p.graph es) start goal (p.advance es hp hh).observe :=
  (repair_correct p.graph p.positive start goal h p.state p.valid es hp hh).2

end Search.Incremental
