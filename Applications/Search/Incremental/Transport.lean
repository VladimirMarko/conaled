import Applications.Search.Incremental.Interpretation
import Applications.Representations.ExecutableTransport

/-! Bijective changes of finite graph presentation retain every cached label and
queue entry. Native repairs remain correct after migration. Exact execution
commutation additionally requires preservation of successor enumeration. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental.Transport
variable {n : Nat}

abbrev Relabel (n : Nat) := Fin n ≃ Fin n

def graph (e : Relabel n) (w : Graph n) : Graph n := fun u v => w (e.symm u) (e.symm v)
def labels (e : Relabel n) (g : Labels n) : Labels n := fun v => g (e.symm v)
def heuristic (e : Relabel n) (h : Fin n → ℚ) : Fin n → ℚ := fun v => h (e.symm v)
def state (e : Relabel n) (s : State n) : State n :=
  ⟨labels e s.g, labels e s.rhs, s.queue.map e⟩
def assignment (e : Relabel n) (a : Assignment n) : Assignment n :=
  ⟨e a.source, e a.target, a.cost⟩
def batch (e : Relabel n) (es : Batch n) : Batch n := es.map (assignment e)

@[simp] theorem graph_apply (e : Relabel n) (w : Graph n) (u v : Fin n) :
    graph e w (e u) (e v) = w u v := by simp [graph]
@[simp] theorem labels_apply (e : Relabel n) (g : Labels n) (v : Fin n) :
    labels e g (e v) = g v := by simp [labels]
@[simp] theorem heuristic_apply (e : Relabel n) (h : Fin n → ℚ) (v : Fin n) :
    heuristic e h (e v) = h v := by simp [heuristic]
@[simp] theorem graph_inverse (e : Relabel n) (w : Graph n) : graph e.symm (graph e w) = w := by
  funext u v; simp [graph]
@[simp] theorem labels_inverse (e : Relabel n) (g : Labels n) : labels e.symm (labels e g) = g := by
  funext v; simp [labels]
@[simp] theorem state_inverse (e : Relabel n) (s : State n) : state e.symm (state e s) = s := by
  cases s; simp [state, List.map_map, Function.comp_def]
@[simp] theorem batch_inverse (e : Relabel n) (es : Batch n) : batch e.symm (batch e es) = es := by
  induction es with
  | nil => rfl
  | cons a es ih => cases a; simp_all [batch, assignment]

theorem positive (e : Relabel n) {w : Graph n} (hw : Positive w) : Positive (graph e w) :=
  fun u v => hw (e.symm u) (e.symm v)
theorem consistent (e : Relabel n) {w : Graph n} {goal : Fin n} {h : Fin n → ℚ}
    (hh : ConsistentHeuristic w goal h) :
    ConsistentHeuristic (graph e w) (e goal) (heuristic e h) := by
  refine ⟨fun v => hh.1 (e.symm v), ?_, fun u v => hh.2.2 (e.symm u) (e.symm v)⟩
  simpa using hh.2.1

theorem predecessorMinimum_map (e : Relabel n) (w : Graph n) (g : Labels n) (v : Fin n) :
    predecessorMinimum (graph e w) (labels e g) (e v) = predecessorMinimum w g v := by
  apply le_antisymm
  · apply (le_predecessorMinimum_iff _ _ _ _).mpr
    intro u
    simpa using predecessorMinimum_le (graph e w) (labels e g) (e u) (e v)
  · apply (le_predecessorMinimum_iff _ _ _ _).mpr
    intro u
    simpa [graph, labels] using predecessorMinimum_le w g (e.symm u) v

theorem rhs_map (e : Relabel n) (w : Graph n) (start : Fin n) (g : Labels n) :
    rhsValue (graph e w) (e start) (labels e g) = labels e (rhsValue w start g) := by
  funext v
  obtain ⟨v, rfl⟩ := e.surjective v
  simp [rhsValue, predecessorMinimum_map]

theorem valid (e : Relabel n) {w : Graph n} {start : Fin n} {s : State n}
    (hs : Valid w start s) : Valid (graph e w) (e start) (state e s) := by
  refine ⟨?_, ?_, ?_, fun v => hs.2.2.2 (e.symm v)⟩
  · change labels e s.rhs = rhsValue (graph e w) (e start) (labels e s.g)
    rw [rhs_map, hs.1]
  · exact hs.2.1.map e.injective
  · intro v
    obtain ⟨v, rfl⟩ := e.surjective v
    simpa [state] using hs.2.2.1 v

theorem assign_map (e : Relabel n) (w : Graph n) (a : Assignment n) :
    assign (graph e w) (assignment e a) = graph e (assign w a) := by
  funext u v
  obtain ⟨u, rfl⟩ := e.surjective u
  obtain ⟨v, rfl⟩ := e.surjective v
  simp [assign_apply, assignment]

theorem applyBatch_map (e : Relabel n) (w : Graph n) (es : Batch n) :
    applyBatch (graph e w) (batch e es) = graph e (applyBatch w es) := by
  induction es generalizing w with
  | nil => rfl
  | cons a es ih =>
    change applyBatch (assign (graph e w) (assignment e a)) (batch e es) = _
    rw [assign_map, ih]; rfl

theorem positiveBatch (e : Relabel n) {es : Batch n} (hp : PositiveBatch es) :
    PositiveBatch (batch e es) := by
  intro a ha
  change a ∈ es.map (assignment e) at ha
  rcases List.mem_map.mp ha with ⟨b, hb, hab⟩
  subst a
  exact hp b hb

/-- Transport includes proof fields, using all four native validity clauses. -/
def session (e : Relabel n) {start goal : Fin n} {h : Fin n → ℚ}
    (p : Session n start goal h) : Session n (e start) (e goal) (heuristic e h) :=
  ⟨graph e p.graph, positive e p.positive, state e p.state, valid e p.valid⟩

@[simp] theorem observe_session (e : Relabel n) {start goal : Fin n} {h : Fin n → ℚ}
    (p : Session n start goal h) : (session e p).observe = p.observe := by
  simp [session, Session.observe, state]

/-- Recovery retains the complete data of the proof-bearing package. Endpoint
and heuristic indices recover propositionally through the inverse bijection. -/
theorem session_recover (e : Relabel n) {start goal : Fin n} {h : Fin n → ℚ}
    (p : Session n start goal h) :
    (session e.symm (session e p)).graph = p.graph ∧
      (session e.symm (session e p)).state = p.state :=
  ⟨graph_inverse e p.graph, state_inverse e p.state⟩

/-- Execute the existing repair on the migrated state and ordered mapped batch. -/
def advance (e : Relabel n) {start goal : Fin n} {h : Fin n → ℚ}
    (p : Session n start goal h) (es : Batch n) (hp : PositiveBatch es)
    (hh : ConsistentHeuristic (applyBatch p.graph es) goal h) :
    Session n (e start) (e goal) (heuristic e h) :=
  (session e p).advance (batch e es) (positiveBatch e hp)
    (by simpa only [session, applyBatch_map] using consistent e hh)

theorem advance_correct (e : Relabel n) {start goal : Fin n} {h : Fin n → ℚ}
    (p : Session n start goal h) (es : Batch n) (hp : PositiveBatch es)
    (hh : ConsistentHeuristic (applyBatch p.graph es) goal h) :
    DistanceResult (graph e (applyBatch p.graph es)) (e start) (e goal)
      (advance e p es hp hh).observe := by
  simpa only [advance, session, applyBatch_map] using
    Session.advance_correct (session e p) (batch e es) (positiveBatch e hp)
      (by simpa only [session, applyBatch_map] using consistent e hh)

/-- An executable inverse on raw retained states, with one declared conversion
call as tariff. This does not count array copies or native search operations. -/
def stateEquiv (e : Relabel n) : State n ≃ State n where
  toFun := state e
  invFun := state e.symm
  left_inv := state_inverse e
  right_inv := state_inverse e.symm

def stateAdapter (e : Relabel n) :
    Representations.ExecutableTransport.Adapter (stateEquiv e) :=
  Representations.ExecutableTransport.primitive (stateEquiv e)

/-- Rational walks transport their endpoints and retain their cost. The native
observer promises existence of such a walk, not an executable path selector. -/
theorem walk_map (e : Relabel n) (w : Graph n) {u v : Fin n} {c : ℚ}
    (hw : RationalCost.Walk (adjacency w) u v c) :
    RationalCost.Walk (adjacency (graph e w)) (e u) (e v) c := by
  induction hw with
  | nil v => exact .nil (e v)
  | cons he _ ih => exact .cons (by simpa using he) ih

theorem walk_iff (e : Relabel n) (w : Graph n) (u v : Fin n) (c : ℚ) :
    RationalCost.Walk (adjacency (graph e w)) (e u) (e v) c ↔
      RationalCost.Walk (adjacency w) u v c := by
  constructor
  · intro hw
    simpa using walk_map e.symm (graph e w) hw
  · exact walk_map e w

theorem distance (e : Relabel n) (w : Graph n) (start goal : Fin n) (d : Cost) :
    DistanceResult (graph e w) (e start) (e goal) d ↔ DistanceResult w start goal d := by
  cases d with
  | none =>
    simp only [DistanceResult, RationalCost.DistanceResult, ne_eq, decide_eq_true_eq]
    constructor
    · intro hd t c ht he
      exact hd (e t) c (walk_map e w ht) (congrArg e he)
    · intro hd t c ht he
      obtain ⟨t, rfl⟩ := e.surjective t
      exact hd t c ((walk_iff e w start t c).mp ht) (e.injective he)
  | some d =>
    simp only [DistanceResult, RationalCost.DistanceResult, decide_eq_true_eq]
    constructor
    · rintro ⟨t, ht, he, hm⟩
      subst t
      refine ⟨goal, (walk_iff e w start goal d).mp ht, rfl, ?_⟩
      intro u c hu he
      exact hm (e u) c (walk_map e w hu) (congrArg e he)
    · rintro ⟨t, ht, he, hm⟩
      subst t
      refine ⟨e goal, walk_map e w ht, rfl, ?_⟩
      intro u c hu he
      obtain ⟨u, rfl⟩ := e.surjective u
      exact hm u c ((walk_iff e w start u c).mp hu) (e.injective he)

/-- Migration of the initialized package reuses native initialization. -/
theorem begin_correct (e : Relabel n) (w : Graph n) (hw : Positive w)
    (start goal : Fin n) (h : Fin n → ℚ) (hh : ConsistentHeuristic w goal h) :
    DistanceResult (graph e w) (e start) (e goal)
      (session e (Session.begin w hw start goal h hh)).observe := by
  rw [observe_session, distance]
  exact Session.begin_correct w hw start goal h hh

/-- Direct callers can use `advance_correct`; the square route reuses the
native repair/observation composition, with the same full input evidence. -/
def input (e : Relabel n) {start goal : Fin n} {h : Fin n → ℚ}
    (p : RepairInput n start goal h) : RepairInput n (e start) (e goal) (heuristic e h) :=
  ⟨graph e p.graph, positive e p.positive, state e p.retained, valid e p.valid,
    batch e p.changes, positiveBatch e p.changes_positive,
    by rw [applyBatch_map]; exact consistent e p.final_heuristic⟩

theorem square_correct (e : Relabel n) {start goal : Fin n} {h : Fin n → ℚ}
    (p : RepairInput n start goal h) :
    DistanceResult (graph e (applyBatch p.graph p.changes)) (e start) (e goal)
      ((repairDistanceSquare n (e start) (e goal) (heuristic e h)).impl (input e p)).2 := by
  simpa only [input, applyBatch_map] using
    repairDistanceSquare_correct (e start) (e goal) (heuristic e h) (input e p)

/-- Preserve the enumeration actually used by native expansion, not just its
set of vertices. This hypothesis can hold for nonidentity sparse graphs. -/
def Ordered (e : Relabel n) (w : Graph n) : Prop :=
  ∀ u, successors (graph e w) (e u) = (successors w u).map e

@[simp] theorem update_labels (e : Relabel n) (g : Labels n) (u : Fin n) (a : Cost) :
    Function.update (labels e g) (e u) a = labels e (Function.update g u a) := by
  funext v
  obtain ⟨v, rfl⟩ := e.surjective v
  by_cases hv : v = u <;> simp [labels, hv]

theorem filter_map (e : Relabel n) (vs : List (Fin n)) (u : Fin n) :
    (vs.map e).filter (· != e u) = (vs.filter (· != u)).map e := by
  induction vs with
  | nil => rfl
  | cons v vs ih => by_cases hv : v = u <;> simp_all

theorem refresh_map (e : Relabel n) (w : Graph n) (start : Fin n) (s : State n) (u : Fin n) :
    refresh (graph e w) (e start) (state e s) (e u) = state e (refresh w start s u) := by
  simp only [refresh, state, rhs_map, labels_apply, update_labels, filter_map]
  split <;> simp

theorem refreshMany_map (e : Relabel n) (w : Graph n) (start : Fin n)
    (s : State n) (vs : List (Fin n)) :
    refreshMany (graph e w) (e start) (state e s) (vs.map e) =
      state e (refreshMany w start s vs) := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih =>
    change refreshMany _ _ (refresh _ _ _ _) _ = _
    rw [refresh_map, ih]; rfl

theorem expand_map (e : Relabel n) (w : Graph n) (ho : Ordered e w)
    (start : Fin n) (s : State n) (u : Fin n) :
    expand (graph e w) (e start) (state e s) (e u) = state e (expand w start s u) := by
  unfold expand
  simp only [state, labels_apply, update_labels, filter_map, ho u]
  split
  · exact refreshMany_map e w start
      { s with g := Function.update s.g u (s.rhs u), queue := s.queue.filter (· != u) } _
  · exact refreshMany_map e w start
      { s with g := Function.update s.g u ⊤, queue := s.queue.filter (· != u) } (u :: successors w u)

@[simp] theorem labelKey_map (e : Relabel n) (h : Fin n → ℚ) (s : State n) (u : Fin n) :
    labelKey (heuristic e h) (state e s).g (state e s).rhs (e u) = labelKey h s.g s.rhs u := by
  simp [labelKey, state]

theorem argmin_map (e : Relabel n) (f g : Fin n → Key) (he : ∀ u, g (e u) = f u)
    (vs : List (Fin n)) :
    Optimization.Thinning.argmin g (vs.map e) = (Optimization.Thinning.argmin f vs).map e := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, Optimization.Thinning.argmin, ih]
    cases Optimization.Thinning.argmin f vs with
    | none => rfl
    | some u => simp only [Option.map_some, he]; split <;> rfl

theorem select_map (e : Relabel n) (h : Fin n → ℚ) (s : State n) :
    select (heuristic e h) (state e s) = (select h s).map e :=
  argmin_map e _ _ (labelKey_map e h s) s.queue

theorem active_map (e : Relabel n) (goal : Fin n) (h : Fin n → ℚ) (s : State n) :
    active (e goal) (heuristic e h) (state e s) ↔ active goal h s := by
  simp only [active, topKey, select_map, labelKey_map]
  cases select h s <;> simp [state, labelKey]

def outcome (e : Relabel n) : Outcome n → Outcome n
  | .stopped s => .stopped (state e s)
  | .exhausted s => .exhausted (state e s)

/-- Exact literal execution, including exhaustion and the complete terminal
state, when native successor enumeration commutes. Selection retains first ties. -/
theorem run_map (e : Relabel n) (w : Graph n) (ho : Ordered e w)
    (start goal : Fin n) (h : Fin n → ℚ) (fuel : Nat) (s : State n) :
    run (graph e w) (e start) (e goal) (heuristic e h) fuel (state e s) =
      outcome e (run w start goal h fuel s) := by
  induction fuel generalizing s with
  | zero =>
    simp only [run, runWith.eq_def, active_map]
    split <;> rfl
  | succ k ih =>
    unfold run
    rw [runWith.eq_def, runWith.eq_def]
    simp only [active_map, select_map]
    split
    · cases hs : select h s with
      | none => rfl
      | some u => simpa only [Option.map_some, expand_map e w ho, run] using ih (expand w start s u)
    · rfl

theorem initial_map (e : Relabel n) (start : Fin n) :
    initial (e start) = state e (initial start) := by
  have hr : (fun v : Fin n => if v = e start then (0 : Cost) else ⊤) =
      labels e (fun v => if v = start then 0 else ⊤) := by
    funext v
    obtain ⟨v, rfl⟩ := e.surjective v
    simp [labels]
  simp only [initial, state, List.map_cons, List.map_nil]
  rw [hr]
  rfl

theorem complete_map (e : Relabel n) (w : Graph n) (ho : Ordered e w)
    (hw : Positive w) (start goal : Fin n) (h : Fin n → ℚ)
    (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (s : State n) (hs : Valid w start s) :
    complete (graph e w) (positive e hw) (e start) (e goal) (heuristic e h)
      (fun u v => hh (e.symm u) (e.symm v)) (state e s) (valid e hs) =
      state e (complete w hw start goal h hh s hs) := by
  have ht := complete_run (graph e w) (positive e hw) (e start) (e goal) (heuristic e h)
    (fun u v => hh (e.symm u) (e.symm v)) (state e s) (valid e hs)
  rw [run_map e w ho, complete_run w hw start goal h hh s hs] at ht
  exact Outcome.stopped.inj ht.symm

theorem applyUpdates_map (e : Relabel n) (start : Fin n) (w : Graph n) (s : State n) (es : Batch n) :
    applyUpdates (e start) (graph e w) (state e s) (batch e es) =
      (graph e (applyUpdates start w s es).1, state e (applyUpdates start w s es).2) := by
  induction es generalizing w s with
  | nil => rfl
  | cons a es ih =>
    change applyUpdates (e start) (assign (graph e w) (assignment e a))
      (refresh (assign (graph e w) (assignment e a)) (e start) (state e s) (e a.target))
      (batch e es) = _
    rw [assign_map, refresh_map, ih]
    rfl

/-- Exact repair commutation requires ordered enumeration only for the final
batch graph. Intermediate ordered writes commute without that hypothesis. -/
theorem repair_map (e : Relabel n) (w : Graph n) (hw : Positive w)
    (start goal : Fin n) (h : Fin n → ℚ) (s : State n) (hs : Valid w start s)
    (es : Batch n) (hp : PositiveBatch es)
    (hh : ConsistentHeuristic (applyBatch w es) goal h)
    (ho : Ordered e (applyBatch w es)) :
    repair (graph e w) (positive e hw) (e start) (e goal) (heuristic e h)
      (state e s) (valid e hs) (batch e es) (positiveBatch e hp)
      (by rw [applyBatch_map]; exact consistent e hh) =
      state e (repair w hw start goal h s hs es hp hh) := by
  unfold repair
  simp only [applyUpdates_map]
  exact complete_map e _ (by simpa only [applyUpdates_graph] using ho) _ start goal h _ _ _

/-- The complete package after a repair commutes under the order hypothesis. -/
theorem advance_map (e : Relabel n) {start goal : Fin n} {h : Fin n → ℚ}
    (p : Session n start goal h) (es : Batch n) (hp : PositiveBatch es)
    (hh : ConsistentHeuristic (applyBatch p.graph es) goal h)
    (ho : Ordered e (applyBatch p.graph es)) :
    advance e p es hp hh = session e (p.advance es hp hh) := by
  unfold advance session Session.advance
  congr 1
  · exact applyBatch_map e p.graph es
  · exact repair_map e p.graph p.positive start goal h p.state p.valid es hp hh ho

/-- Without enumeration preservation, only the distance observations coincide;
the complete retained states remain available on both sides. -/
theorem advance_observe (e : Relabel n) {start goal : Fin n} {h : Fin n → ℚ}
    (p : Session n start goal h) (es : Batch n) (hp : PositiveBatch es)
    (hh : ConsistentHeuristic (applyBatch p.graph es) goal h) :
    (advance e p es hp hh).observe = (p.advance es hp hh).observe :=
  distance_unique ((distance e _ start goal _).mp (advance_correct e p es hp hh))
    (Session.advance_correct p es hp hh)

/-- A checked history retains every full native session, including the incoming
one. Its constructors carry the ordered batches and their dependent evidence. -/
inductive History {start goal : Fin n} {h : Fin n → ℚ} :
    Session n start goal h → List (Session n start goal h) → Prop where
  | nil (p) : History p [p]
  | cons (p) (es : Batch n) (hp : PositiveBatch es)
      (hh : ConsistentHeuristic (applyBatch p.graph es) goal h)
      {tail : List (Session n start goal h)} :
      History (p.advance es hp hh) tail → History p (p :: tail)

/-- Each subsequent observation is correct. Only the incoming observation
needs a premise; every step reuses `Session.advance_correct`. -/
theorem history_correct {start goal : Fin n} {h : Fin n → ℚ}
    {p : Session n start goal h} {states : List (Session n start goal h)}
    (hc : History p states) (hp : DistanceResult p.graph start goal p.observe) :
    ∀ q ∈ states, DistanceResult q.graph start goal q.observe := by
  induction hc with
  | nil p => simpa using hp
  | cons p es hep hh _ ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact ih (Session.advance_correct p es hep hh) q hq

/-- Exact repeated continuation needs enumeration preservation for each graph
in the history. This includes every final batch graph; no intermediate-write
order hypothesis is needed. -/
theorem history_map (e : Relabel n) {start goal : Fin n} {h : Fin n → ℚ}
    {p : Session n start goal h} {states : List (Session n start goal h)}
    (hc : History p states) (ho : ∀ q ∈ states, Ordered e q.graph) :
    History (session e p) (states.map (session e)) := by
  induction hc with
  | nil p => exact .nil _
  | @cons p es hp hh tail ht ih =>
    have hmem : p.advance es hp hh ∈ tail := by cases ht <;> simp
    have horder := ho _ (List.mem_cons_of_mem p hmem)
    have he := advance_map e p es hp hh horder
    have hi := ih (fun q hq => ho q (List.mem_cons_of_mem p hq))
    rw [← he] at hi
    exact .cons (session e p) (batch e es) (positiveBatch e hp)
      (by simpa only [session, applyBatch_map] using consistent e hh) hi

end Search.Incremental.Transport
