import Applications.Languages.ParserWorkload
import Applications.Resources.Prepared
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod

/-! Selection uses exact bounded profiles for immutable parser instances.
Query arenas are released after synchronous consumption; setup arenas persist. -/
namespace LanguageWitnesses.ParserSelection
open ParserWorkload RetainedSnapshot Resources.Prepared

/-- A finite encoding of every word and view in the public admission envelope.
Preparation depth is separate, so admitted requests can still be rejected. -/
abbrev Request (views words : Nat) :=
  Fin (views + 1) × ((n : Fin (words + 1)) × (Fin n.val → Bool))

def Request.raw {v w} (q : Request v w) : RetainedSnapshot.Request :=
  (q.1.val, List.ofFn q.2.2)

def Request.ofRaw {v w} (q : RetainedSnapshot.Request)
    (hv : q.1 ≤ v) (hw : q.2.length ≤ w) : Request v w :=
  (⟨q.1, Nat.lt_succ_of_le hv⟩, ⟨⟨q.2.length, Nat.lt_succ_of_le hw⟩, q.2.get⟩)

@[simp] theorem Request.ofRaw_raw {v w} (q : RetainedSnapshot.Request)
    (hv : q.1 ≤ v) (hw : q.2.length ≤ w) :
    (Request.ofRaw q hv hw).raw = q := by
  simp [Request.ofRaw, Request.raw]

def kinds : List Kind := [.derivative, .nullable, .normalization, .map, .closure,
  .snapshot, .validation, .traversal, .allocation]
abbrev Tariff := Kind → Nat

def cost (tariff : Tariff) (events : Trace) : Nat :=
  (kinds.map fun k => tariff k * events.count k).sum

theorem cost_append (t : Tariff) (a b : Trace) :
    cost t (a ++ b) = cost t a + cost t b := by
  simp [cost, Trace.count, List.filter_append, List.map_append, List.sum_append,
    Nat.mul_add, List.sum_map_add]

/-- Source identity is retained independently of any normalized representation. -/
structure State (depth : Nat) where
  source : Spine
  prepared : Setup depth

def ops (depth views words : Nat) (t : Tariff) (c : Policy) :
    Ops Spine (Request views words) (Option (Decision Payload)) (State depth) where
  prepare p := (⟨p, setup c p depth⟩, cost t (setup c p depth).events)
  answer r q := let a := r.prepared.query q.raw; (a.1, cost t a.2)

def Valid (depth : Nat) (c : Policy) (p : Spine) (r : State depth) : Prop :=
  r.source = p ∧ r.prepared = setup c p depth

def spec (depth : Nat) (p : Spine) (q : Request views words) : Option (Decision Payload) :=
  if admissible depth q.raw then some (p.native.parse q.raw.2) else none

theorem laws (d v w : Nat) (t : Tariff) (c : Policy) :
    Laws (spec d) (ops d v w t c) (Valid d c) where
  prepare _ := ⟨rfl, rfl⟩
  answer p r h q := by
    change (r.prepared.query q.raw).1 = _
    rw [h.2, setup_query_result, session_exact]
    rfl

/-- Exhaustive maximum over the entire admitted domain, including rejections. -/
def worst {v w} (f : Request v w → Nat) : Nat := Finset.univ.sup f

theorem le_worst {v w} (f : Request v w → Nat) (q : Request v w) :
    f q ≤ worst f := Finset.le_sup (Finset.mem_univ q)

def retained (r : State d) : Nat :=
  r.source.slots + r.prepared.events.count .allocation

def storage (d v w : Nat) (c : Policy) : Storage Spine (State d) where
  retained := retained
  preparePeak p := retained ⟨p, setup c p d⟩
  queryPeak r := retained r + worst (v := v) (w := w)
    (fun q => (r.prepared.query q.raw).2.count .allocation)

def profile (d v w : Nat) (t : Tariff) (c : Policy) : Profile Spine where
  preparation p := cost t (setup c p d).events
  query p := worst (v := v) (w := w) fun q => cost t ((setup c p d).query q.raw).2
  maintenance _ := 0
  retained p := retained ⟨p, setup c p d⟩
  peak p := (storage d v w c).queryPeak ⟨p, setup c p d⟩

theorem bounds (d v w : Nat) (t : Tariff) (c : Policy) :
    Bounds (ops d v w t c) (Valid d c) (storage d v w c) (profile d v w t c) where
  preparation _ := Nat.le_refl _
  query p r h q := by
    change cost t (r.prepared.query q.raw).2 ≤ _
    rw [h.2]
    exact le_worst (fun q : Request v w => cost t ((setup c p d).query q.raw).2) q
  retained p r h := by
    rcases r with ⟨s,a⟩
    change s = p ∧ a = setup c p d at h
    rcases h with ⟨rfl,rfl⟩
    exact Nat.le_refl _
  preparePeak _ := Nat.le_add_right _ _
  queryPeak p r h := by
    rcases r with ⟨s,a⟩
    change s = p ∧ a = setup c p d at h
    rcases h with ⟨rfl,rfl⟩
    exact Nat.le_refl _

def catalog : List Policy := [.ordinary, .retained, .normalized, .combined]

/-- No future words are supplied to this count-bounded objective. -/
def upperObjective (d v w : Nat) (t : Tariff) (p : Spine) (count : Nat) (c : Policy) : Nat :=
  (profile d v w t c).preparation p + count * (profile d v w t c).query p

def choose (d v w : Nat) (t : Tariff) (req : Requirements) (p : Spine)
    (objective : Policy → Nat) : Option Policy :=
  select catalog (profile d v w t) req p objective

theorem chosen_correct {d v w t req p objective c}
    (h : choose d v w t req p objective = some c) (q : Request v w) :
    ((ops d v w t c).answer ((ops d v w t c).prepare p).1 q).1 = spec d p q :=
  selected_agreement (ops d v w t) (Valid d) (fun c _ => laws d v w t c) h q

theorem chosen_deadline {d v w t req p objective c}
    (h : choose d v w t req p objective = some c) (q : Request v w) :
    ((ops d v w t c).answer ((ops d v w t c).prepare p).1 q).2 ≤ req.deadline :=
  response_deadline (bounds d v w t c) (selected h).1.2 ((laws d v w t c).prepare p) q

/-- A raw request needs only the public envelope hypotheses. No assumption
that the parser will accept the requested view or word is used. -/
theorem raw_deadline {d v w t req p objective c}
    (h : choose d v w t req p objective = some c)
    (q : RetainedSnapshot.Request) (hv : q.1 ≤ v) (hw : q.2.length ≤ w) :
    cost t ((setup c p d).query q).2 ≤ req.deadline := by
  simpa only [ops, Request.ofRaw_raw] using
    chosen_deadline h (Request.ofRaw q hv hw)

/-- Recognition equivalence cannot justify reusing a different source setup. -/
theorem valid_source {d c p r} (h : Valid d c p r) : r.source = p := h.1

/-- Fixed P permits an exact tagged dependent answer without erasing its fiber. -/
def semanticAnswer {P : Language Bool} (c : Policy) (p : Parser P) (d : Nat)
    (q : RetainedSnapshot.Request) : (w : List Bool) × Option (Decision (P w)) :=
  ⟨q.2, session c p d q⟩

theorem semanticAnswer_exact {P : Language Bool} (c : Policy) (p : Parser P) (d q) :
    semanticAnswer c p d q =
      ⟨q.2, if admissible d q then some (p.parse q.2) else none⟩ := by
  simp [semanticAnswer, session_exact]

/-- Full feasibility and minimality are inherited from the shared selector. -/
theorem chosen_minimal {d v w t req p objective c}
    (h : choose d v w t req p objective = some c) :
    c ∈ catalog ∧ Feasible req (profile d v w t c) p ∧
      ∀ other ∈ catalog, Feasible req (profile d v w t other) p →
        objective c ≤ objective other :=
  ⟨(selected h).1.1, (selected h).1.2, fun _ hc hf => (selected h).2 ⟨hc,hf⟩⟩

theorem choose_none_iff (d v w t req p objective) :
    choose d v w t req p objective = none ↔
      ∀ c ∈ catalog, ¬ Feasible req (profile d v w t c) p := by
  simp [choose, select, Optimization.Thinning.argmin_eq_none_iff,
    List.filter_eq_nil_iff]

/-- Exact batch tariff; future words are explicitly present in offline input. -/
def batchCost (t : Tariff) (r : Run) : Nat :=
  cost t r.setupEvents + (r.queryEvents.map (cost t)).sum

def offlineObjective (d : Nat) (t : Tariff)
    (input : Spine × List RetainedSnapshot.Request) (c : Policy) : Nat :=
  batchCost t (execute c input.1 d input.2)

/-- Public offline selection admits the batch at preparation and enforces the
same request envelope as the uniform service guarantees. -/
def chooseOffline (d v w : Nat) (t : Tariff) (req : Requirements)
    (input : Spine × List (Request v w)) : Option Policy :=
  choose d v w t req input.1
    (offlineObjective d t (offlineInput input.1 (input.2.map Request.raw)))

def chooseFuture (d v w : Nat) (t : Tariff) (req : Requirements)
    (p : Spine) (count : Nat) : Option Policy :=
  choose d v w t req p (upperObjective d v w t p count)

theorem batchCost_unit (r : Run) : batchCost (fun _ => 1) r = r.work := by
  have sums (es : List Trace) :
      (es.map (cost (fun _ => 1))).sum =
        (kinds.map fun k => (es.map fun t => t.count k).sum).sum := by
    induction es with
    | nil => simp [cost, kinds]
    | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, ih, cost, one_mul]
      rw [List.sum_map_add]
  simp only [batchCost, sums, cost, one_mul, Run.work, Run.count]
  rw [List.sum_map_add]
  rfl

theorem queries_cost (d v w t c p) (qs : List (Request v w)) :
    (Resources.Prepared.queries (ops d v w t c) ((ops d v w t c).prepare p).1 qs).2 =
      (((execute c p d (qs.map Request.raw)).queryEvents).map (cost t)).sum := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simpa [Resources.Prepared.queries, Resources.bind, Resources.pure, ops,
      execute, List.map_map] using congrArg (fun n => cost t ((setup c p d).query q.raw).2 + n) ih

/-- The count bound covers all admitted batches, without supplying their words
at preparation. It is not an exact unknown-workload prediction. -/
theorem batch_upper (d v w t c p) (qs : List (Request v w)) (count : Nat)
    (hcount : qs.length ≤ count) :
    batchCost t (execute c p d (qs.map Request.raw)) ≤ upperObjective d v w t p count c := by
  have h := queries_bound (bounds d v w t c) p _ ((laws d v w t c).prepare p) qs
  rw [queries_cost] at h
  exact Nat.add_le_add_left (h.trans (Nat.mul_le_mul_right _ hcount)) _

/-- The profile's peak bounds every actual batch arena, including zero queries. -/
theorem batch_peak (d v w t c p) (qs : List (Request v w)) :
    (execute c p d (qs.map Request.raw)).peak ≤ (profile d v w t c).peak p := by
  have fold_bound : ∀ (xs : List Nat) (a b : Nat), a ≤ b →
      (∀ x ∈ xs, x ≤ b) → xs.foldl max a ≤ b := by
    intro xs
    induction xs with
    | nil => intro a b ha _; exact ha
    | cons x xs ih =>
      intro a b ha hx
      exact ih _ _ (max_le ha (hx x (by simp))) (fun y hy => hx y (by simp [hy]))
  apply Nat.add_le_add_left
  apply fold_bound _ _ _ (Nat.zero_le _)
  intro x hx
  simp only [execute, List.map_map, List.mem_map] at hx
  obtain ⟨q, _, rfl⟩ := hx
  exact le_worst (fun q : Request v w => ((setup c p d).query q.raw).2.count .allocation) q

end LanguageWitnesses.ParserSelection
