import Applications.Resources.FirstHitScan
import Applications.Incremental.Stateful

/-! Threshold repair retains ordered cumulative sums and extends them lazily.
The store and starting index/sum are fixed across updates. -/
namespace Resources.FirstHitScan.Retained
open MeasuredLoop

/-- Each retained cell is the next accumulated sum, including repeated sums. -/
def Valid (read : Nat → Nat) (i a : Nat) : List Nat → Prop
  | [] => True
  | b :: bs => b = a + read i ∧ Valid read (i+1) b bs

structure Result where
  out : Nat × Nat
  cache : List Nat
  steps : Nat
  reads : Nat
  cost : Nat
  deriving Repr, DecidableEq

/-- A guard costs seven as in the native scan. A continuing cached step costs
four: two cache inspection/dispatch units, index increment and cons allocation. A miss adds
one store read and one addition. The final guard is charged even at exhaustion. -/
def repair (read : Nat → Nat) : Nat → Nat → Nat → Nat → List Nat → Result
  | 0, i, a, _, cs => ⟨(i,a),cs,0,0,7⟩
  | fuel+1, i, a, t, cs =>
    if t ≤ a then ⟨(i,a),cs,0,0,7⟩ else
    match cs with
    | [] =>
      let b := a + read i
      let r := repair read fuel (i+1) b t []
      ⟨r.out,b::r.cache,r.steps+1,r.reads+1,r.cost+13⟩
    | b::bs =>
      let r := repair read fuel (i+1) b t bs
      ⟨r.out,b::r.cache,r.steps+1,r.reads,r.cost+11⟩

theorem repair_valid (read : Nat → Nat) (fuel i a t : Nat) (cs : List Nat)
    (h : Valid read i a cs) : Valid read i a (repair read fuel i a t cs).cache := by
  induction fuel generalizing i a cs with
  | zero => exact h
  | succ fuel ih =>
    simp only [repair]
    split
    · exact h
    · cases cs with
      | nil => exact ⟨rfl, ih _ _ [] trivial⟩
      | cons b bs => exact ⟨h.1, ih _ _ bs h.2⟩

theorem repair_steps (read : Nat → Nat) (fuel i a t : Nat) (cs : List Nat)
    (h : Valid read i a cs) :
    Steps (done (i+fuel)) (step read) (repair read fuel i a t cs).steps
      (i,(a,t)) ((repair read fuel i a t cs).out.1,((repair read fuel i a t cs).out.2,t)) := by
  induction fuel generalizing i a cs with
  | zero => exact .stop ((done_iff _ _).2 (Or.inl (by omega)))
  | succ fuel ih =>
    simp only [repair]
    split
    next ht => exact .stop ((done_iff _ _).2 (Or.inr ht))
    next ht =>
      have hp : done (i+(fuel+1)) (i,(a,t)) = false := by
        apply Bool.eq_false_iff.mpr
        intro hd
        have := (done_iff _ _).mp hd
        simp only at this
        omega
      cases cs with
      | nil =>
        apply Steps.step hp
        simpa [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (i+1) (a+read i) [] trivial
      | cons b bs =>
        apply Steps.step hp
        simpa [step, h.1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (i+1) b bs h.2

/-- Exact cache growth counts only newly read store cells. Earlier stops retain
all unvisited cached cells; updates never invalidate a fixed-store prefix. -/
theorem repair_accounting (read : Nat → Nat) (fuel i a t : Nat) (cs : List Nat) :
    let r := repair read fuel i a t cs
    r.cache.length = cs.length + r.reads ∧
    r.reads = r.steps - cs.length ∧
    r.steps ≤ fuel ∧
    r.cost = 11*r.steps + 2*r.reads + 7 := by
  induction fuel generalizing i a cs with
  | zero => simp [repair]
  | succ fuel ih =>
    simp only [repair]
    split
    · simp
    · cases cs with
      | nil =>
        have h := ih (i+1) (a+read i) []
        simp only [List.length_nil, List.length_cons, Nat.zero_add, Nat.sub_zero] at h ⊢
        omega
      | cons b bs =>
        have h := ih (i+1) b bs
        simp only [List.length_cons]
        omega

/-- The repaired execution is exactly a fresh native execution, including its
first-stop minimality; the two implementations have different charged costs. -/
theorem repair_correct (read : Nat → Nat) (fuel i a t : Nat) (cs : List Nat)
    (h : Valid read i a cs) :
    let r := repair read fuel i a t cs
    FirstHit read (i+fuel) (i,(a,t)) r.steps r.out ∧
    native (i+fuel) read (i,(a,t)) = (r.out,(r.steps+1)*7+r.steps*3) := by
  have hs := repair_steps read fuel i a t cs h
  exact ⟨(source_correct hs (by simp)).1, native_of_steps hs⟩

/-- Repeated threshold changes share the fixed store and start. -/
def updates (read : Nat → Nat) (fuel i a : Nat) : List Nat → List Nat → List Result
  | [], _ => []
  | t::ts, cs => let r := repair read fuel i a t cs
                r :: updates read fuel i a ts r.cache

theorem updates_correct (read : Nat → Nat) (fuel i a : Nat) (ts cs : List Nat)
    (h : Valid read i a cs) :
    ∀ r ∈ updates read fuel i a ts cs,
      Valid read i a r.cache ∧
      ∃ t ∈ ts, FirstHit read (i+fuel) (i,(a,t)) r.steps r.out ∧
        native (i+fuel) read (i,(a,t)) = (r.out,(r.steps+1)*7+r.steps*3) := by
  induction ts generalizing cs with
  | nil => simp [updates]
  | cons t ts ih =>
    intro r hr
    simp only [updates, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨repair_valid _ _ _ _ _ _ h, t, by simp, repair_correct _ _ _ _ _ _ h⟩
    · obtain ⟨hv,t',ht',hc⟩ := ih _ (repair_valid _ _ _ _ _ _ h) r hr
      exact ⟨hv,t',by simp [ht'],hc⟩

/-- Positional correctness: the result at each update belongs to that threshold,
not merely to some threshold appearing elsewhere in the sequence. -/
theorem updates_outputs (read : Nat → Nat) (fuel i a : Nat) (ts cs : List Nat)
    (h : Valid read i a cs) :
    (updates read fuel i a ts cs).map Result.out =
      ts.map (fun t => (native (i+fuel) read (i,(a,t))).1) := by
  induction ts generalizing cs with
  | nil => rfl
  | cons t ts ih =>
    simp only [updates, List.map_cons]
    rw [ih _ (repair_valid _ _ _ _ _ _ h), (repair_correct _ _ _ _ _ _ h).2]

/-- No existing cache cell is discarded or rewritten on a threshold change. -/
theorem repair_extends (read : Nat → Nat) (fuel i a t : Nat) (cs : List Nat) :
    ∃ tail, (repair read fuel i a t cs).cache = cs ++ tail := by
  induction fuel generalizing i a cs with
  | zero => exact ⟨[], by simp [repair]⟩
  | succ fuel ih =>
    simp only [repair]
    split
    · exact ⟨[], by simp⟩
    · cases cs with
      | nil => exact ⟨_, rfl⟩
      | cons b bs =>
        obtain ⟨tail, ht⟩ := ih (i+1) b bs
        exact ⟨tail, by simp [ht]⟩

def finalCache (read : Nat → Nat) (fuel i a : Nat) : List Nat → List Nat → List Nat
  | [], cs => cs
  | t::ts, cs => finalCache read fuel i a ts (repair read fuel i a t cs).cache

theorem updates_growth (read : Nat → Nat) (fuel i a : Nat) (ts cs : List Nat) :
    (finalCache read fuel i a ts cs).length =
      cs.length + ((updates read fuel i a ts cs).map Result.reads).sum := by
  induction ts generalizing cs with
  | nil => simp [finalCache, updates]
  | cons t ts ih =>
    simp only [finalCache, updates, List.map_cons, List.sum_cons]
    rw [ih, (repair_accounting read fuel i a t cs).1]
    omega

theorem finalCache_bound (read : Nat → Nat) (fuel i a : Nat) (ts cs : List Nat)
    (h : cs.length ≤ fuel) : (finalCache read fuel i a ts cs).length ≤ fuel := by
  induction ts generalizing cs with
  | nil => exact h
  | cons t ts ih =>
    apply ih
    have ha := repair_accounting read fuel i a t cs
    dsimp only at ha
    omega

/-- Across any finite update sequence, each store position is newly read at most
once. The cache begins empty; no eager prefixes are hidden in initialization. -/
theorem total_reads_bound (read : Nat → Nat) (fuel i a : Nat) (ts : List Nat) :
    ((updates read fuel i a ts []).map Result.reads).sum ≤ fuel := by
  have h := finalCache_bound read fuel i a ts [] (by simp)
  rw [updates_growth] at h
  simpa using h

theorem cached_no_reads (read : Nat → Nat) (fuel i a t : Nat) (cs : List Nat)
    (h : (repair read fuel i a t cs).steps ≤ cs.length) :
    (repair read fuel i a t cs).reads = 0 := by
  rw [(repair_accounting _ _ _ _ _ _).2.1, Nat.sub_eq_zero_of_le h]

/-- Initialization charges one control operation, with no source reads. -/
def initialCache : Measured (List Nat) Nat := ([],1)

/-- Retained cells plus nine fixed slots: fuel/start/initial sum, output index/sum,
cache root and three diagnostics. This excludes the resident store and transient
stack/history; transient cache copying is charged in cost. -/
def storage (cs : List Nat) : Nat := cs.length + 9

def measuredRepair (read : Nat → Nat) (fuel i a t : Nat) (cs : List Nat) :
    Measured (Nat × Nat × List Nat) Nat :=
  let r := repair read fuel i a t cs
  ((r.out.1,r.out.2,r.cache),r.cost)

/-- With unit tariffs, the retained route has an explicit overhead over #590;
fewer source reads alone do not imply a total-work speedup. -/
theorem cost_comparison (read : Nat → Nat) (fuel i a t : Nat) (cs : List Nat) :
    let r := repair read fuel i a t cs
    r.cost = ((r.steps+1)*7+r.steps*3) + r.steps + 2*r.reads ∧
    r.cost ≤ ((r.steps+1)*7+r.steps*3) + 3*r.steps := by
  have h := repair_accounting read fuel i a t cs
  dsimp only at h ⊢
  omega

/-- The same repaired result is recovered by the checked alternate store view. -/
theorem representation_recovery (n i a t : Nat) (hi : i ≤ n) (r q : Nat → Nat)
    (reads : ∀ j < n, q j = r j) (cs : List Nat) (hv : Valid r i a cs) :
    (compiled n q (i,(a,t))).1 = (repair r (n-i) i a t cs).out := by
  rw [representation_reuse n r q reads, routes_equal]
  have hc := (repair_correct r (n-i) i a t cs hv).2
  have hn : i+(n-i)=n := by omega
  rw [hn] at hc
  rw [hc]

/-- Concrete validity includes both a legal retained prefix and the current
observation. Threshold replacement does not change the store/start parameters. -/
def StateValid (read : Nat → Nat) (fuel i a t : Nat) (s : Result) : Prop :=
  Valid read i a s.cache ∧ s.cache.length ≤ fuel ∧
    s.out = (native (i+fuel) read (i,(a,t))).1

theorem repair_stateValid (read : Nat → Nat) (fuel i a t : Nat) (cs : List Nat)
    (hv : Valid read i a cs) (hb : cs.length ≤ fuel) :
    StateValid read fuel i a t (repair read fuel i a t cs) := by
  refine ⟨repair_valid _ _ _ _ _ _ hv, ?_, ?_⟩
  · have h := repair_accounting read fuel i a t cs
    dsimp only at h
    omega
  · rw [(repair_correct _ _ _ _ _ _ hv).2]

/-- Existing initialized-state composition can use this backend directly. -/
def stateful (read : Nat → Nat) (fuel i a : Nat) :
    Incremental.Stateful.Ops (Incremental.replacement Nat)
      (Incremental.replacement (Nat × Nat)) where
  State := Result
  init t := repair read fuel i a t []
  repair s t := let r := repair read fuel i a t s.cache; (r,r.out)
  observe := Result.out

theorem stateful_laws (read : Nat → Nat) (fuel i a : Nat) :
    Incremental.Stateful.Laws (fun t => (native (i+fuel) read (i,(a,t))).1)
      (stateful read fuel i a) (StateValid read fuel i a) where
  init t := repair_stateValid read fuel i a t [] trivial (by simp)
  repair _ _ t h := repair_stateValid read fuel i a t _ h.1 h.2.1
  observe _ _ h := h.2.2
  boundary _ _ _ _ := rfl

/-- The prior ordinary cache projection is recovered without recomputing in the
stateful repair operation. Its abstract replacement map is the baseline only. -/
theorem stateful_project_repair (read : Nat → Nat) (fuel i a t : Nat)
    (s : Result) (hs : StateValid read fuel i a t s) (t' : Nat) :
    (stateful read fuel i a).observe ((stateful read fuel i a).repair s t').1 =
      ((Incremental.Stateful.project
        (f := Incremental.recompute (fun t => (native (i+fuel) read (i,(a,t))).1))
        (stateful_laws read fuel i a) t s hs).advance t').output :=
  Incremental.Stateful.project_repair
    (f := Incremental.recompute (fun t => (native (i+fuel) read (i,(a,t))).1))
    (stateful_laws read fuel i a) t s hs t'

theorem initialization_bill (read : Nat → Nat) (fuel i a t : Nat) :
    initialCache.2 + (repair read fuel i a t initialCache.1).cost =
      13*(repair read fuel i a t []).steps + 8 := by
  have h := repair_accounting read fuel i a t []
  simp only [List.length_nil, Nat.sub_zero] at h
  change 1 + (repair read fuel i a t []).cost = _
  omega

theorem storage_bound (read : Nat → Nat) (fuel i a t : Nat) (s : Result)
    (hs : StateValid read fuel i a t s) : storage s.cache ≤ fuel + 9 := by
  exact Nat.add_le_add_right hs.2.1 9

end Resources.FirstHitScan.Retained
