import SquareKit.Temporal.Finite
import Applications.FRP.Demand
import Applications.Progress.Processors

/-!
Finite temporal evidence for the reference one-shot demand machine (#206).
Indices are processing steps, while `t : T` is a fixed event timestamp. Search
reads a supplied trace; it does not run an environmental scheduler. One search
transition has unit cost, excluding computation of the reference trace.
-/
namespace FRPSpec.Frontier.Demand.Temporal
open FRPSpec.Frontier.Trace
open _root_.Temporal
variable {T α : Type} [LinearOrder T]
variable (s : Inputs T α) (ms : Streams T α) (a : Nat → Action T) (t : T)

abbrev Pending (n : Nat) := PLift (request s ms a n = .pending t)
abbrev Delivered (n : Nat) := (out : List α) × PLift (response s ms a n = some (t,out))
abbrev Correct (truth : Source → T → List α) (n : Nat) :=
  (out : List α) × PLift (response s ms a n = some (t,out) ∧
    out = truth .left t ++ truth .right t)
abbrev Arrival (n : Nat) := Until (Pending s ms a t) (Delivered s ms a t) n

structure Frame where
  stored : Request T
  observed : Option (List α)
  emitted : Option (T × List α)

def frame (n : Nat) : Frame (T := T) (α := α) :=
  ⟨request s ms a n, observe (run s ms (sourceSchedule a) n) t, response s ms a n⟩

theorem frame_comparison {n : Nat} {out : List α}
    (h : (frame s ms a t n).emitted = some (t,out)) :
    (frame s ms a t n).stored = .pending t ∧ (frame s ms a t n).observed = some out :=
  (emit_iff.mp h).2

/-- Honest traces justify the terminal value; they are not needed to schedule it. -/
def correct (truth : Source → T → List α) (honest : (traceRep ms).Rel s truth)
    {n : Nat} (w : Arrival s ms a t n) : Until (Pending s ms a t) (Correct s ms a t truth) n :=
  w.map (fun _ => id) (fun j ⟨out,h⟩ => ⟨out, ⟨h.down,
    (responseSquare ms a j t).preserves honest out
      ((responseFor_iff s ms a j t out).mpr h.down)⟩⟩)

theorem pending_next {n : Nat} (h : request s ms a n = .pending t)
    (silent : responseFor s ms a n t = none) : request s ms a (n+1) = .pending t := by
  rcases no_lost_work (run s ms (sourceSchedule a) n) (a n) t with hn | ⟨out,he⟩
  · simpa [request, h] using hn
  · have e : responseFor s ms a n t = some out :=
      (responseFor_iff s ms a n t out).mpr (by simpa [response, h] using he)
    simp [silent] at e

/-- Read one processing-indexed observation, retaining the absolute terminal index. -/
def machine : Progress.Machine Nat (Nat × List α) := fun n =>
  match responseFor s ms a n t with
  | some out => .inl (n,out)
  | none => .inr (n+1)

/-- A bounded witness constructor. Proof fields are erased; all branching uses
finite fuel and decidable trace observations, never choice from existence. -/
def searchArrival : (fuel n : Nat) → request s ms a n = .pending t → Option (Arrival s ms a t n)
  | 0, _, _ => none
  | fuel+1, n, h =>
    match he : responseFor s ms a n t with
    | some out => some (.now ⟨out, ⟨(responseFor_iff s ms a n t out).mp he⟩⟩)
    | none => (searchArrival fuel (n+1) (pending_next s ms a t h he)).map (.wait ⟨h⟩)

/-- Every certificate terminates at an actual response. -/
theorem arrival_response {n : Nat} (w : Arrival s ms a t n) :
    ∃ j out, n ≤ j ∧ response s ms a j = some (t,out) := by
  induction w with
  | now b => exact ⟨_, b.1, le_rfl, b.2.down⟩
  | wait _ _ ih => obtain ⟨j,out,h,e⟩ := ih; exact ⟨j,out,by omega,e⟩

def output {n : Nat} (w : Arrival s ms a t n) : List α :=
  w.fold (fun _ b => b.1) (fun _ _ out => out)

/-- The typed constructor follows precisely the shared fuel-search evaluator. -/
theorem searchArrival_search (fuel n : Nat) (h : request s ms a n = .pending t) :
    (searchArrival s ms a t fuel n h).map
      (fun w => (n + w.horizon, output s ms a t w, w.horizon+1)) =
    (Progress.search (machine s ms a t) fuel n).map (fun p => (p.1.1,p.1.2,p.2)) := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    simp only [searchArrival, Progress.search, machine]
    split
    next out he => simp [he, Until.horizon, output, Until.fold]
    next he =>
      simp only [he]
      specialize ih (n+1) (pending_next s ms a t h he)
      cases hw : searchArrival s ms a t fuel (n+1) (pending_next s ms a t h he) with
      | none =>
        simp only [hw, Option.map_none] at ih ⊢
        cases hs : Progress.search (machine s ms a t) fuel (n+1) <;> simp_all
      | some w =>
        simp only [hw, Option.map_some] at ih ⊢
        cases hs : Progress.search (machine s ms a t) fuel (n+1) with
        | none => simp_all
        | some p =>
          simp only [hs, Option.map_some, Option.some.injEq] at ih
          simp only [Option.map_some, Until.horizon, output, Until.fold]
          simp only [Option.some.injEq, Prod.mk.injEq] at ih ⊢
          exact ⟨by omega, ih.2.1, by omega⟩

/-- Exact success contract: the first response, its processing index and atomic cost. -/
theorem evaluation_spec {n cost : Nat} {result : Nat × List α}
    (h : Progress.Evaluates (machine s ms a t) n result cost) :
    n ≤ result.1 ∧ cost = result.1-n+1 ∧ responseFor s ms a result.1 t = some result.2 ∧
      ∀ q, n ≤ q → q < result.1 → responseFor s ms a q t = none := by
  induction h with
  | @done n result he =>
    simp only [machine] at he
    split at he
    next xs hx =>
      cases he
      exact ⟨le_rfl, by omega, hx, fun q hq hq' => by omega⟩
    next hx => cases he
  | @next n nextState result k he h ih =>
    simp only [machine] at he
    split at he
    next xs hx => cases he
    next hx =>
      cases he
      obtain ⟨hj,hk,hit,before⟩ := ih
      refine ⟨by omega, by omega, hit, ?_⟩
      intro q hq hq'
      by_cases eq : q = n
      · simpa [eq] using hx
      · exact before q (by omega) hq'

theorem search_spec {fuel n j cost : Nat} {out : List α}
    (h : Progress.search (machine s ms a t) fuel n = some ((j,out),cost)) :
    n ≤ j ∧ cost = j-n+1 ∧ responseFor s ms a j t = some out ∧
      ∀ q, n ≤ q → q < j → responseFor s ms a q t = none :=
  evaluation_spec s ms a t (Progress.search_sound h)

/-- A known finite response yields finite search, provided earlier steps are silent. -/
theorem search_complete_at {n k : Nat} {out : List α}
    (hit : responseFor s ms a (n+k) t = some out)
    (before : ∀ j, j < k → responseFor s ms a (n+j) t = none) :
    Progress.Evaluates (machine s ms a t) n (n+k,out) (k+1) := by
  induction k generalizing n with
  | zero =>
    simp only [Nat.add_zero] at hit
    exact .done (by simp [machine, hit])
  | succ k ih =>
    apply Progress.Evaluates.next (t := n+1)
    · have e := before 0 (by omega)
      simp only [Nat.add_zero] at e
      simp [machine, e]
    · have h := ih (n := n+1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hit)
        (fun j hj => by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using before (j+1) (by omega))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- An observed future response provides some finite successful typed search. -/
theorem response_has_fuel {n j : Nat} {out : List α}
    (registered : request s ms a n = .pending t) (hn : n ≤ j)
    (hj : response s ms a j = some (t,out)) :
    ∃ fuel result, searchArrival s ms a t fuel n registered = some result := by
  classical
  have ex : ∃ k, ∃ out, responseFor s ms a (n+k) t = some out := by
    refine ⟨j-n,out,?_⟩
    simpa [Nat.add_sub_of_le hn] using (responseFor_iff s ms a j t out).mpr hj
  obtain ⟨out,hit⟩ := Nat.find_spec ex
  have before : ∀ j, j < Nat.find ex → responseFor s ms a (n+j) t = none := by
    intro j hj
    cases he : responseFor s ms a (n+j) t with
    | none => rfl
    | some xs => exact (Nat.find_min ex hj ⟨xs,he⟩).elim
  have evaluation := search_complete_at s ms a t hit before
  have hs := Progress.search_complete evaluation (fuel := Nat.find ex+1) le_rfl
  have comparison := searchArrival_search s ms a t (Nat.find ex+1) n registered
  rw [hs] at comparison
  cases h : searchArrival s ms a t (Nat.find ex+1) n registered with
  | none => simp [h] at comparison
  | some result => exact ⟨_,result,h⟩

/-- Existence remains in Prop. It supplies no fixed latency or executable choice. -/
theorem eventual_arrival (d : Delivery (sourceSchedule a)) (fair : d.Fair)
    (processing : ProcessingFair s ms a) (n : Nat)
    (registered : request s ms a n = .pending t)
    (progress : ∀ source, ∃ k j, k ≤ d.available source j ∧
      t < (sourcePrefix (s source) (ms source) k).frontier) :
    Nonempty (Arrival s ms a t n) := by
  obtain ⟨j,out,hn,hj⟩ := eventual_response s ms a d fair processing t n registered progress
  obtain ⟨_,result,_⟩ := response_has_fuel s ms a t registered hn hj
  exact ⟨result⟩

/-- A typed arrival supplies finite successful search, but not a uniform bound. -/
theorem arrival_has_fuel {n : Nat} (w : Arrival s ms a t n)
    (registered : request s ms a n = .pending t) :
    ∃ fuel result, searchArrival s ms a t fuel n registered = some result := by
  obtain ⟨j,out,hn,hj⟩ := arrival_response s ms a t w
  exact response_has_fuel s ms a t registered hn hj

/-- Conditional semantic delivery combines progress with the honest observation square. -/
theorem eventual_correct (d : Delivery (sourceSchedule a)) (fair : d.Fair)
    (processing : ProcessingFair s ms a) (n : Nat)
    (registered : request s ms a n = .pending t)
    (progress : ∀ source, ∃ k j, k ≤ d.available source j ∧
      t < (sourcePrefix (s source) (ms source) k).frontier)
    (truth : Source → T → List α) (honest : (traceRep ms).Rel s truth) :
    Nonempty (Until (Pending s ms a t) (Correct s ms a t truth) n) := by
  obtain ⟨w⟩ := eventual_arrival s ms a t d fair processing n registered progress
  exact ⟨correct s ms a t truth honest w⟩

/-- No global fairness hypothesis can turn a permanently silent trace into data. -/
theorem no_arrival (silent : ∀ n, response s ms a n = none) (n : Nat) :
    ¬ Nonempty (Arrival s ms a t n) := by
  rintro ⟨w⟩
  obtain ⟨j,out,_,h⟩ := arrival_response s ms a t w
  simp [silent] at h

end FRPSpec.Frontier.Demand.Temporal
