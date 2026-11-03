import Applications.FRP.Feedback
import SquareKit.InteractionContracts

/-! One-shot reactive contracts: independent registration, honest optional
emissions, and an initialized history consumer. Liveness assumptions stay external. -/
namespace FRPSpec.ReactiveContracts
open FRPSpec.Feedback
open FRPSpec.Frontier FRPSpec.Frontier.Trace FRPSpec.Frontier.Demand
open FRPSpec.Frontier.Demand.Temporal
variable {α T : Type} [LinearOrder T]

abbrev History (α : Type) := Nat × List α
abbrev Result (α : Type) := List (History α) × History α

def updated (s : History α) (batch : List α) : History α := (s.1+1,s.2++batch)

def history (s : History α) : Progress.Feedback.Initialized (List α) (History α) (History α) where
  initial := s
  step := fun (batch,state) => (updated state batch,updated state batch)

/-- Optional stuttering is permitted; a completed empty batch is a singleton. -/
def AllowedInput (batch : List α) : Set (List (Option (List α))) :=
  {xs | completed xs = [] ∨ completed xs = [batch]}

/-- Independent permitted results, including the initialized state. -/
def AllowedResult (s : History α) (batch : List α) : Set (Result α) :=
  {z | z = ([],s) ∨ z = ([updated s batch],updated s batch)}

theorem consume_zero (s : History α) (xs : List (Option (List α)))
    (h : completed xs = []) : consume (history s) s xs = ([],s) := by
  rw [agreement,h]; rfl

theorem consume_one (s : History α) (xs : List (Option (List α))) (batch : List α)
    (h : completed xs = [batch]) :
    consume (history s) s xs = ([updated s batch],updated s batch) := by
  rw [agreement,h]; rfl

theorem consume_allowed (s : History α) (xs : List (Option (List α))) (batch : List α)
    (h : AllowedInput batch xs) : AllowedResult s batch (consume (history s) s xs) := by
  rcases h with h | h
  · exact Or.inl (consume_zero s xs h)
  · exact Or.inr (consume_one s xs batch h)

/-- The consumer issues registration before any supplied source/process actions. -/
def register (t : T) (tail : Nat → Action T) : Nat → Action T
  | 0 => .register t
  | n+1 => tail n

theorem bootstrap (s : Inputs T α) (ms : Streams T α) (t : T) (tail : Nat → Action T) :
    request s ms (register t tail) 1 = .pending t := rfl

theorem registered (s : Inputs T α) (ms : Streams T α) (a : Nat → Action T) (t : T)
    (h : a 0 = .register t) : request s ms a 1 = .pending t := by
  simp [request,h,next]

/-- Later duplicate registration cannot change the selected timestamp. -/
theorem request_after_bootstrap (s : Inputs T α) (ms : Streams T α) (a : Nat → Action T)
    (t : T) (h : a 0 = .register t) (n : Nat) :
    request s ms a (n+1) = .pending t ∨ request s ms a (n+1) = .done := by
  induction n with
  | zero => exact Or.inl (registered s ms a t h)
  | succ n ih =>
    rcases ih with hp | hd
    · change next _ _ (request s ms a (n+1)) = _ ∨ next _ _ (request s ms a (n+1)) = _
      rw [hp]
      cases a (n+1) <;> simp [next]
      exact Classical.em _
    · apply Or.inr
      change next _ _ (request s ms a (n+1)) = _
      rw [hd,next_done]

theorem emitted_time (s : Inputs T α) (ms : Streams T α) (a : Nat → Action T)
    (t : T) (h : a 0 = .register t) (n : Nat) (u : T) (out : List α)
    (em : response s ms a n = some (u,out)) : u = t := by
  have hp := (emit_iff.mp em).2.1
  cases n with
  | zero => simp [request] at hp
  | succ n =>
    rcases request_after_bootstrap s ms a t h n with ht | hd
    · rw [ht] at hp; exact (Request.pending.inj hp).symm
    · rw [hd] at hp; cases hp

/-- Prefix characterization retains an emission witness to exclude repeated delivery. -/
theorem completion_prefix (f : Nat → Option (List α)) (batch : List α)
    (honest : ∀ i b, f i = some b → b = batch)
    (once : ∀ i j b, i < j → f i = some b → f j = none) (n : Nat) :
    completed ((List.range n).map f) = [] ∨
      ∃ i, i < n ∧ f i = some batch ∧ completed ((List.range n).map f) = [batch] := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [List.range_succ,List.map_append,completed_append]
    cases hn : f n with
    | none =>
      simp only [List.map_cons,List.map_nil,hn,completed,List.append_nil]
      rcases ih with h | ⟨i,hi,he,h⟩
      · exact Or.inl h
      · exact Or.inr ⟨i,Nat.lt_succ_of_lt hi,he,h⟩
    | some b =>
      have hb := honest n b hn
      subst b
      simp only [List.map_cons,List.map_nil,hn,completed]
      rcases ih with h | ⟨i,hi,he,_⟩
      · exact Or.inr ⟨n,Nat.lt_succ_self n,hn,by rw [h]; rfl⟩
      · have bad := once i n batch hi he
        rw [hn] at bad; cases bad

/-- Actual emissions, with honesty and one-shot protocol facts discharged. -/
theorem broker_allowed (s : Inputs T α) (ms : Streams T α) (a : Nat → Action T)
    (t : T) (reg : a 0 = .register t) (truth : Source → T → List α)
    (honest : (traceRep ms).Rel s truth) (n : Nat) :
    AllowedInput (truth .left t ++ truth .right t) (feedbackInputs s ms a t n) := by
  have h := completion_prefix (fun i => frameBatch (frame s ms a t i))
    (truth .left t ++ truth .right t) ?_ ?_ n
  · rcases h with h | ⟨_,_,_,h⟩
    · exact Or.inl h
    · exact Or.inr h
  · intro i b hb
    obtain ⟨⟨u,out⟩,he,hb⟩ := Option.map_eq_some_iff.mp hb
    change response s ms a i = some (u,out) at he
    have ht := emitted_time s ms a t reg i u out he
    subst u
    cases hb
    exact (responseSquare ms a i t).preserves honest out
      ((responseFor_iff s ms a i t out).mpr he)
  · intro i j b hij hb
    obtain ⟨⟨u,out⟩,he,_⟩ := Option.map_eq_some_iff.mp hb
    have hn := at_most_once s ms a hij he
    change (response s ms a j).map Prod.snd = none
    rw [hn]; rfl

/-- The executable broker graph does not contain the desired safety theorem. -/
def broker (ms : Streams T α) (a : Nat → Action T) (t : T) (n : Nat)
    (s : Inputs T α) (xs : List (Option (List α))) : Prop := feedbackInputs s ms a t n = xs

def consumer (s : History α) (xs : List (Option (List α))) (z : Result α) : Prop :=
  consume (history s) s xs = z

def admissible (ms : Streams T α) (truth : Source → T → List α) : Set (Inputs T α) :=
  {s | (traceRep ms).Rel s truth}

open SquareKit.RelationTransport

theorem broker_compatibility (ms : Streams T α) (a : Nat → Action T) (t : T)
    (reg : a 0 = .register t) (truth : Source → T → List α) (n : Nat) :
    image (broker ms a t n) (admissible ms truth) ⊆
      AllowedInput (truth .left t ++ truth .right t) := by
  rintro xs ⟨s,hs,rfl⟩
  exact broker_allowed s ms a t reg truth hs n

theorem consumer_compatibility (s : History α) (batch : List α) :
    image (consumer s) (AllowedInput batch) ⊆ AllowedResult s batch := by
  rintro z ⟨xs,h,rfl⟩
  exact consume_allowed s xs batch h

/-- Both internal interfaces are discharged independently: registration first,
then broker emissions meeting the consumer requirement. -/
theorem connected_requirement (ms : Streams T α) (a : Nat → Action T) (t : T)
    (reg : a 0 = .register t) (truth : Source → T → List α) (n : Nat) (s : History α) :
    admissible ms truth ⊆ requirement (Relation.Comp (broker ms a t n) (consumer s))
      (AllowedResult s (truth .left t ++ truth .right t)) := by
  rw [requirement_comp]
  have hb := (image_requirement (broker ms a t n) _ _).mp
    (broker_compatibility ms a t reg truth n)
  have hc := (image_requirement (consumer s) _ _).mp (consumer_compatibility s
    (truth .left t ++ truth .right t))
  intro x hx xs hxs
  exact hc (hb hx xs hxs)

theorem connected_image (ms : Streams T α) (a : Nat → Action T) (t : T)
    (reg : a 0 = .register t) (truth : Source → T → List α) (n : Nat) (s : History α) :
    image (Relation.Comp (broker ms a t n) (consumer s)) (admissible ms truth) ⊆
      AllowedResult s (truth .left t ++ truth .right t) := by
  rw [image_comp]
  exact ((image_requirement (consumer s)).monotone_l (broker_compatibility ms a t reg truth n)).trans
    (consumer_compatibility s _)

/-- The selected registering consumer discharges the broker requirement without
assuming delivery; the connected safety requirement then follows. -/
theorem handshake (ms : Streams T α) (tail : Nat → Action T) (t : T)
    (truth : Source → T → List α) (n : Nat) (s : History α) :
    (∀ initial, request initial ms (register t tail) 1 = .pending t) ∧
    admissible ms truth ⊆ requirement
      (Relation.Comp (broker ms (register t tail) t n) (consumer s))
      (AllowedResult s (truth .left t ++ truth .right t)) :=
  ⟨fun initial => bootstrap initial ms t tail,
    connected_requirement ms (register t tail) t rfl truth n s⟩

/-- Every actual result has an allowed specification result (the API's order). -/
theorem connected_refines (ms : Streams T α) (a : Nat → Action T) (t : T)
    (reg : a 0 = .register t) (truth : Source → T → List α) (n : Nat) (s : History α) :
    Interaction.Refines Eq (AllowedResult s (truth .left t ++ truth .right t))
      (image (Relation.Comp (broker ms a t n) (consumer s)) (admissible ms truth)) := by
  intro z hz
  exact ⟨z,connected_image ms a t reg truth n s hz,rfl⟩

/-- A property transferred through refinement, retaining order and multiplicity. -/
theorem connected_history (ms : Streams T α) (a : Nat → Action T) (t : T)
    (reg : a 0 = .register t) (truth : Source → T → List α) (n : Nat) (s : History α) :
    image (Relation.Comp (broker ms a t n) (consumer s)) (admissible ms truth) ⊆
      {z | z.2 = s ∨ z.2 = updated s (truth .left t ++ truth .right t)} := by
  apply (connected_refines ms a t reg truth n s).requirement
  intro z hz y he
  subst y
  rcases hz with rfl | rfl <;> simp

/-- Membership remembers the difference between absence and a completed batch. -/
theorem mem_completed (xs : List (Option (List α))) (batch : List α) :
    batch ∈ completed xs ↔ some batch ∈ xs := by
  induction xs with
  | nil => simp [completed]
  | cons x xs ih => cases x <;> simp [completed,ih]

/-- An actual emission selects the updated branch, excluding vacuous safety. -/
theorem delivered_result (s : Inputs T α) (ms : Streams T α) (a : Nat → Action T)
    (t : T) (reg : a 0 = .register t) (truth : Source → T → List α)
    (honest : (traceRep ms).Rel s truth) (initial : History α) (i : Nat) (out : List α)
    (emitted : response s ms a i = some (t,out)) :
    consume (history initial) initial (feedbackInputs s ms a t (i+1)) =
      ([updated initial (truth .left t ++ truth .right t)],
        updated initial (truth .left t ++ truth .right t)) := by
  have hm : out ∈ completed (feedbackInputs s ms a t (i+1)) := by
    apply (mem_completed _ _).mpr
    apply List.mem_map.mpr
    refine ⟨i,List.mem_range.mpr (Nat.lt_succ_self i),?_⟩
    change (response s ms a i).map Prod.snd = some out
    rw [emitted]; rfl
  rcases broker_allowed s ms a t reg truth honest (i+1) with h | h
  · rw [h] at hm; cases hm
  · exact consume_one initial _ _ h

/-- Fair available source progress and fair processing remain environmental
hypotheses. This existential theorem does not extract an executable horizon. -/
theorem eventual_update (s : Inputs T α) (ms : Streams T α) (a : Nat → Action T)
    (t : T) (reg : a 0 = .register t) (truth : Source → T → List α)
    (honest : (traceRep ms).Rel s truth) (initial : History α)
    (d : Delivery (sourceSchedule a)) (fair : d.Fair)
    (processing : ProcessingFair s ms a)
    (progress : ∀ source, ∃ k n, k ≤ d.available source n ∧
      t < (sourcePrefix (s source) (ms source) k).frontier) :
    ∃ n, consume (history initial) initial (feedbackInputs s ms a t n) =
      ([updated initial (truth .left t ++ truth .right t)],
        updated initial (truth .left t ++ truth .right t)) := by
  obtain ⟨i,out,_,he⟩ := eventual_response s ms a d fair processing t 1
    (registered s ms a t reg) progress
  exact ⟨i+1,delivered_result s ms a t reg truth honest initial i out he⟩

/-- Silence yields safety with no progress, for every finite processing bound. -/
theorem silent_consume (s : Inputs T α) (ms : Streams T α) (a : Nat → Action T)
    (t : T) (silent : ∀ i, response s ms a i = none) (initial : History α) (n : Nat) :
    consume (history initial) initial (feedbackInputs s ms a t n) = ([],initial) := by
  apply consume_zero
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [feedbackInputs,List.range_succ,List.map_append,completed_append,
      frameBatch,frame,silent,completed] using ih

end FRPSpec.ReactiveContracts
