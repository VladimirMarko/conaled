import Applications.Resources.Potential
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

/-! Actual front-array updates and ordered observations for two resize boundaries. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.DynamicFrontArrays
universe u
variable {α : Type u}

inductive Event (α : Type u) where
  | allocate (slots : Nat)
  | copy (index : Nat) (value : Option α)
  | write (index : Nat) (value : α)
  deriving DecidableEq, Repr

/-- Copy and write events record attempted storage updates; layout invariants
below establish that every event in a valid execution has an in-range index. -/
def work : List (Event α) → Nat
  | [] => 0
  | .allocate _ :: es => work es
  | .copy _ _ :: es => 1 + work es
  | .write _ _ :: es => 1 + work es

def allocation : List (Event α) → Nat
  | [] => 0
  | .allocate n :: es => n + allocation es
  | .copy _ _ :: es => allocation es
  | .write _ _ :: es => allocation es

theorem work_append (es fs : List (Event α)) : work (es ++ fs) = work es + work fs := by
  induction es with
  | nil => simp [work]
  | cons e es ih => cases e <;> simp [work, ih, Nat.add_assoc]

theorem allocation_append (es fs : List (Event α)) :
    allocation (es ++ fs) = allocation es + allocation fs := by
  induction es with
  | nil => simp [allocation]
  | cons e es ih => cases e <;> simp [allocation, ih, Nat.add_assoc]

/-- Copy the old values to increasing indices in the newly allocated buffer. -/
def copyInto : List (Option α) → Nat → Array (Option α) → Array (Option α) × List (Event α)
  | [], _, dst => (dst, [])
  | v :: vs, i, dst =>
      let r := copyInto vs (i + 1) (dst.setIfInBounds i v)
      (r.1, .copy i v :: r.2)

def copyEvents : List (Option α) → Nat → List (Event α)
  | [], _ => []
  | v :: vs, i => .copy i v :: copyEvents vs (i + 1)

theorem copyInto_trace (vs : List (Option α)) (i : Nat) (dst : Array (Option α)) :
    (copyInto vs i dst).2 = copyEvents vs i := by
  induction vs generalizing i dst with
  | nil => rfl
  | cons v vs ih => simp [copyInto, copyEvents, ih]

theorem copyInto_size (vs : List (Option α)) (i : Nat) (dst : Array (Option α)) :
    (copyInto vs i dst).1.size = dst.size := by
  induction vs generalizing i dst with
  | nil => rfl
  | cons v vs ih => simp [copyInto, ih]

theorem copyInto_work (vs : List (Option α)) (i : Nat) (dst : Array (Option α)) :
    work (copyInto vs i dst).2 = vs.length := by
  induction vs generalizing i dst with
  | nil => rfl
  | cons v vs ih => simp [copyInto, work, ih, Nat.add_comm]

theorem copyInto_allocation (vs : List (Option α)) (i : Nat) (dst : Array (Option α)) :
    allocation (copyInto vs i dst).2 = 0 := by
  induction vs generalizing i dst with
  | nil => rfl
  | cons v vs ih => simp [copyInto, allocation, ih]

theorem copyEvents_inbounds (vs : List (Option α)) (i cap : Nat)
    (h : i + vs.length ≤ cap) :
    ∀ e ∈ copyEvents vs i, ∃ j v, e = Event.copy j v ∧ j < cap := by
  induction vs generalizing i with
  | nil => simp [copyEvents]
  | cons v vs ih =>
      intro e he
      simp only [copyEvents, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨i, v, rfl, by simp only [List.length_cons] at h; omega⟩
      · exact ih (i + 1) (by simp only [List.length_cons] at h; omega) e he

/-- An independent destination-layout contract for the actual copying loop. -/
theorem copyInto_layout (vs pre post : List (Option α)) (dst : Array (Option α))
    (h : dst.toList = pre ++ List.replicate vs.length none ++ post) :
    (copyInto vs pre.length dst).1.toList = pre ++ vs ++ post := by
  induction vs generalizing pre dst with
  | nil => simpa [copyInto] using h
  | cons v vs ih =>
      have hset : (dst.setIfInBounds pre.length v).toList =
          (pre ++ [v]) ++ List.replicate vs.length none ++ post := by
        simp only [Array.toList_setIfInBounds, h, List.length_cons,
          List.replicate_succ, List.append_assoc]
        rw [List.set_append_right _ _ (Nat.le_refl _)]
        simp
      have hr := ih (pre ++ [v]) (dst.setIfInBounds pre.length v) hset
      simpa [copyInto, List.length_append, List.append_assoc] using hr

/-- Copy overwrites only its window, regardless of the old contents. -/
theorem copyInto_window (vs old pre post : List (Option α)) (dst : Array (Option α))
    (hlen : old.length = vs.length) (h : dst.toList = pre ++ old ++ post) :
    (copyInto vs pre.length dst).1.toList = pre ++ vs ++ post := by
  induction vs generalizing old pre dst with
  | nil =>
    have ho : old = [] := by simpa using hlen
    simpa [copyInto,ho] using h
  | cons v vs ih =>
    cases old with
    | nil => simp at hlen
    | cons o old =>
      have hset : (dst.setIfInBounds pre.length v).toList = (pre ++ [v]) ++ old ++ post := by
        simp only [Array.toList_setIfInBounds,h,List.append_assoc]
        rw [List.set_append_right _ _ (Nat.le_refl _)]
        simp
      have hr := ih old (pre ++ [v]) (dst.setIfInBounds pre.length v) (by simpa using hlen) hset
      simpa only [copyInto,List.length_append,List.length_singleton,List.append_assoc,List.cons_append,List.nil_append] using hr

structure State (α : Type u) where
  slots : Array (Option α)
  free : Nat
  deriving DecidableEq, Repr

/-- Unused cells are precisely the leading None cells. -/
def Layout (s : State α) (xs : List α) : Prop :=
  0 < s.slots.size ∧ s.slots.toList = List.replicate s.free none ++ xs.map some

def value (s : State α) : List α := (s.slots.toList.drop s.free).filterMap id

def empty : State α := ⟨Array.replicate 1 none, 1⟩

theorem empty_layout : Layout (empty : State α) [] := by simp [Layout, empty]

theorem layout_size {s : State α} {xs : List α} (h : Layout s xs) :
    s.slots.size = s.free + xs.length := by
  have hl := congrArg List.length h.2
  simpa using hl

theorem layout_value {s : State α} {xs : List α} (h : Layout s xs) : value s = xs := by
  simp [value, h.2]

/-- Double capacity, leaving the represented values in the upper half. -/
def grow (s : State α) : State α × List (Event α) :=
  let c := s.slots.size
  let r := copyInto (s.slots.toList.drop s.free) (c + s.free) (Array.replicate (2 * c) none)
  (⟨r.1, c + s.free⟩, .allocate (2 * c) :: r.2)

theorem grow_size (s : State α) : (grow s).1.slots.size = 2 * s.slots.size := by
  simp [grow, copyInto_size]

theorem grow_free (s : State α) : (grow s).1.free = s.slots.size + s.free := rfl

theorem grow_work (s : State α) : work (grow s).2 = s.slots.size - s.free := by
  simp [grow, work, copyInto_work]

theorem grow_allocation (s : State α) : allocation (grow s).2 = 2 * s.slots.size := by
  simp [grow, allocation, copyInto_allocation]

theorem grow_layout {s : State α} {xs : List α} (h : Layout s xs) :
    Layout (grow s).1 xs := by
  have hs := layout_size h
  have hsrc : s.slots.toList.drop s.free = xs.map some := by simp [h.2]
  have hpad : (Array.replicate (2 * s.slots.size) (none : Option α)).toList =
      List.replicate (s.slots.size + s.free) none ++
        List.replicate (xs.map some).length none ++ [] := by
    simp only [Array.toList_replicate, List.length_map, List.append_nil,
      List.replicate_append_replicate]
    congr 1
    omega
  have hc := copyInto_layout (xs.map some)
    (List.replicate (s.slots.size + s.free) none) []
    (Array.replicate (2 * s.slots.size) none) hpad
  have hpos := h.1
  refine ⟨by rw [grow_size]; omega, ?_⟩
  simpa only [grow, hsrc, List.length_replicate, List.append_nil] using hc

theorem grow_upper_half (s : State α) (hfull : s.free = 0) :
    (grow s).1.slots.toList = List.replicate s.slots.size none ++ s.slots.toList := by
  have hpad : (Array.replicate (2 * s.slots.size) (none : Option α)).toList =
      List.replicate s.slots.size none ++
        List.replicate s.slots.toList.length none ++ [] := by
    simp [List.replicate_append_replicate, Nat.two_mul]
  have h := copyInto_layout s.slots.toList (List.replicate s.slots.size none) []
    (Array.replicate (2 * s.slots.size) none) hpad
  simpa [grow, hfull] using h

theorem grow_copy_indices {s : State α} {xs : List α} (h : Layout s xs) :
    ∀ e ∈ (grow s).2, (∃ n, e = Event.allocate n) ∨
      (∃ i v, e = Event.copy i v ∧ i < (grow s).1.slots.size) := by
  have hs := layout_size h
  intro e he
  simp only [grow, List.mem_cons] at he
  rcases he with rfl | he
  · exact Or.inl ⟨_, rfl⟩
  · apply Or.inr
    rw [grow_size]
    rw [copyInto_trace] at he
    exact copyEvents_inbounds _ _ _ (by simp only [List.length_drop, Array.length_toList]; omega) e he

/-- One actual front write, after the caller has ensured a spare cell. -/
def writeFront (x : α) (s : State α) : State α × List (Event α) :=
  (⟨s.slots.setIfInBounds (s.free - 1) (some x), s.free - 1⟩,
    [.write (s.free - 1) x])

theorem writeFront_layout (x : α) {s : State α} {xs : List α}
    (h : Layout s xs) (hfree : 0 < s.free) : Layout (writeFront x s).1 (x :: xs) := by
  have hr : List.replicate s.free (none : Option α) =
      List.replicate (s.free - 1) none ++ [none] := by
    change List.replicate s.free none =
      List.replicate (s.free - 1) none ++ List.replicate 1 none
    rw [List.replicate_append_replicate]
    congr 1
    omega
  refine ⟨by simpa [writeFront] using h.1, ?_⟩
  simp only [writeFront, Array.toList_setIfInBounds, h.2, hr,
    List.append_assoc, List.map_cons]
  rw [List.set_append_right _ _ (by simp)]
  simp

/-- Literal exercise convention: grow when the old array is already full. -/
def add (x : α) (s : State α) : State α × List (Event α) :=
  if s.free = 0 then
    let g := grow s
    let r := writeFront x g.1
    (r.1, g.2 ++ r.2)
  else writeFront x s

theorem add_layout (x : α) {s : State α} {xs : List α} (h : Layout s xs) :
    Layout (add x s).1 (x :: xs) := by
  unfold add
  split
  · apply writeFront_layout x (grow_layout h)
    simp only [grow_free]
    have hp := h.1
    omega
  · apply writeFront_layout x h
    omega

theorem add_value (x : α) {s : State α} {xs : List α} (h : Layout s xs) :
    value (add x s).1 = x :: xs := layout_value (add_layout x h)

theorem add_size (x : α) (s : State α) :
    (add x s).1.slots.size = if s.free = 0 then 2 * s.slots.size else s.slots.size := by
  by_cases h : s.free = 0 <;> simp [add, h, writeFront, grow_size]

theorem add_capacity_mono (x : α) (s : State α) : s.slots.size ≤ (add x s).1.slots.size := by
  rw [add_size]
  split <;> omega

theorem add_work (x : α) (s : State α) :
    work (add x s).2 = if s.free = 0 then s.slots.size + 1 else 1 := by
  by_cases h : s.free = 0 <;> simp [add, h, work_append, grow_work, writeFront, work]

theorem add_allocation (x : α) (s : State α) :
    allocation (add x s).2 = if s.free = 0 then 2 * s.slots.size else 0 := by
  by_cases h : s.free = 0 <;> simp [add, h, allocation_append, grow_allocation, writeFront, allocation]

def InBounds (cap : Nat) : Event α → Prop
  | .allocate _ => True
  | .copy i _ => i < cap
  | .write i _ => i < cap

theorem writeFront_inbounds (x : α) {s : State α} {xs : List α}
    (h : Layout s xs) (hfree : 0 < s.free) :
    ∀ e ∈ (writeFront x s).2, InBounds (writeFront x s).1.slots.size e := by
  have hs := layout_size h
  intro e he
  simp only [writeFront, List.mem_singleton] at he
  subst e
  simp only [writeFront, InBounds, Array.size_setIfInBounds]
  omega

theorem add_inbounds (x : α) {s : State α} {xs : List α} (h : Layout s xs) :
    ∀ e ∈ (add x s).2, InBounds (add x s).1.slots.size e := by
  by_cases hfull : s.free = 0
  · simp only [add, hfull, ite_true, List.mem_append]
    intro e he
    rcases he with he | he
    · have hg := grow_copy_indices h e he
      rcases hg with ⟨n, rfl⟩ | ⟨i, v, rfl, hi⟩
      · trivial
      · simpa only [InBounds, writeFront, Array.size_setIfInBounds] using hi
    · have hp := h.1
      exact writeFront_inbounds x (grow_layout h) (by simp only [grow_free]; omega) e he
  · simpa only [add, hfull, ite_false] using
      writeFront_inbounds x h (by omega)

/-- Use the existing ordered workload executor, with a native free observation. -/
def execute (step : α → State α → State α × List (Event α)) (xs : List α) (s : State α) :
    State α × List (Event α) :=
  let r := Resources.run (fun x t => let a := step x t
    (a.1, Additive.ofMul (FreeMonoid.ofList a.2))) xs s
  (r.1,r.2.toMul.toList)

@[simp] theorem execute_nil (step : α → State α → State α × List (Event α)) (s : State α) :
    execute step [] s = (s,[]) := rfl
@[simp] theorem execute_cons (step : α → State α → State α × List (Event α))
    (x : α) (xs : List α) (s : State α) :
    execute step (x::xs) s = ((execute step xs (step x s).1).1,
      (step x s).2 ++ (execute step xs (step x s).1).2) := rfl

def adds (xs : List α) (s : State α) : State α × List (Event α) := execute add xs s
@[simp] theorem adds_nil (s : State α) : adds [] s = (s,[]) := rfl
@[simp] theorem adds_cons (x : α) (xs : List α) (s : State α) :
    adds (x::xs) s = ((adds xs (add x s).1).1,(add x s).2 ++ (adds xs (add x s).1).2) := rfl

theorem adds_layout (xs : List α) {s : State α} {ys : List α} (h : Layout s ys) :
    Layout (adds xs s).1 (xs.reverse ++ ys) := by
  induction xs generalizing s ys with
  | nil => simpa [adds_nil, adds_cons] using h
  | cons x xs ih =>
      have hr := ih (add_layout x h)
      simpa [adds_nil, adds_cons, List.reverse_cons, List.append_assoc] using hr

theorem adds_value (xs : List α) {s : State α} {ys : List α} (h : Layout s ys) :
    value (adds xs s).1 = xs.reverse ++ ys := layout_value (adds_layout xs h)

theorem adds_capacity_mono (xs : List α) (s : State α) :
    s.slots.size ≤ (adds xs s).1.slots.size := by
  induction xs generalizing s with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (add_capacity_mono x s) (ih (add x s).1)

theorem adds_inbounds (xs : List α) {s : State α} {ys : List α} (h : Layout s ys) :
    ∀ e ∈ (adds xs s).2, InBounds (adds xs s).1.slots.size e := by
  induction xs generalizing s ys with
  | nil => simp [adds_nil]
  | cons x xs ih =>
      intro e he
      simp only [adds_cons, List.mem_append] at he
      rcases he with he | he
      · have hi := add_inbounds x h e he
        have hc := adds_capacity_mono xs (add x s).1
        cases e <;> simp only [InBounds, adds_cons] at hi ⊢ <;> omega
      · exact ih (add_layout x h) e he

theorem from_empty_value (xs : List α) : value (adds xs empty).1 = xs.reverse := by
  simpa using adds_value xs empty_layout


namespace Eager
def add (x : α) (s : State α) : State α × List (Event α) :=
  if s.free ≤ 1 then
    let g := grow s
    let r := writeFront x g.1
    (r.1, g.2 ++ r.2)
  else writeFront x s

theorem add_layout (x : α) {s : State α} {xs : List α} (h : Layout s xs) :
    Layout (add x s).1 (x :: xs) := by
  unfold add
  split
  · apply writeFront_layout x (grow_layout h)
    have hp := h.1
    simp only [grow_free]
    omega
  · apply writeFront_layout x h
    omega

theorem add_spare (x : α) {s : State α} {xs : List α}
    (h : Layout s xs) (hfree : 0 < s.free) : 0 < (add x s).1.free := by
  have hp := h.1
  unfold add
  split
  · simp only [writeFront, grow_free]
    omega
  · simp only [writeFront]
    omega

theorem add_value (x : α) {s : State α} {xs : List α} (h : Layout s xs) :
    value (add x s).1 = x :: xs := layout_value (add_layout x h)

theorem add_size (x : α) (s : State α) :
    (add x s).1.slots.size = if s.free ≤ 1 then 2 * s.slots.size else s.slots.size := by
  by_cases h : s.free ≤ 1 <;> simp [add, h, writeFront, grow_size]

theorem add_work (x : α) (s : State α) :
    work (add x s).2 = if s.free ≤ 1 then s.slots.size - s.free + 1 else 1 := by
  by_cases h : s.free ≤ 1 <;> simp [add, h, work_append, grow_work, writeFront, work]

theorem add_allocation (x : α) (s : State α) :
    allocation (add x s).2 = if s.free ≤ 1 then 2 * s.slots.size else 0 := by
  by_cases h : s.free ≤ 1 <;> simp [add, h, allocation_append, grow_allocation, writeFront, allocation]

theorem add_inbounds (x : α) {s : State α} {xs : List α} (h : Layout s xs) :
    ∀ e ∈ (add x s).2, InBounds (add x s).1.slots.size e := by
  by_cases hsmall : s.free ≤ 1
  · simp only [add, hsmall, ite_true, List.mem_append]
    intro e he
    rcases he with he | he
    · have hg := grow_copy_indices h e he
      rcases hg with ⟨n, rfl⟩ | ⟨i, v, rfl, hi⟩
      · trivial
      · simpa only [InBounds, writeFront, Array.size_setIfInBounds] using hi
    · have hp := h.1
      exact writeFront_inbounds x (grow_layout h) (by simp only [grow_free]; omega) e he
  · simpa only [add, hsmall, ite_false] using writeFront_inbounds x h (by omega)

def adds (xs : List α) (s : State α) : State α × List (Event α) := execute add xs s
@[simp] theorem adds_nil (s : State α) : adds [] s = (s,[]) := rfl
@[simp] theorem adds_cons (x : α) (xs : List α) (s : State α) :
    adds (x::xs) s = ((adds xs (add x s).1).1,(add x s).2 ++ (adds xs (add x s).1).2) := rfl

theorem adds_layout (xs : List α) {s : State α} {ys : List α} (h : Layout s ys) :
    Layout (adds xs s).1 (xs.reverse ++ ys) := by
  induction xs generalizing s ys with
  | nil => simpa [adds_nil, adds_cons] using h
  | cons x xs ih =>
      have hr := ih (add_layout x h)
      simpa [adds_nil, adds_cons, List.reverse_cons, List.append_assoc] using hr

theorem adds_spare (xs : List α) {s : State α} {ys : List α}
    (h : Layout s ys) (hfree : 0 < s.free) : 0 < (adds xs s).1.free := by
  induction xs generalizing s ys with
  | nil => exact hfree
  | cons x xs ih => exact ih (add_layout x h) (add_spare x h hfree)

theorem adds_value (xs : List α) {s : State α} {ys : List α} (h : Layout s ys) :
    value (adds xs s).1 = xs.reverse ++ ys := layout_value (adds_layout xs h)

theorem logical_agreement (xs : List α) {s : State α} {ys : List α} (h : Layout s ys) :
    value (adds xs s).1 = value (DynamicFrontArrays.adds xs s).1 := by
  rw [adds_value xs h, DynamicFrontArrays.adds_value xs h]


end Eager
end Resources.DynamicFrontArrays
