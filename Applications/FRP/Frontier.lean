import Applications.FRP.Spec
import SquareKit.Relations

/-! Exploratory complete-window source protocol for #27. A packet closes an interval
of timestamps, including silence. Time and payload stay generic; rational time is
executable. No scheduler, phase evaluator, or source honesty is assumed implemented. -/

namespace FRPSpec.Frontier

variable {T α : Type} [LinearOrder T]

abbrev Log (T α : Type) := List (T × List α)

/-- Retain list order and multiplicity within each timestamp. -/
def batch (xs : Log T α) (t : T) : List α :=
  xs.foldr (fun x acc => if x.1 = t then x.2 ++ acc else acc) []

@[simp] theorem batch_append (xs ys : Log T α) (t : T) :
    batch (xs ++ ys) t = batch xs t ++ batch ys t := by
  induction xs with
  | nil => simp [batch]
  | cons x xs ih =>
    simp only [List.cons_append, batch, List.foldr_cons] at *
    split <;> simp_all [List.append_assoc]

theorem batch_empty (xs : Log T α) (t : T)
    (h : ∀ x ∈ xs, x.1 ≠ t) : batch xs t = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [batch, List.foldr_cons]
    rw [ite_eq_right (h x (by simp))]
    exact ih (fun y hy => h y (by simp [hy]))

structure State (T α : Type) where
  frontier : T
  log : Log T α
  deriving DecidableEq, Repr

/-- Stored observations must already be closed. -/
def State.Valid (s : State T α) : Prop :=
  ∀ x ∈ s.log, x.1 < s.frontier

/-- A completion can have any future, including an infinite future. -/
def State.Completes (s : State T α) (truth : T → List α) : Prop :=
  ∀ t, t < s.frontier → batch s.log t = truth t

/-- Absence before the initial frontier is part of the initialization contract. -/
def initial (w : T) : State T α := ⟨w, []⟩

def windowValid (s : State T α) (w : T) (xs : Log T α) : Prop :=
  s.frontier ≤ w ∧ ∀ x ∈ xs, s.frontier ≤ x.1 ∧ x.1 < w

instance (s : State T α) (w : T) (xs : Log T α) :
    Decidable (windowValid s w xs) := by
  unfold windowValid
  infer_instance

/-- Omitted timestamps in the closed window assert an empty batch.
Fragments at the same timestamp are concatenated in packet order. -/
def advance (s : State T α) (w : T) (xs : Log T α) : Option (State T α) :=
  if windowValid s w xs then some ⟨w, s.log ++ xs⟩ else none

theorem advance_valid {s q : State T α} {w : T} {xs : Log T α}
    (hs : s.Valid) (h : advance s w xs = some q) : q.Valid := by
  unfold advance at h
  split at h
  next hw =>
    cases h
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact lt_of_lt_of_le (hs x hx) hw.1
    · exact (hw.2 x hx).2
  next => simp at h

/-- Advancing cannot change any already certified observation. -/
theorem advance_refines {s q : State T α} {w : T} {xs : Log T α}
    (h : advance s w xs = some q) :
    s.frontier ≤ q.frontier ∧
      ∀ t, t < s.frontier → batch q.log t = batch s.log t := by
  unfold advance at h
  split at h
  next hw =>
    cases h
    refine ⟨hw.1, ?_⟩
    intro t ht
    rw [batch_append, batch_empty xs t, List.append_nil]
    intro x hx he
    exact (not_le_of_gt ht) (he ▸ (hw.2 x hx).1)
  next => simp at h

/-- Source honesty is a semantic obligation, separate from packet validation. -/
theorem advance_sound {s q : State T α} {w : T} {xs : Log T α}
    {truth : T → List α} (hs : s.Valid) (old : s.Completes truth)
    (h : advance s w xs = some q)
    (fresh : ∀ t, s.frontier ≤ t → t < w → batch xs t = truth t) :
    q.Completes truth := by
  have refines := advance_refines h
  unfold advance at h
  split at h
  next hw =>
    cases h
    intro t ht
    by_cases hp : t < s.frontier
    · exact (refines.2 t hp).trans (old t hp)
    · have hn := le_of_not_gt hp
      change batch (s.log ++ xs) t = truth t
      rw [batch_append, batch_empty s.log t, List.nil_append]
      · exact fresh t hn ht
      · intro x hx he
        exact (not_lt_of_ge hn) (he ▸ hs x hx)
  next => simp at h

/-- A complete merge batch is available only after both frontiers cross it. -/
def observeMerge (l r : State T α) (t : T) : Option (List α) :=
  if t < l.frontier ∧ t < r.frontier then
    some (batch l.log t ++ batch r.log t)
  else none

theorem observeMerge_sound {l r : State T α} {t : T} {out : List α}
    (h : observeMerge l r t = some out) :
    ∀ left right, l.Completes left → r.Completes right →
      out = left t ++ right t := by
  intro left right hl hr
  unfold observeMerge at h
  split at h
  next ht =>
    simp only [Option.some.injEq] at h
    rw [← h, hl t ht.1, hr t ht.2]
  next => simp at h

/-- Two observations with the same source completions agree regardless of log layout. -/
theorem observations_agree {l r l' r' : State T α} {t : T} {a b : List α}
    {left right : T → List α}
    (hl : l.Completes left) (hr : r.Completes right)
    (hl' : l'.Completes left) (hr' : r'.Completes right)
    (ha : observeMerge l r t = some a) (hb : observeMerge l' r' t = some b) :
    a = b :=
  (observeMerge_sound ha left right hl hr).trans
    (observeMerge_sound hb left right hl' hr').symm

theorem completion_exists (s : State T α) : ∃ truth, s.Completes truth :=
  ⟨batch s.log, fun _ _ => rfl⟩

theorem advance_completion {s q : State T α} {w : T} {xs : Log T α}
    {truth : T → List α} (h : advance s w xs = some q)
    (hq : q.Completes truth) : s.Completes truth := by
  obtain ⟨hw, he⟩ := advance_refines h
  intro t ht
  exact (he t ht).symm.trans (hq t (lt_of_lt_of_le ht hw))

/-- Partial observations relate to every possible value while unavailable. -/
def observationRep (α : Type) : Relational.RelRep where
  R := Option (List α)
  S := List α
  Rel result truth := ∀ out, result = some out → out = truth

def sourceRep (T α : Type) [LinearOrder T] : Relational.RelRep where
  R := State T α
  S := T → List α
  Rel := State.Completes

def mergeObservation (t : T) : Relational.RelSquare
    (Relational.product (sourceRep T α) (sourceRep T α)) (observationRep α) where
  impl p := observeMerge p.1 p.2 t
  spec p := p.1 t ++ p.2 t
  preserves h _out ho := observeMerge_sound ho _ _ h.1 h.2

def mapObservation {β : Type} (f : α → β) :
    Relational.RelSquare (observationRep α) (observationRep β) where
  impl := Option.map (List.map f)
  spec := List.map f
  preserves := by
    intro r s h out ho
    cases r with
    | none => simp at ho
    | some xs =>
      have he := h xs rfl
      simp only [Option.map_some, Option.some.injEq] at ho
      exact ho.symm.trans (congrArg (List.map f) he)

/-- The shared composition operation transports merge soundness through a consumer. -/
def mappedMergeObservation {β : Type} (f : α → β) (t : T) :=
  Relational.compose (mapObservation f) (mergeObservation (α := α) t)

/-- The finite log defines a past-finite real-time event. -/
noncomputable def logEvent (xs : Log ℝ α) : Event α where
  «at» := batch xs
  finite_past := by
    intro t
    classical
    apply (xs.map Prod.fst).toFinset.finite_toSet.subset
    intro u hu
    simp only [List.coe_toFinset, Set.mem_ofPred_eq, List.mem_map]
    by_contra h
    apply hu.2
    apply batch_empty
    intro x hx he
    exact h ⟨x, hx, he⟩

noncomputable def toPrefix (s : State ℝ α) : Prefix α :=
  ⟨s.frontier, logEvent s.log⟩

/-- Exact bridge at real timestamps; this does not embed a rational evaluator. -/
theorem completes_iff_prefix_sound (s : State ℝ α) (truth : Event α) :
    s.Completes truth.at ↔ (toPrefix s).Sound truth := Iff.rfl

end FRPSpec.Frontier
