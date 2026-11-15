import Applications.Progress.Evaluation

/-!
# Finite delivery for state-based producers

A producer may perform silent work. `Delivers` records a finite trace, its
outputs, final state and exact number of atomic steps. Productivity requires
such traces for every finite observation. It is not inferred from safety of
state transitions. The semantics here is deterministic and has no scheduler.
-/
namespace Progress
universe u
variable {S T A B C : Type u}

/-- A transition emits a value or performs silent work. -/
abbrev Producer (S A : Type u) := S → Sum (A × S) S

inductive Delivers (step : Producer S A) : S → List A → S → Nat → Prop
  | nil (s) : Delivers step s [] s 0
  | cons {s t z a xs k l} : Evaluates step s (a, t) k →
      Delivers step t xs z l → Delivers step s (a :: xs) z (k + l)

/-- Existence for every length is distinct from halting the infinite producer. -/
def Productive (step : Producer S A) (s : S) : Prop :=
  ∀ n, ∃ xs t k, xs.length = n ∧ Delivers step s xs t k

/-- Local finite-progress evidence composes over observations. An invariant may
restrict the states for which the next output is guaranteed. For filtering,
this is the obligation to supply routes to sufficiently many matches. -/
theorem productive_of_next {step : Producer S A} (inv : S → Prop)
    (next : ∀ s, inv s → ∃ a t k, Evaluates step s (a, t) k ∧ inv t)
    (s : S) (hs : inv s) : Productive step s := by
  intro n
  induction n generalizing s with
  | zero => exact ⟨[], s, 0, rfl, .nil s⟩
  | succ n ih =>
    obtain ⟨a, t, k, h, ht⟩ := next s hs
    obtain ⟨xs, z, l, len, rest⟩ := ih t ht
    exact ⟨a :: xs, z, k + l, by simp [len], .cons h rest⟩

/-- Determinism gives coherence across all finite deliveries, including silent work. -/
theorem Delivers.coherent {step : Producer S A} {s xs ys t z k l}
    (h : Delivers step s xs t k) (j : Delivers step s ys z l) :
    xs.take ys.length = ys.take xs.length := by
  induction h generalizing ys z l with
  | nil => simp
  | cons h rest ih =>
    cases j with
    | nil => simp
    | cons j tail =>
      obtain ⟨eq, _⟩ := h.unique j
      cases eq
      simpa using ih tail

/-- Determinism fixes the state and transition count of the same output prefix. -/
theorem Delivers.unique {step : Producer S A} {s : S} {xs : List A} {t z : S} {k l : Nat}
    (h : Delivers step s xs t k) (j : Delivers step s xs z l) : t = z ∧ k = l := by
  induction h generalizing z l with
  | nil => cases j; exact ⟨rfl, rfl⟩
  | cons first _ ih =>
    cases j with
    | cons other tail =>
      obtain ⟨same, cost⟩ := first.unique other
      cases same
      cases cost
      obtain ⟨rfl, rfl⟩ := ih tail
      exact ⟨rfl, rfl⟩

/-- A silent prefix can precede a nonempty delivery, never a positive-cost empty one. -/
theorem Delivers.prepend_silent {step : Producer S A} {s t z : S} {a : A} {xs : List A}
    {k : Nat} (h : Delivers step t (a :: xs) z k) (silent : step s = .inr t) :
    Delivers step s (a :: xs) z (k + 1) := by
  cases h with
  | cons first rest =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Delivers.cons (Evaluates.next silent first) rest

/-- Guarded coalgebras have exactly one output per atomic step. -/
abbrev Coalgebra (S A : Type u) := S → A × S

def guarded (c : Coalgebra S A) : Producer S A := fun s => .inl (c s)

/-- Independent finite unfolding of the coalgebra, not a call to a checker. -/
def unfold (c : Coalgebra S A) (s : S) : Nat → List A
  | 0 => []
  | n + 1 => (c s).1 :: unfold c (c s).2 n

def advance (c : Coalgebra S A) (s : S) : Nat → S
  | 0 => s
  | n + 1 => advance c (c s).2 n

theorem unfold_add (c : Coalgebra S A) (s : S) (m n : Nat) :
    unfold c s (m + n) = unfold c s m ++ unfold c (advance c s m) n := by
  induction m generalizing s with
  | zero => simp [unfold, advance]
  | succ m ih => simp [Nat.succ_add, unfold, advance, ih]

theorem advance_add (c : Coalgebra S A) (s : S) (m n : Nat) :
    advance c s (m + n) = advance c (advance c s m) n := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simp [Nat.succ_add, advance, ih]

@[simp] theorem unfold_length (c : Coalgebra S A) (s : S) (n : Nat) :
    (unfold c s n).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [unfold, ih]

theorem guarded_delivery (c : Coalgebra S A) (s : S) (n : Nat) :
    Delivers (guarded c) s (unfold c s n) (advance c s n) n := by
  induction n generalizing s with
  | zero => exact .nil s
  | succ n ih =>
    simpa [unfold, advance, Nat.add_comm] using
      Delivers.cons (Evaluates.done (s := s) (step := guarded c) rfl) (ih (c s).2)

theorem guarded_productive (c : Coalgebra S A) (s : S) : Productive (guarded c) s :=
  fun n => ⟨unfold c s n, advance c s n, n, unfold_length c s n, guarded_delivery c s n⟩

/-- State maps that commute with coalgebra steps transport all finite observations. -/
theorem unfold_transport (c : Coalgebra S A) (d : Coalgebra T B)
    (state : S → T) (value : A → B)
    (commutes : ∀ s, d (state s) = (value (c s).1, state (c s).2)) (s : S) (n : Nat) :
    unfold d (state s) n = (unfold c s n).map value := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [unfold, commutes, ih]

def mapCoalgebra (f : A → B) (c : Coalgebra S A) : Coalgebra S B :=
  fun s => (f (c s).1, (c s).2)

theorem unfold_map (f : A → B) (c : Coalgebra S A) (s : S) (n : Nat) :
    unfold (mapCoalgebra f c) s n = (unfold c s n).map f :=
  unfold_transport c (mapCoalgebra f c) id f (fun _ => rfl) s n

def zipCoalgebra (c : Coalgebra S A) (d : Coalgebra T B) : Coalgebra (S × T) (A × B) :=
  fun (s, t) => (((c s).1, (d t).1), ((c s).2, (d t).2))

theorem unfold_zip (c : Coalgebra S A) (d : Coalgebra T B) (s : S) (t : T) (n : Nat) :
    unfold (zipCoalgebra c d) (s, t) n = (unfold c s n).zip (unfold d t n) := by
  induction n generalizing s t with
  | zero => rfl
  | succ n ih => simp [unfold, zipCoalgebra, ih]

/-- Inclusive scan emits the updated accumulator, retaining it as state. -/
def scanCoalgebra (f : B → A → B) (c : Coalgebra S A) : Coalgebra (B × S) B :=
  fun (b, s) => let b' := f b (c s).1; (b', (b', (c s).2))

def scanList (f : B → A → B) (b : B) : List A → List B
  | [] => []
  | a :: xs => let b' := f b a; b' :: scanList f b' xs

theorem unfold_scan (f : B → A → B) (c : Coalgebra S A) (b : B) (s : S) (n : Nat) :
    unfold (scanCoalgebra f c) (b, s) n = scanList f b (unfold c s n) := by
  induction n generalizing b s with
  | zero => rfl
  | succ n ih => simp [unfold, scanCoalgebra, scanList, ih]

/-- A slower realization inserts exactly one silent step before each emission.
The Boolean is a phase, not an environmental fairness assumption. -/
def paused (c : Coalgebra S A) : Producer (Bool × S) A
  | (false, s) => .inr (true, s)
  | (true, s) => .inl ((c s).1, (false, (c s).2))

theorem paused_next (c : Coalgebra S A) (s : S) :
    Evaluates (paused c) (false, s) ((c s).1, (false, (c s).2)) 2 :=
  .next rfl (.done rfl)

theorem paused_delivery (c : Coalgebra S A) (s : S) (n : Nat) :
    Delivers (paused c) (false, s) (unfold c s n) (false, advance c s n) (2 * n) := by
  induction n generalizing s with
  | zero => exact .nil _
  | succ n ih =>
    simpa [unfold, advance, Nat.mul_add, Nat.add_comm] using
      Delivers.cons (paused_next c s) (ih (c s).2)

/-- The realization comparison preserves progress with an explicit factor two.
It cannot insert an unbounded silent prefix between outputs. -/
theorem guarded_paused_progress (c : Coalgebra S A) (s : S) (n : Nat) :
    Delivers (guarded c) s (unfold c s n) (advance c s n) n ∧
    Delivers (paused c) (false, s) (unfold c s n) (false, advance c s n) (2 * n) :=
  ⟨guarded_delivery c s n, paused_delivery c s n⟩

/-- A silent transition that always continues has no finite evaluation. -/
theorem silent_no_evaluation (next : S → S) {s : S} {a : A} {k : Nat} :
    ¬ Evaluates (fun s => .inr (next s) : Machine S A) s a k := by
  intro h
  induction h with
  | done h => cases h
  | next _ _ ih => exact ih

/-- Filtering is a partial producer unless matching progress is supplied. -/
def filterProducer (p : A → Bool) (c : Coalgebra S A) : Producer S A :=
  fun s => if p (c s).1 then .inl (c s) else .inr (c s).2

/-- A valid finite search certificate for the next match is precisely a finite
operational route to that output. A bound is not inferred from the predicate. -/
theorem filter_no_match (p : A → Bool) (c : Coalgebra S A)
    (never : ∀ s, p (c s).1 = false) (s : S) :
    ¬ Productive (filterProducer p c) s := by
  intro h
  obtain ⟨xs, t, k, len, delivered⟩ := h 1
  cases delivered with
  | nil => simp at len
  | cons h _ =>
    have eq : filterProducer p c = fun s => .inr (c s).2 := by
      funext s
      simp [filterProducer, never]
    rw [eq] at h
    exact silent_no_evaluation _ h

end Progress
