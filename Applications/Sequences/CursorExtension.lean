import Applications.Sequences.AbstractFIFO

/-! Experimental semantic type extension for #262. A cursor is a queue with a
selected dependent position, including its end position. This host-level type
constructor does not extend the fixed STLC grammar. See
`docs/research/semantic-type-extension.md` for admission and adequacy boundaries. -/
namespace Sequences.AbstractFIFO.CursorExtension
universe u
variable {α Q : Type u}

/-- A selected position is data; its bound is a proof. -/
structure Cursor (Q : Type u) (size : Q → Nat) where
  value : Q
  position : Fin (size value + 1)

/-- New type admission is a correspondence with the independently specified
sequence length, not a definition of that sequence's denotation. -/
def Admissible (rel : Q → List α → Prop) (size : Q → Nat) : Prop :=
  ∀ q xs, rel q xs → size q = xs.length

/-- Type interpretation retains both the old relation and the selected index. -/
def Related (rel : Q → List α → Prop) {size : Q → Nat}
    (c : Cursor Q size) (d : Cursor (List α) List.length) : Prop :=
  rel c.value d.value ∧ c.position.val = d.position.val

/-- Updating the queue clips a cursor to the new end position. This operation
is total, including empty queues and deletion past the end. -/
def resize {size : Q → Nat} (f : Q → Q) (c : Cursor Q size) : Cursor Q size :=
  ⟨f c.value, ⟨min c.position.val (size (f c.value)),
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩

def ops (a : Ops α Q) (size : Q → Nat) : Ops α (Cursor Q size) where
  empty := ⟨a.empty, ⟨0, Nat.zero_lt_succ _⟩⟩
  snoc x := resize (a.snoc x)
  tail := resize a.tail
  head c := a.head c.value

/-- Compatibility for the new selected-witness update rule. -/
theorem resize_related {rel : Q → List α → Prop} {size : Q → Nat}
    (admitType : Admissible rel size) (f : Q → Q) (g : List α → List α)
    (compatible : ∀ q xs, rel q xs → rel (f q) (g xs))
    {c : Cursor Q size} {d : Cursor (List α) List.length} (h : Related rel c d) :
    Related rel (resize f c) (resize g d) := by
  refine ⟨compatible _ _ h.1, ?_⟩
  change min c.position.val (size (f c.value)) = min d.position.val (g d.value).length
  rw [h.2, admitType _ _ (compatible _ _ h.1)]

/-- A new constructor may choose any valid index, not only zero. Its semantic
argument is transported in the dependent family by the admissibility law. -/
theorem select_related {rel : Q → List α → Prop} {size : Q → Nat}
    (admitType : Admissible rel size) {q xs} (h : rel q xs)
    (i : Fin (size q + 1)) :
    Related rel (⟨q, i⟩ : Cursor Q size)
      ⟨xs, Fin.cast (congrArg (fun n => n + 1) (admitType q xs h)) i⟩ :=
  ⟨h, rfl⟩

/-- Relational retention implies equality of the actual transported Fin value,
not only equality after observing the queue head. -/
theorem selected_transport {rel : Q → List α → Prop} {size : Q → Nat}
    (admitType : Admissible rel size)
    {c : Cursor Q size} {d : Cursor (List α) List.length} (h : Related rel c d) :
    Fin.cast (congrArg (fun n => n + 1) (admitType _ _ h.1)) c.position = d.position :=
  Fin.ext h.2

/-- Admission plus the old operation compatibility and new resize rule retain
all four FIFO compatibility obligations at the richer semantic type. -/
theorem simulation (a : Ops α Q) {rel : Q → List α → Prop} {size : Q → Nat}
    (old : Simulation a (lists α) rel) (admitType : Admissible rel size) :
    Simulation (ops a size) (ops (lists α) List.length) (Related rel) where
  empty := ⟨old.empty, rfl⟩
  snoc x _ _ h := resize_related admitType (a.snoc x) ((lists α).snoc x) (old.snoc x) h
  tail _ _ h := resize_related admitType a.tail (lists α).tail old.tail h
  head _ _ h := old.head _ _ h.1

/-- The old observation forgets the cursor. This forgetful map is not the
extension's full observation contract. -/
theorem forget_simulation (α : Type u) :
    Simulation (ops (lists α) List.length) (lists α) (fun c xs => c.value = xs) where
  empty := rfl
  snoc x _ _ h := congrArg ((lists α).snoc x) h
  tail _ _ h := congrArg (lists α).tail h
  head _ _ h := congrArg (lists α).head h

/-- Bounded extension: the existing public composition theorem yields the old
client's original simulation interface, retaining an intermediate cursor. -/
theorem extension (a : Ops α Q) {rel : Q → List α → Prop} {size : Q → Nat}
    (old : Simulation a (lists α) rel) (admitType : Admissible rel size) :
    Simulation (ops a size) (lists α)
      (fun c xs => ∃ d, Related rel c d ∧ d.value = xs) :=
  (simulation a old admitType).comp (forget_simulation α)

/-- Unchanged public client theorem, for arbitrary words and initial witnesses. -/
theorem old_client (a : Ops α Q) {rel : Q → List α → Prop} {size : Q → Nat}
    (old : Simulation a (lists α) rel) (admitType : Admissible rel size)
    (cs : List (Command α)) {c : Cursor Q size} {xs : List α}
    (h : ∃ d, Related rel c d ∧ d.value = xs) :
    client (ops a size) cs c = client (lists α) cs xs :=
  (extension a old admitType).client_eq cs h

/-- Reuse also retains the stronger relation after the entire old client word. -/
theorem run_retains (a : Ops α Q) {rel : Q → List α → Prop} {size : Q → Nat}
    (old : Simulation a (lists α) rel) (admitType : Admissible rel size)
    (cs : List (Command α)) {c : Cursor Q size} {d : Cursor (List α) List.length}
    (h : Related rel c d) :
    Related rel (run (ops a size) cs c) (run (ops (lists α) List.length) cs d) :=
  (simulation a old admitType).run_preserves cs h

/-- The direct route reproves the same word induction. It uses the same type
admission and new-rule compatibility; it is retained for the author-work comparison. -/
theorem direct_run (a : Ops α Q) {rel : Q → List α → Prop} {size : Q → Nat}
    (old : Simulation a (lists α) rel) (admitType : Admissible rel size)
    (cs : List (Command α)) {c : Cursor Q size} {d : Cursor (List α) List.length}
    (h : Related rel c d) :
    Related rel (run (ops a size) cs c) (run (ops (lists α) List.length) cs d) := by
  induction cs generalizing c d with
  | nil => exact h
  | cons cmd cs ih =>
    apply ih
    cases cmd with
    | enqueue x => exact resize_related admitType _ _ (old.snoc x) h
    | delete => exact resize_related admitType _ _ old.tail h

end Sequences.AbstractFIFO.CursorExtension
