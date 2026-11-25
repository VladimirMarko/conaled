import Applications.Sequences.AbstractFIFO

/-!
# Source queue equations and the raw two-list realization

The VFA ADT chapter gives two different queue contracts. Its six algebraic
equations compare actual states. Its four model equations compare decoded
lists and leave the empty-test operation unconstrained. Operations and proofs
are separate, and their payload and state universes are independent.

The pair implementation retains every source branch on every raw pair.
Observing peek does not return an updated state. Its concrete optional-head
adapter connects to the existing AbstractFIFO executor and clients; it does
not derive an optional head from an arbitrary model's unconstrained empty test.

Source: VFA 2.1 ADT.v, Queue, ListQueue, QueueAbs and TwoListQueueAbs.
The source correspondence is in docs/research/vfa-coverage.md and the MIT
notice is in docs/licenses/vfa-MIT.txt. Execution costs have a separate owner.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Sequences.SourceQueue
universe u v
variable {V : Type u} {Q : Type v}

/-- The explicit default belongs to each peek invocation. -/
structure Ops (V : Type u) (Q : Type v) where
  empty : Q
  isEmpty : Q → Bool
  enqueue : Q → V → Q
  dequeue : Q → Q
  peek : V → Q → V

/-- The six source equations, including literal state equality on dequeue. -/
structure Laws (ops : Ops V Q) : Prop where
  isEmpty_empty : ops.isEmpty ops.empty = true
  isEmpty_enqueue : ∀ q value, ops.isEmpty (ops.enqueue q value) = false
  peek_empty : ∀ default, ops.peek default ops.empty = default
  peek_enqueue : ∀ default q value, ops.peek default (ops.enqueue q value) = ops.peek value q
  dequeue_empty : ops.dequeue ops.empty = ops.empty
  dequeue_enqueue : ∀ q value, ops.dequeue (ops.enqueue q value) =
    if ops.isEmpty q then q else ops.enqueue (ops.dequeue q) value

/-- Exactly the source's four unguarded model laws. There is no empty-test law. -/
structure AbsLaws (ops : Ops V Q) (decode : Q → List V) : Prop where
  empty : decode ops.empty = []
  enqueue : ∀ q value, decode (ops.enqueue q value) = decode q ++ [value]
  peek : ∀ default q, ops.peek default q = (decode q).headD default
  dequeue : ∀ q, decode (ops.dequeue q) = (decode q).tail

/-- Appending a singleton is the source ListQueue enqueue operation. -/
def lists (V : Type u) : Ops V (List V) where
  empty := []
  isEmpty := List.isEmpty
  enqueue q value := q ++ [value]
  dequeue := List.tail
  peek default q := q.headD default

theorem lists_laws (V : Type u) : Laws (lists V) where
  isEmpty_empty := rfl
  isEmpty_enqueue q value := by cases q <;> rfl
  peek_empty _ := rfl
  peek_enqueue default q value := by cases q <;> rfl
  dequeue_empty := rfl
  dequeue_enqueue q value := by cases q <;> rfl

theorem lists_absLaws (V : Type u) : AbsLaws (lists V) id where
  empty := rfl
  enqueue _ _ := rfl
  peek _ _ := rfl
  dequeue _ := rfl

/-- Replacing the empty test preserves all four model laws, for any state type. -/
theorem AbsLaws.with_isEmpty {ops : Ops V Q} {decode : Q → List V}
    (laws : AbsLaws ops decode) (test : Q → Bool) :
    AbsLaws { ops with isEmpty := test } decode where
  empty := laws.empty
  enqueue := laws.enqueue
  peek := laws.peek
  dequeue := laws.dequeue

theorem lists_arbitrary_empty_test (test : List V → Bool) :
    AbsLaws { lists V with isEmpty := test } id :=
  (lists_absLaws V).with_isEmpty test

/-- This lawful model's empty test is false even on its empty state. -/
theorem model_empty_test_unconstrained (V : Type u) :
    AbsLaws { lists V with isEmpty := fun _ => false } id ∧
      ({ lists V with isEmpty := fun _ => false } : Ops V (List V)).isEmpty [] = false :=
  ⟨lists_arbitrary_empty_test _, rfl⟩

/-- Every raw pair is a source state; no normalization invariant is imposed. -/
abbrev TwoList (V : Type u) := List V × List V

def twoListDecode (q : TwoList V) : List V := q.1 ++ q.2.reverse

def twoListEmpty : TwoList V := ([], [])

def twoListIsEmpty : TwoList V → Bool
  | ([], []) => true
  | _ => false

def twoListEnqueue (q : TwoList V) (value : V) : TwoList V := (q.1, value :: q.2)

/-- The empty/empty branch and the reversed-back match are retained literally. -/
def twoListDequeue : TwoList V → TwoList V
  | ([], []) => ([], [])
  | ([], back) =>
      match back.reverse with
      | [] => ([], [])
      | _ :: front => (front, [])
  | (_ :: front, back) => (front, back)

/-- Peek returns only the observed value; it does not cache the reversed back. -/
def twoListPeek (default : V) : TwoList V → V
  | ([], []) => default
  | ([], back) =>
      match back.reverse with
      | [] => default
      | value :: _ => value
  | (value :: _, _) => value

def twoLists (V : Type u) : Ops V (TwoList V) where
  empty := twoListEmpty
  isEmpty := twoListIsEmpty
  enqueue := twoListEnqueue
  dequeue := twoListDequeue
  peek := twoListPeek

@[simp] theorem twoListEnqueue_mk (front back : List V) (value : V) :
    twoListEnqueue (front, back) value = (front, value :: back) := rfl

@[simp] theorem twoListDequeue_empty :
    twoListDequeue (twoListEmpty : TwoList V) = twoListEmpty := rfl

@[simp] theorem twoListDequeue_front (value : V) (front back : List V) :
    twoListDequeue (value :: front, back) = (front, back) := rfl

/-- An all-input value bridge; the definition still performs the source match. -/
theorem twoListDequeue_back (back : List V) :
    twoListDequeue ([], back) = (back.reverse.tail, []) := by
  cases back with
  | nil => rfl
  | cons value back =>
      simp only [twoListDequeue]
      cases (value :: back).reverse <;> rfl

@[simp] theorem twoListPeek_empty (default : V) :
    twoListPeek default twoListEmpty = default := rfl

@[simp] theorem twoListPeek_front (default value : V) (front back : List V) :
    twoListPeek default (value :: front, back) = value := rfl

theorem twoListPeek_back (default : V) (back : List V) :
    twoListPeek default ([], back) = back.reverse.headD default := by
  cases back with
  | nil => rfl
  | cons value back =>
      simp only [twoListPeek]
      cases (value :: back).reverse <;> rfl

@[simp] theorem twoListEmpty_decode :
    twoListDecode (twoListEmpty : TwoList V) = [] := rfl

theorem twoListEnqueue_decode (q : TwoList V) (value : V) :
    twoListDecode (twoListEnqueue q value) = twoListDecode q ++ [value] := by
  simp [twoListDecode, twoListEnqueue, List.reverse_cons, List.append_assoc]

theorem twoListPeek_decode (default : V) (q : TwoList V) :
    twoListPeek default q = (twoListDecode q).headD default := by
  rcases q with ⟨front, back⟩
  cases front with
  | nil => simpa only [twoListDecode, List.nil_append] using twoListPeek_back default back
  | cons value front => rfl

theorem twoListDequeue_decode (q : TwoList V) :
    twoListDecode (twoListDequeue q) = (twoListDecode q).tail := by
  rcases q with ⟨front, back⟩
  cases front with
  | nil => simp only [twoListDequeue_back, twoListDecode, List.reverse_nil,
      List.append_nil, List.nil_append]
  | cons value front => rfl

theorem twoLists_absLaws (V : Type u) : AbsLaws (twoLists V) twoListDecode where
  empty := twoListEmpty_decode
  enqueue := twoListEnqueue_decode
  peek := twoListPeek_decode
  dequeue := twoListDequeue_decode

/-- This concrete extra observation is not a field of AbsLaws. -/
theorem twoListIsEmpty_decode (q : TwoList V) :
    twoListIsEmpty q = (twoListDecode q).isEmpty := by
  rcases q with ⟨front, back⟩
  cases front <;> cases back <;> simp [twoListIsEmpty, twoListDecode]

theorem twoListIsEmpty_iff (q : TwoList V) :
    twoListIsEmpty q = true ↔ twoListDecode q = [] := by
  rw [twoListIsEmpty_decode]
  exact List.isEmpty_iff

/-- Actual optional-head branches, independent of the unconstrained abstract
empty-test field. -/
def twoListHead? : TwoList V → Option V
  | ([], []) => none
  | ([], back) =>
      match back.reverse with
      | [] => none
      | value :: _ => some value
  | (value :: _, _) => some value

theorem twoListHead?_back (back : List V) :
    twoListHead? ([], back) = back.reverse.head? := by
  cases back with
  | nil => rfl
  | cons value back =>
      simp only [twoListHead?]
      cases (value :: back).reverse <;> rfl

theorem twoListHead?_decode (q : TwoList V) :
    twoListHead? q = (twoListDecode q).head? := by
  rcases q with ⟨front, back⟩
  cases front with
  | nil => simpa only [twoListDecode, List.nil_append] using twoListHead?_back back
  | cons value front => rfl

theorem twoListPeek_eq_getD (default : V) (q : TwoList V) :
    twoListPeek default q = (twoListHead? q).getD default := by
  rw [twoListPeek_decode, twoListHead?_decode]
  cases twoListDecode q <;> rfl

/-- The existing FIFO interface uses value-before-state enqueue and optional
head; this adapter keeps the concrete source operations. -/
def twoListFIFO (V : Type u) : AbstractFIFO.Ops V (TwoList V) where
  empty := twoListEmpty
  snoc value q := twoListEnqueue q value
  tail := twoListDequeue
  head := twoListHead?

theorem twoList_simulation (V : Type u) :
    AbstractFIFO.Simulation (twoListFIFO V) (AbstractFIFO.lists V)
      (fun q xs => twoListDecode q = xs) where
  empty := rfl
  snoc value q xs related := by
    change twoListDecode (twoListEnqueue q value) = xs ++ [value]
    rw [twoListEnqueue_decode, related]
  tail q xs related := by
    change twoListDecode (twoListDequeue q) = xs.tail
    rw [twoListDequeue_decode, related]
  head q xs related := by
    change twoListHead? q = xs.head?
    rw [twoListHead?_decode, related]

/-- Arbitrary existing command histories, starting at any raw pair. -/
theorem twoList_run_decode (commands : List (AbstractFIFO.Command V)) (q : TwoList V) :
    twoListDecode (AbstractFIFO.run (twoListFIFO V) commands q) =
      AbstractFIFO.run (AbstractFIFO.lists V) commands (twoListDecode q) :=
  (twoList_simulation V).run_preserves commands rfl

theorem twoList_client_eq (commands : List (AbstractFIFO.Command V)) (q : TwoList V) :
    AbstractFIFO.client (twoListFIFO V) commands q =
      AbstractFIFO.client (AbstractFIFO.lists V) commands (twoListDecode q) :=
  (twoList_simulation V).client_eq commands rfl

theorem twoList_client_empty (commands : List (AbstractFIFO.Command V)) :
    AbstractFIFO.client (twoListFIFO V) commands twoListEmpty =
      AbstractFIFO.client (AbstractFIFO.lists V) commands [] :=
  (twoList_simulation V).client_empty commands

theorem twoList_representation_independent (commands : List (AbstractFIFO.Command V))
    (q r : TwoList V) (same : twoListDecode q = twoListDecode r) :
    AbstractFIFO.client (twoListFIFO V) commands q =
      AbstractFIFO.client (twoListFIFO V) commands r :=
  (twoList_simulation V).representation_independent commands same rfl

theorem twoList_peek_run (default : V) (commands : List (AbstractFIFO.Command V))
    (q : TwoList V) :
    twoListPeek default (AbstractFIFO.run (twoListFIFO V) commands q) =
      (AbstractFIFO.client (AbstractFIFO.lists V) commands (twoListDecode q)).getD default := by
  rw [twoListPeek_eq_getD]
  exact congrArg (fun result => result.getD default) (twoList_client_eq commands q)

/-- Enqueue-only reachability is an exact result of the existing executor. -/
theorem twoList_run_enqueues (values front back : List V) :
    AbstractFIFO.run (twoListFIFO V) (values.map AbstractFIFO.Command.enqueue) (front, back) =
      (front, values.reverse ++ back) := by
  induction values generalizing back with
  | nil => rfl
  | cons value values ih =>
      change AbstractFIFO.run (twoListFIFO V) (values.map AbstractFIFO.Command.enqueue)
        (front, value :: back) = (front, (value :: values).reverse ++ back)
      rw [ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem twoList_run_replicate_enqueue (n : Nat) (value : V) :
    AbstractFIFO.run (twoListFIFO V) (List.replicate n (.enqueue value)) twoListEmpty =
      ([], List.replicate n value) := by
  simpa [twoListEmpty] using twoList_run_enqueues (List.replicate n value) [] []

/-! Connected functional cases. Root's source-facing module supplies the exact
Nat module instantiations and chapter-wide clients. -/

theorem twoList_singleton (default value : V) :
    twoListDecode (twoListEnqueue twoListEmpty value) = [value] ∧
      twoListPeek default (twoListEnqueue twoListEmpty value) = value ∧
      twoListDequeue (twoListEnqueue twoListEmpty value) = twoListEmpty :=
  ⟨rfl, rfl, rfl⟩

theorem twoList_source_branches (default first second : V) :
    twoListPeek default ([first], [second]) = first ∧
      twoListDequeue ([first], [second]) = ([], [second]) ∧
      twoListPeek default ([], [second, first]) = first ∧
      twoListDequeue ([], [second, first]) = ([second], []) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem twoList_fifo_client (first second : V) :
    AbstractFIFO.client (twoListFIFO V) [.enqueue first, .enqueue second, .delete]
      twoListEmpty = some second := by
  rw [twoList_client_empty]
  rfl

/-- The source pair queue cannot satisfy the stronger raw-state dequeue law. -/
theorem twoList_dequeue_enqueue_counterexample :
    twoListDequeue (twoListEnqueue (([], [1]) : TwoList Nat) 2) = ([2], []) ∧
      (if twoListIsEmpty (([], [1]) : TwoList Nat) then ([], [1])
        else twoListEnqueue (twoListDequeue ([], [1])) 2) = ([], [2]) ∧
      (([2], []) : TwoList Nat) ≠ ([], [2]) := by decide

theorem twoList_counterexample_same_decode :
    twoListDecode (([2], []) : TwoList Nat) = [2] ∧
      twoListDecode (([], [2]) : TwoList Nat) = [2] := ⟨rfl, rfl⟩

theorem twoLists_not_laws : ¬ Laws (twoLists Nat) := by
  intro laws
  have equal := laws.dequeue_enqueue ([], [1]) 2
  have different : (([2], []) : TwoList Nat) ≠ ([], [2]) :=
    twoList_dequeue_enqueue_counterexample.2.2
  exact different equal

end Sequences.SourceQueue
