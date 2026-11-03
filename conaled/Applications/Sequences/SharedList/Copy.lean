import Applications.Sequences.SharedList.Basic
import SquareKit.Relations

/-! Path copying follows actual root links. Fuel bounds totalize malformed
inputs; valid public calls obtain sufficient fuel from the allocation frontier.
The measured count is one structural visit per recursive call, including the
empty case. Allocation is independently counted by the frontier difference. -/
set_option autoImplicit false
set_option warningAsError true

namespace Sequences.SharedList
variable {α : Type}

/-- Initialize a prefix from external values, sharing an already stored suffix. -/
def prepend : List α → Store α → Root → Store α × Root
  | [], s, r => (s, r)
  | x :: xs, s, r =>
      let rest := prepend xs s r
      allocate rest.1 x rest.2

theorem prepend_correct (xs : List α) {s : Store α} {r : Root} {ys : List α}
    (h : Represents s.heap r ys) :
    Durability.Extends s.heap (prepend xs s r).1.heap ∧
    Represents (prepend xs s r).1.heap (prepend xs s r).2 (xs ++ ys) ∧
    (prepend xs s r).1.next = s.next + xs.length := by
  induction xs with
  | nil => exact ⟨Durability.Extends.refl _, h, by simp [prepend]⟩
  | cons x xs ih =>
      refine ⟨ih.1.trans (allocate_extends _ _ _), allocate_represents ih.2.1 x, ?_⟩
      simp only [prepend, allocate_next, ih.2.2, List.length_cons]
      omega

def load (xs : List α) : Store α × Root := prepend xs empty none

theorem load_represents (xs : List α) :
    Represents (load xs).1.heap (load xs).2 xs := by
  simpa only [load, List.append_nil] using (prepend_correct xs (s := empty) .nil).2.1

@[simp] theorem load_next (xs : List α) : (load xs).1.next = xs.length := by
  simpa [load, empty] using (prepend_correct xs (s := empty) .nil).2.2

def appendRunFuel : Nat → Store α → Root → Root →
    Resources.Measured (Option (Store α × Root)) Nat
  | _, s, none, q => (some (s, q), 1)
  | 0, _, some _, _ => (none, 0)
  | n + 1, s, some a, q =>
      match s.heap a with
      | none => (none, 1)
      | some (x, r) =>
          let rest := appendRunFuel n s r q
          (rest.1.map (fun out => allocate out.1 x out.2), rest.2 + 1)

theorem appendRunFuel_correct {s : Store α} {r q : Root} {xs ys : List α}
    (hx : Represents s.heap r xs) (hy : Represents s.heap q ys) {fuel : Nat}
    (enough : xs.length ≤ fuel) :
    ∃ out, appendRunFuel fuel s r q = (some out, xs.length + 1) ∧
      Durability.Extends s.heap out.1.heap ∧
      Represents out.1.heap out.2 (xs ++ ys) ∧
      out.1.next = s.next + xs.length ∧
      advance xs.length out.1 out.2 = some q := by
  induction hx generalizing fuel with
  | nil =>
      exact ⟨(s, q), by simp [appendRunFuel], Durability.Extends.refl _, hy, by simp, rfl⟩
  | @cons a x r xs lookup _ _ ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          obtain ⟨out, run, ext, rep, count, shared⟩ := ih (by simpa using enough)
          refine ⟨allocate out.1 x out.2, ?_, ext.trans (allocate_extends _ _ _),
            allocate_represents rep x, ?_, ?_⟩
          · simp [appendRunFuel, lookup, run]
          · simp only [allocate_next, count, List.length_cons]
            omega
          · have kept := advance_mono (allocate_extends out.1 x out.2) shared
            simpa [advance, read, allocate_lookup] using kept

def appendRun (s : Store α) (r q : Root) :
    Resources.Measured (Option (Store α × Root)) Nat :=
  appendRunFuel s.next s r q

/-- The output preserves values and old roots, allocates exactly the left
length, and reaches the original right root after precisely that prefix. -/
theorem appendRun_correct {s : Store α} {r q : Root} {xs ys : List α}
    (hx : Represents s.heap r xs) (hy : Represents s.heap q ys) :
    ∃ out, appendRun s r q = (some out, xs.length + 1) ∧
      Durability.Extends s.heap out.1.heap ∧
      Represents out.1.heap out.2 (xs ++ ys) ∧
      out.1.next = s.next + xs.length ∧
      advance xs.length out.1 out.2 = some q :=
  appendRunFuel_correct hx hy hx.length_le_next

/-- A partial update specification; out-of-range replacement is a failure. -/
def updateValue (xs : List α) (i : Nat) (x : α) : Option (List α) :=
  if i < xs.length then some (xs.set i x) else none

def updateRunFuel : Nat → Store α → Root → Nat → α →
    Resources.Measured (Option (Store α × Root)) Nat
  | _, _, none, _, _ => (none, 1)
  | 0, _, some _, _, _ => (none, 0)
  | n + 1, s, some a, i, y =>
      match s.heap a with
      | none => (none, 1)
      | some (x, r) =>
          match i with
          | 0 => (some (allocate s y r), 1)
          | i + 1 =>
              let rest := updateRunFuel n s r i y
              (rest.1.map (fun out => allocate out.1 x out.2), rest.2 + 1)

theorem updateRunFuel_success {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) {fuel i : Nat} (enough : xs.length ≤ fuel)
    (inside : i < xs.length) (y : α) :
    ∃ out, updateRunFuel fuel s r i y = (some out, i + 1) ∧
      Durability.Extends s.heap out.1.heap ∧
      Represents out.1.heap out.2 (xs.set i y) ∧
      out.1.next = s.next + (i + 1) ∧
      advance (i + 1) out.1 out.2 = advance (i + 1) s r := by
  induction h generalizing fuel i with
  | nil => simp at inside
  | @cons a x r xs lookup below rest ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          cases i with
          | zero =>
              refine ⟨allocate s y r, ?_, allocate_extends _ _ _, ?_, rfl, ?_⟩
              · simp [updateRunFuel, lookup]
              · simpa only [List.set_cons_zero] using allocate_represents rest y
              · simp [advance, read, lookup, allocate_lookup]
          | succ i =>
              obtain ⟨out, run, ext, rep, count, shared⟩ :=
                ih (by simpa using enough) (by simpa using inside)
              refine ⟨allocate out.1 x out.2, ?_, ext.trans (allocate_extends _ _ _),
                ?_, ?_, ?_⟩
              · simp [updateRunFuel, lookup, run]
              · simpa only [List.set_cons_succ] using allocate_represents rep x
              · simp only [allocate_next, count]
                omega
              · obtain ⟨q, hq, _⟩ := advance_prefix rest (n := i + 1) (by
                  simp only [List.length_cons] at inside
                  omega)
                have kept := advance_mono (allocate_extends out.1 x out.2) (shared.trans hq)
                change advance ((i + 1) + 1) (allocate out.1 x out.2).1
                  (some out.1.next) = advance ((i + 1) + 1) s (some a)
                rw [advance_step (allocate_lookup out.1 x out.2), advance_step lookup]
                exact kept.trans hq.symm

theorem updateRunFuel_failure {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) {fuel i : Nat} (enough : xs.length ≤ fuel)
    (outside : xs.length ≤ i) (y : α) :
    updateRunFuel fuel s r i y = (none, xs.length + 1) := by
  induction h generalizing fuel i with
  | nil => simp [updateRunFuel]
  | @cons a x r xs lookup _ _ ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          cases i with
          | zero => simp at outside
          | succ i => simp [updateRunFuel, lookup, ih (by simpa using enough)
              (by simpa using outside)]

def updateRun (s : Store α) (r : Root) (i : Nat) (x : α) :
    Resources.Measured (Option (Store α × Root)) Nat :=
  updateRunFuel s.next s r i x

theorem updateRun_success {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) {i : Nat} (inside : i < xs.length) (x : α) :
    ∃ out, updateRun s r i x = (some out, i + 1) ∧
      Durability.Extends s.heap out.1.heap ∧
      Represents out.1.heap out.2 (xs.set i x) ∧
      out.1.next = s.next + (i + 1) ∧
      advance (i + 1) out.1 out.2 = advance (i + 1) s r :=
  updateRunFuel_success h h.length_le_next inside x

theorem updateRun_failure {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) {i : Nat} (outside : xs.length ≤ i) (x : α) :
    updateRun s r i x = (none, xs.length + 1) :=
  updateRunFuel_failure h h.length_le_next outside x

end Sequences.SharedList
