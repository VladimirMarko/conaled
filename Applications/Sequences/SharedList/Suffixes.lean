import Applications.Sequences.SharedList.Basic
import Mathlib.Data.List.Infix

/-! Enumerating suffix roots does not copy any element cell. The result has
one root-list entry per suffix, including the empty suffix. Space below counts
abstract fixed-size cells, excluding payload size, allocator metadata and stack
space; no runtime sharing or garbage-collection claim follows. -/
set_option autoImplicit false
set_option warningAsError true

namespace Sequences.SharedList
variable {α : Type}

/-- Actual graph reachability, independent of the list observation. -/
inductive Reaches (heap : Durability.Heap (α × Root)) : Root → Nat → Prop
  | here (a : Nat) : Reaches heap (some a) a
  | next {a b : Nat} {x : α} {r : Root} :
      heap a = some (x, r) → Reaches heap r b → Reaches heap (some a) b

def ReachableFrom (heap : Durability.Heap (α × Root)) (roots : List Root)
    (a : Nat) : Prop := ∃ r ∈ roots, Reaches heap r a

/-- No tail reachable by one cell read is omitted from the root enumeration. -/
def ClosedRoots (heap : Durability.Heap (α × Root)) (roots : List Root) : Prop :=
  ∀ a x r, some a ∈ roots → heap a = some (x, r) → r ∈ roots

theorem Reaches.mem_closed {heap : Durability.Heap (α × Root)} {r : Root} {a : Nat}
    (h : Reaches heap r a) {roots : List Root} (closed : ClosedRoots heap roots)
    (member : r ∈ roots) : some a ∈ roots := by
  induction h generalizing roots with
  | here => exact member
  | next lookup _ ih => exact ih closed (closed _ _ _ member lookup)

theorem ClosedRoots.reachable_iff {heap : Durability.Heap (α × Root)}
    {roots : List Root} (closed : ClosedRoots heap roots) (a : Nat) :
    ReachableFrom heap roots a ↔ a ∈ roots.filterMap id := by
  constructor
  · rintro ⟨r, member, reachable⟩
    exact List.mem_filterMap.mpr ⟨some a, reachable.mem_closed closed member, rfl⟩
  · intro member
    obtain ⟨r, member, eq⟩ := List.mem_filterMap.mp member
    change r = some a at eq
    subst r
    exact ⟨some a, member, .here a⟩

/-- The roots are obtained by following the actual tail fields to null. -/
inductive SuffixChain (heap : Durability.Heap (α × Root)) : Root → List Root → Prop
  | nil : SuffixChain heap none [none]
  | cons {a : Nat} {x : α} {r : Root} {roots : List Root} :
      heap a = some (x, r) → SuffixChain heap r roots →
      SuffixChain heap (some a) (some a :: roots)

theorem SuffixChain.root_mem {heap : Durability.Heap (α × Root)}
    {r : Root} {roots : List Root} (h : SuffixChain heap r roots) : r ∈ roots := by
  cases h <;> simp

theorem SuffixChain.closed {heap : Durability.Heap (α × Root)}
    {r : Root} {roots : List Root} (h : SuffixChain heap r roots) :
    ClosedRoots heap roots := by
  induction h with
  | nil => intro a x r member; simp at member
  | @cons a x r roots lookup rest ih =>
      intro b y q member other
      rcases List.mem_cons.mp member with eq | member
      · have ba : b = a := Option.some.inj eq
        subst b
        have fields : (x, r) = (y, q) := Option.some.inj (lookup.symm.trans other)
        cases fields
        exact List.mem_cons_of_mem _ rest.root_mem
      · exact List.mem_cons_of_mem _ (ih _ _ _ member other)

def suffixesRunFuel : Nat → Store α → Root →
    Resources.Measured (Option (List Root)) Nat
  | _, _, none => (some [none], 1)
  | 0, _, some _ => (none, 0)
  | n + 1, s, some a =>
      match s.heap a with
      | none => (none, 1)
      | some (_, r) =>
          let rest := suffixesRunFuel n s r
          (rest.1.map (some a :: ·), rest.2 + 1)

theorem suffixesRunFuel_chain {s : Store α} {r : Root} {roots : List Root}
    {fuel : Nat} (success : (suffixesRunFuel fuel s r).1 = some roots) :
    SuffixChain s.heap r roots := by
  induction fuel generalizing r roots with
  | zero =>
      cases r with
      | none =>
          have eq : [none] = roots := by simpa [suffixesRunFuel] using success
          subst roots
          exact .nil
      | some a => simp [suffixesRunFuel] at success
  | succ fuel ih =>
      cases r with
      | none =>
          have eq : [none] = roots := by simpa [suffixesRunFuel] using success
          subst roots
          exact .nil
      | some a =>
          cases lookup : s.heap a with
          | none => simp [suffixesRunFuel, lookup] at success
          | some cell =>
              cases run : (suffixesRunFuel fuel s cell.2).1 with
              | none => simp [suffixesRunFuel, lookup, run] at success
              | some tails =>
                  have eq : some a :: tails = roots := by
                    simpa [suffixesRunFuel, lookup, run] using success
                  subst roots
                  exact .cons lookup (ih run)

theorem suffixesRunFuel_correct {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) {fuel bound : Nat}
    (enough : xs.length ≤ fuel) (below : Below r bound) :
    ∃ roots, suffixesRunFuel fuel s r = (some roots, xs.length + 1) ∧
      List.Forall₂ (Represents s.heap) roots xs.tails ∧
      roots.length = xs.length + 1 ∧
      (roots.filterMap id).length = xs.length ∧
      roots.Nodup ∧ (∀ q ∈ roots, Below q bound) := by
  induction h generalizing fuel bound with
  | nil =>
      refine ⟨[none], by simp [suffixesRunFuel], ?_, by simp, by simp, by simp, ?_⟩
      · exact .cons .nil .nil
      · intro q hq
        have eq : q = none := by simpa using hq
        subst q
        trivial
  | @cons a x r xs lookup tailBelow rest ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          obtain ⟨roots, run, observations, len, cells, distinct, bounded⟩ :=
            ih (by simpa using enough) tailBelow
          refine ⟨some a :: roots, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [suffixesRunFuel, lookup, run]
          · simpa only [List.tails_cons] using
              List.Forall₂.cons (.cons lookup tailBelow rest) observations
          · simp [len]
          · change (a :: roots.filterMap id).length = (x :: xs).length
            simp only [List.length_cons, cells]
          · apply List.nodup_cons.mpr
            refine ⟨?_, distinct⟩
            intro member
            exact Nat.lt_irrefl a (bounded (some a) member)
          · intro q member
            rcases List.mem_cons.mp member with eq | member
            · simpa [eq] using below
            · exact (bounded q member).mono (Nat.le_of_lt below)

def suffixesRun (s : Store α) (r : Root) :
    Resources.Measured (Option (List Root)) Nat := suffixesRunFuel s.next s r

/-- The successful traversal enumerates exactly the reachable element cells.
Distinctness is proved separately on valid inputs by `suffixesRun_correct`. -/
theorem suffixesRun_reachable {s : Store α} {r : Root} {roots : List Root}
    (success : (suffixesRun s r).1 = some roots) (a : Nat) :
    ReachableFrom s.heap roots a ↔ a ∈ roots.filterMap id :=
  (suffixesRunFuel_chain success).closed.reachable_iff a

theorem nonnull_nodup {roots : List Root} (distinct : roots.Nodup) :
    (roots.filterMap id).Nodup :=
  List.Nodup.filterMap (by
    intro a b x ha hb
    cases a <;> cases b <;> simp_all) distinct

/-- Root-entry count plus root-list length. Interpreting this as shared storage
requires the actual reachability theorem and non-null distinctness evidence. -/
def sharedSpace (roots : List Root) : Nat := (roots.filterMap id).length + roots.length

theorem suffixesRun_correct {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) :
    ∃ roots, suffixesRun s r = (some roots, xs.length + 1) ∧
      List.Forall₂ (Represents s.heap) roots xs.tails ∧
      roots.length = xs.length + 1 ∧
      (roots.filterMap id).length = xs.length ∧
      roots.Nodup ∧ sharedSpace roots = 2 * xs.length + 1 := by
  obtain ⟨roots, run, obs, len, cells, distinct, _⟩ :=
    suffixesRunFuel_correct h h.length_le_next h.below_next
  refine ⟨roots, run, obs, len, cells, distinct, ?_⟩
  simp only [sharedSpace, len, cells]
  omega

end Sequences.SharedList
