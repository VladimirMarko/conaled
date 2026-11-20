import Applications.Sequences.SharedList.Copy
import Applications.Sequences.SharedList.Suffixes
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# Reachable cells of immutable lists

Finite footprints use the existing heap graph and allocation frontier. A valid
list root reaches exactly as many distinct element cells as its observed list
has elements. Extending an immutable heap preserves every valid old footprint;
prepending allocates precisely a fresh interval and shares the tail footprint.

These are mathematical reachability observations. They do not implement a
collector, certify physical cell sizes, or say that unreachable cells have
actually been reclaimed. An application must state which roots are retained.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Sequences.SharedList

variable {α : Type}

@[simp] theorem not_reaches_none {heap : Durability.Heap (α × Root)} {a : Nat} :
    ¬ Reaches heap none a := by
  intro h
  cases h

theorem reaches_cons_iff {heap : Durability.Heap (α × Root)}
    {a b : Nat} {x : α} {r : Root} (lookup : heap b = some (x, r)) :
    Reaches heap (some b) a ↔ a = b ∨ Reaches heap r a := by
  constructor
  · intro h
    cases h with
    | here => exact Or.inl rfl
    | next lookup' tail =>
        have fields := Option.some.inj (lookup.symm.trans lookup')
        cases fields
        exact Or.inr tail
  · rintro (rfl | tail)
    · exact .here _
    · exact .next lookup tail

theorem Reaches.mono {a b : Durability.Heap (α × Root)}
    (extension : Durability.Extends a b) {r : Root} {i : Nat}
    (h : Reaches a r i) : Reaches b r i := by
  induction h with
  | here i => exact .here i
  | next lookup _ ih => exact .next (extension _ _ lookup) ih

theorem Represents.reaches_below {heap : Durability.Heap (α × Root)}
    {r : Root} {xs : List α} (h : Represents heap r xs) {a n : Nat}
    (below : Below r n) (reach : Reaches heap r a) : a < n := by
  induction h generalizing n a with
  | nil => exact False.elim (not_reaches_none reach)
  | cons lookup tailBelow _ ih =>
      rcases (reaches_cons_iff lookup).mp reach with rfl | tail
      · exact below
      · exact Nat.lt_trans (ih tailBelow tail) below

/-- A valid old chain cannot acquire additional reachable cells when other
addresses are added. No relation between the two frontiers is required. -/
theorem Represents.reaches_iff_of_extends {old new : Durability.Heap (α × Root)}
    {r : Root} {xs : List α} (h : Represents old r xs)
    (extension : Durability.Extends old new) (a : Nat) :
    Reaches new r a ↔ Reaches old r a := by
  induction h with
  | nil => simp
  | cons lookup _ _ ih =>
      rw [reaches_cons_iff (extension _ _ lookup), reaches_cons_iff lookup, ih]

/-- Following a chain to null enumerates exactly the cells reachable from its
initial root, even before the list-validity and distinctness laws are used. -/
theorem SuffixChain.reaches_iff {heap : Durability.Heap (α × Root)}
    {r : Root} {roots : List Root} (h : SuffixChain heap r roots) (a : Nat) :
    Reaches heap r a ↔ a ∈ roots.filterMap id := by
  induction h with
  | nil => simp
  | cons lookup _ ih =>
      rw [reaches_cons_iff lookup]
      simpa only [List.filterMap_cons, id_eq, List.mem_cons] using
        or_congr Iff.rfl ih

/-- Reachable addresses below the store frontier. For valid roots the bound
omits nothing. This noncomputable observer does not run a garbage collector. -/
noncomputable def liveCells (s : Store α) (roots : List Root) : Finset Nat := by
  classical
  exact (Finset.range s.next).filter (ReachableFrom s.heap roots)

@[simp] theorem mem_liveCells {s : Store α} {roots : List Root} {a : Nat} :
    a ∈ liveCells s roots ↔ a < s.next ∧ ReachableFrom s.heap roots a := by
  classical
  simp [liveCells]

theorem mem_liveCells_lt {s : Store α} {roots : List Root} {a : Nat}
    (h : a ∈ liveCells s roots) : a < s.next := (mem_liveCells.mp h).1

@[simp] theorem frontier_not_mem_liveCells (s : Store α) (roots : List Root) :
    s.next ∉ liveCells s roots := by
  intro h
  exact Nat.lt_irrefl _ (mem_liveCells_lt h)

@[simp] theorem reachableFrom_singleton {heap : Durability.Heap (α × Root)}
    {r : Root} {a : Nat} : ReachableFrom heap [r] a ↔ Reaches heap r a := by
  simp [ReachableFrom]

theorem reachableFrom_append {heap : Durability.Heap (α × Root)}
    (left right : List Root) (a : Nat) :
    ReachableFrom heap (left ++ right) a ↔
      ReachableFrom heap left a ∨ ReachableFrom heap right a := by
  simp [ReachableFrom, or_and_right, exists_or]

@[simp] theorem liveCells_nil (s : Store α) : liveCells s [] = ∅ := by
  ext a
  simp [ReachableFrom]

@[simp] theorem liveCells_none (s : Store α) : liveCells s [none] = ∅ := by
  ext a
  simp

/-- Retaining both collections keeps the union, so shared cells are counted
once, regardless of the order or multiplicity of the roots. -/
theorem liveCells_append (s : Store α) (left right : List Root) :
    liveCells s (left ++ right) = liveCells s left ∪ liveCells s right := by
  ext a
  simp only [mem_liveCells, reachableFrom_append, Finset.mem_union, and_or_left]

theorem liveCells_cons (s : Store α) (r : Root) (roots : List Root) :
    liveCells s (r :: roots) = liveCells s [r] ∪ liveCells s roots :=
  liveCells_append s [r] roots

theorem mem_liveCells_single {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) {a : Nat} :
    a ∈ liveCells s [r] ↔ Reaches s.heap r a := by
  rw [mem_liveCells, reachableFrom_singleton]
  exact ⟨And.right, fun reach => ⟨h.reaches_below h.below_next reach, reach⟩⟩

theorem liveCells_single_extends {s t : Store α}
    (extension : Durability.Extends s.heap t.heap) {r : Root} {xs : List α}
    (h : Represents s.heap r xs) : liveCells t [r] = liveCells s [r] := by
  ext a
  rw [mem_liveCells_single (h.mono extension), mem_liveCells_single h]
  exact h.reaches_iff_of_extends extension a

/-- List validity supplies finiteness, distinctness and an exact element-cell
count; payload values need not be distinct. -/
theorem liveCells_single_card {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) : (liveCells s [r]).card = xs.length := by
  obtain ⟨roots, run, _, _, cells, distinct, _⟩ := suffixesRun_correct h
  have chain : SuffixChain s.heap r roots :=
    suffixesRunFuel_chain (congrArg Prod.fst run)
  have footprint : liveCells s [r] = (roots.filterMap id).toFinset := by
    ext a
    rw [mem_liveCells_single h, List.mem_toFinset]
    exact chain.reaches_iff a
  rw [footprint, List.toFinset_card_of_nodup (nonnull_nodup distinct), cells]

theorem liveCells_allocate {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) (x : α) :
    liveCells (allocate s x r).1 [(allocate s x r).2] =
      insert s.next (liveCells s [r]) := by
  ext a
  rw [mem_liveCells_single (allocate_represents h x), allocate_root,
    reaches_cons_iff (allocate_lookup s x r), Finset.mem_insert,
    mem_liveCells_single h]
  exact or_congr Iff.rfl (h.reaches_iff_of_extends (allocate_extends s x r) a)

/-- An actually followed suffix link cannot introduce a new reachable cell.
This law requires successful traversal, but no list-validity hypothesis. -/
theorem Reaches.of_advance {s : Store α} {n : Nat} {r q : Root}
    (success : advance n s r = some q) {a : Nat} (h : Reaches s.heap q a) :
    Reaches s.heap r a := by
  induction n generalizing r with
  | zero =>
      have eq : r = q := Option.some.inj success
      simpa only [eq] using h
  | succ n ih =>
      cases r with
      | none => simp [advance, read] at success
      | some b =>
          cases lookup : s.heap b with
          | none => simp [advance, read, lookup] at success
          | some cell =>
              have tail : advance n s cell.2 = some q := by
                simpa [advance, read, lookup] using success
              exact .next lookup (ih tail)

theorem liveCells_advance_subset {s : Store α} {n : Nat} {r q : Root}
    (success : advance n s r = some q) : liveCells s [q] ⊆ liveCells s [r] := by
  intro a member
  rw [mem_liveCells, reachableFrom_singleton] at member ⊢
  exact ⟨member.1, member.2.of_advance success⟩

theorem liveCells_disjoint_fresh (s : Store α) (roots : List Root) (upper : Nat) :
    Disjoint (Finset.Ico s.next upper) (liveCells s roots) := by
  apply Finset.disjoint_left.mpr
  intro a fresh old
  have lower := (Finset.mem_Ico.mp fresh).1
  have below := mem_liveCells_lt old
  omega

/-- Exact footprint of path copying: every newly allocated address is used,
and the old suffix is shared by address, rather than copied. -/
theorem liveCells_prepend (pre : List α) {s : Store α} {r : Root} {ys : List α}
    (h : Represents s.heap r ys) :
    liveCells (prepend pre s r).1 [(prepend pre s r).2] =
      Finset.Ico s.next (s.next + pre.length) ∪ liveCells s [r] := by
  induction pre with
  | nil => simp [prepend]
  | cons x pre ih =>
      change liveCells (allocate (prepend pre s r).1 x (prepend pre s r).2).1
        [(allocate (prepend pre s r).1 x (prepend pre s r).2).2] = _
      rw [liveCells_allocate (prepend_correct pre h).2.1,
        ih, (prepend_correct pre h).2.2]
      ext a
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_Ico, List.length_cons]
      by_cases old : a ∈ liveCells s [r]
      · simp only [old, or_true]
      · simp only [old, or_false]
        omega

theorem liveCells_prepend_card (pre : List α) {s : Store α} {r : Root}
    {ys : List α} (h : Represents s.heap r ys) :
    (liveCells (prepend pre s r).1 [(prepend pre s r).2]).card =
      pre.length + ys.length := by
  simpa only [List.length_append] using
    liveCells_single_card (prepend_correct pre h).2.1

/-- If the shared suffix is already reachable from an old retained root, then
retaining that root keeps all of its cells as well as the copied prefix. -/
theorem liveCells_prepend_retained (pre : List α) {s : Store α} {r old : Root}
    {ys xs : List α} (tail : Represents s.heap r ys) (original : Represents s.heap old xs)
    (shared : liveCells s [r] ⊆ liveCells s [old]) :
    liveCells (prepend pre s r).1 [(prepend pre s r).2, old] =
      Finset.Ico s.next (s.next + pre.length) ∪ liveCells s [old] := by
  change liveCells (prepend pre s r).1 ([(prepend pre s r).2] ++ [old]) = _
  rw [liveCells_append, liveCells_prepend pre tail,
    liveCells_single_extends (prepend_correct pre tail).1 original,
    Finset.union_assoc, Finset.union_eq_right.mpr shared]

theorem liveCells_prepend_retained_card (pre : List α) {s : Store α}
    {r old : Root} {ys xs : List α}
    (tail : Represents s.heap r ys) (original : Represents s.heap old xs)
    (shared : liveCells s [r] ⊆ liveCells s [old]) :
    (liveCells (prepend pre s r).1 [(prepend pre s r).2, old]).card =
      pre.length + xs.length := by
  rw [liveCells_prepend_retained pre tail original shared,
    Finset.card_union_of_disjoint (liveCells_disjoint_fresh s [old] _),
    liveCells_single_card original]
  simp

end Sequences.SharedList
