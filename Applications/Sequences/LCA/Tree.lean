import Mathlib.Data.List.Basic
import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false
set_option warningAsError true

/-!
# Finite rooted trees and their Euler tour

`Tree.attach t c` adds `c` as the last child of the root of `t`. Repeated
attachment expresses arbitrary branching. Node identities distinguish all
occurrences even when their subtrees have identical shapes.
-/
namespace Applications.Sequences.LCA

inductive Tree where
  | singleton
  | attach (trunk child : Tree)
  deriving DecidableEq, Repr

namespace Tree

/-- A node occurrence, independent of any query or prepared representation. -/
inductive Node : Tree → Type where
  | root : Node .singleton
  | old {t c} : Node t → Node (.attach t c)
  | new {t c} : Node c → Node (.attach t c)

instance : (t : Tree) → DecidableEq (Node t)
  | .singleton => by intro a b; cases a; cases b; exact isTrue rfl
  | .attach t c => by
    letI := instDecidableEqNode t
    letI := instDecidableEqNode c
    intro a b
    cases a with
    | old a => cases b with
      | old b => exact decidable_of_iff (a = b) ⟨congrArg Node.old, Node.old.inj⟩
      | new b => exact isFalse (by intro h; cases h)
    | new a => cases b with
      | old b => exact isFalse (by intro h; cases h)
      | new b => exact decidable_of_iff (a = b) ⟨congrArg Node.new, Node.new.inj⟩

def root : (t : Tree) → Node t
  | .singleton => .root
  | .attach t _ => .old (root t)

def size : Tree → Nat
  | .singleton => 1
  | .attach t c => size t + size c

def depth : {t : Tree} → Node t → Nat
  | .singleton, .root => 0
  | .attach _ _, .old a => depth a
  | .attach _ _, .new a => depth a + 1

/-- Reflexive ancestry: an old node is above a new child precisely when it is
    the root. This does not use the LCA computation or Euler tour. -/
def Ancestor : {t : Tree} → Node t → Node t → Prop
  | .singleton, .root, .root => True
  | .attach _ _, .old a, .old b => Ancestor a b
  | .attach t _, .old a, .new _ => a = root t
  | .attach _ _, .new _, .old _ => False
  | .attach _ _, .new a, .new b => Ancestor a b

def lca : {t : Tree} → Node t → Node t → Node t
  | .singleton, .root, .root => .root
  | .attach _ _, .old a, .old b => .old (lca a b)
  | .attach t _, .old _, .new _ => .old (root t)
  | .attach t _, .new _, .old _ => .old (root t)
  | .attach _ _, .new a, .new b => .new (lca a b)

@[simp] theorem depth_root (t : Tree) : depth (root t) = 0 := by
  induction t <;> simp_all [root, depth]

@[simp] theorem depth_zero_iff {t : Tree} (a : Node t) : depth a = 0 ↔ a = root t := by
  induction t with
  | singleton => cases a; simp [depth, root]
  | attach t c iht ihc => cases a <;> simp_all [depth, root]

@[simp] theorem root_ancestor {t : Tree} (a : Node t) : Ancestor (root t) a := by
  induction t with
  | singleton => cases a; trivial
  | attach t c iht ihc => cases a <;> simp_all [root, Ancestor]

@[simp] theorem ancestor_refl {t : Tree} (a : Node t) : Ancestor a a := by
  induction t with
  | singleton => cases a; trivial
  | attach t c iht ihc => cases a <;> simp_all [Ancestor]

theorem ancestor_antisymm {t : Tree} {a b : Node t}
    (hab : Ancestor a b) (hba : Ancestor b a) : a = b := by
  induction t with
  | singleton => cases a; cases b; rfl
  | attach t c iht ihc =>
    cases a <;> cases b <;> simp_all [Ancestor]
    · exact iht hab hba
    · exact ihc hab hba

theorem ancestor_trans {t : Tree} {a b c : Node t}
    (hab : Ancestor a b) (hbc : Ancestor b c) : Ancestor a c := by
  induction t with
  | singleton => cases a; cases b; cases c; trivial
  | attach t s iht ihs =>
    cases a <;> cases b <;> cases c <;> simp_all [Ancestor]
    · exact iht hab hbc
    · exact ancestor_antisymm hab (root_ancestor _)
    · exact ihs hab hbc

/-- Independent universal property of the lowest common ancestor. -/
def IsLCA {t : Tree} (a b r : Node t) : Prop :=
  Ancestor r a ∧ Ancestor r b ∧ ∀ z, Ancestor z a → Ancestor z b → Ancestor z r

theorem lca_spec {t : Tree} (a b : Node t) : IsLCA a b (lca a b) := by
  induction t with
  | singleton => cases a; cases b; exact ⟨trivial, trivial, fun z _ _ => by cases z; trivial⟩
  | attach t c iht ihc =>
    cases a with
    | old a => cases b with
      | old b =>
        obtain ⟨ha, hb, hz⟩ := iht a b
        exact ⟨ha, hb, fun z => by cases z <;> simp_all [Ancestor, lca]⟩
      | new b =>
        refine ⟨root_ancestor a, rfl, ?_⟩
        intro z hza hzb
        cases z <;> simp_all [Ancestor, lca]
    | new a => cases b with
      | old b =>
        refine ⟨rfl, root_ancestor b, ?_⟩
        intro z hza hzb
        cases z <;> simp_all [Ancestor, lca]
      | new b =>
        obtain ⟨ha, hb, hz⟩ := ihc a b
        refine ⟨ha, hb, ?_⟩
        intro z hza hzb
        cases z <;> simp_all [Ancestor, lca]

theorem IsLCA.unique {t : Tree} {a b x y : Node t}
    (hx : IsLCA a b x) (hy : IsLCA a b y) : x = y :=
  ancestor_antisymm (hy.2.2 x hx.1 hx.2.1) (hx.2.2 y hy.1 hy.2.1)

theorem ancestor_depth {t : Tree} {a b : Node t} (h : Ancestor a b) : depth a ≤ depth b := by
  induction t with
  | singleton => cases a; cases b; exact Nat.le_refl _
  | attach t c iht ihc =>
    cases a <;> cases b <;> simp_all [Ancestor, depth]

theorem ancestor_eq_of_depth {t : Tree} {a b : Node t}
    (h : Ancestor a b) (hd : depth b ≤ depth a) : a = b := by
  induction t with
  | singleton => cases a; cases b; rfl
  | attach t c iht ihc =>
    cases a <;> cases b <;> simp_all [Ancestor, depth]
    · exact iht h hd
    · exact ihc h hd

/-- Depth-first traversal, recording a return to the root after each child. -/
def tour : (t : Tree) → List (Node t)
  | .singleton => [.root]
  | .attach t c => (tour t).map Node.old ++ (tour c).map Node.new ++ [.old (root t)]

theorem size_pos (t : Tree) : 0 < size t := by
  induction t <;> simp_all [size]; omega


theorem depth_lt_size {t : Tree} (a : Node t) : depth a < size t := by
  induction t with
  | singleton => cases a; simp [depth, size]
  | attach t c iht ihc =>
    cases a with
    | old a => have := iht a; have := size_pos c; simp only [depth, size]; omega
    | new a => have := ihc a; have := size_pos t; simp only [depth, size]; omega

theorem tour_length (t : Tree) : (tour t).length + 1 = 2 * size t := by
  induction t <;> simp_all [tour, size, List.length_append]; omega

/-- Executable first-occurrence map; its output is a tour index. -/
def first : {t : Tree} → Node t → Nat
  | .singleton, .root => 0
  | .attach _ _, .old a => first a
  | .attach t _, .new a => (tour t).length + first a


/-- Indexed execution of the same depth-first traversal. Values outside the
    tour are totalized to the root; all query theorems require valid bounds. -/
def visit : (t : Tree) → Nat → Node t
  | .singleton, _ => .root
  | .attach t c, i =>
      if i < (tour t).length then .old (visit t i)
      else if i < (tour t).length + (tour c).length then
        .new (visit c (i - (tour t).length))
      else .old (root t)

theorem first_lt {t : Tree} (a : Node t) : first a < (tour t).length := by
  induction t with
  | singleton => cases a; simp [first, tour]
  | attach t c iht ihc =>
    cases a with
    | old a => have := iht a; simp only [first, tour, List.length_append, List.length_map, List.length_singleton]; omega
    | new a => have := ihc a; simp only [first, tour, List.length_append, List.length_map, List.length_singleton]; omega

@[simp] theorem visit_first {t : Tree} (a : Node t) : visit t (first a) = a := by
  induction t with
  | singleton => cases a; rfl
  | attach t c iht ihc =>
    cases a with
    | old a => simp [first, visit, first_lt a, iht]
    | new a =>
      have h := first_lt a
      simp [first, visit, show ¬ (tour t).length + first a < (tour t).length by omega,
        show (tour t).length + first a < (tour t).length + (tour c).length by omega, ihc]

theorem tour_nonempty (t : Tree) : 0 < (tour t).length := by
  have := tour_length t
  have := size_pos t
  omega

@[simp] theorem visit_last (t : Tree) : visit t ((tour t).length - 1) = root t := by
  cases t with
  | singleton => rfl
  | attach t c =>
    simp only [tour, List.length_append, List.length_map, List.length_singleton]
    have he : (tour t).length + (tour c).length + 1 - 1 = (tour t).length + (tour c).length := by omega
    rw [he]
    simp [visit, root, show ¬ (tour t).length + (tour c).length < (tour t).length by omega]


@[simp] theorem first_root (t : Tree) : first (root t) = 0 := by
  induction t <;> simp_all [root, first]

/-- The position map selects the first visit, rather than merely some visit. -/
theorem first_visit_le (t : Tree) (i : Nat) : first (visit t i) ≤ i := by
  induction t generalizing i with
  | singleton => simp [visit, first]
  | attach t c iht ihc =>
    by_cases ht : i < (tour t).length
    · simpa [visit, ht, first] using iht i
    · by_cases hc : i < (tour t).length + (tour c).length
      · simp only [visit, ht, hc, ↓reduceIte, first]
        have := ihc (i - (tour t).length)
        omega
      · simp [visit, ht, hc, first]

theorem first_le_of_visit_eq {t : Tree} (a : Node t) (i : Nat)
    (h : visit t i = a) : first a ≤ i := by
  rw [← h]
  exact first_visit_le t i

/-- Every occurrence in the translated interval is below the independent LCA.
    The statement uses first-occurrence positions, not a supplied tour certificate. -/
theorem interval_ancestor {t : Tree} (a b : Node t) (i : Nat)
    (hlo : first a ≤ i) (hhi : i ≤ first b) :
    Ancestor (lca a b) (visit t i) := by
  induction t generalizing i with
  | singleton => cases a; cases b; trivial
  | attach t c iht ihc =>
    cases a with
    | old a => cases b with
      | old b =>
        have hi : i < (tour t).length := Nat.lt_of_le_of_lt hhi (first_lt b)
        simpa [visit, hi, lca, Ancestor] using iht a b i hlo hhi
      | new b =>
        change Ancestor (root (.attach t c)) _
        exact root_ancestor _
    | new a => cases b with
      | old b =>
        have ha := first_lt a
        have hb := first_lt b
        simp only [first] at hlo hhi
        omega
      | new b =>
        have ha := first_lt a
        have hb := first_lt b
        simp only [first] at hlo hhi
        have hi₁ : ¬ i < (tour t).length := by omega
        have hi₂ : i < (tour t).length + (tour c).length := by omega
        simp only [visit, hi₁, ↓reduceIte, hi₂, lca, Ancestor]
        exact ihc a b _ (by omega) (by omega)

/-- The interval actually visits the LCA, so the ancestry bound is attained. -/
theorem interval_witness {t : Tree} (a b : Node t) (h : first a ≤ first b) :
    ∃ i, first a ≤ i ∧ i ≤ first b ∧ visit t i = lca a b := by
  induction t with
  | singleton => cases a; cases b; exact ⟨0, Nat.le_refl _, Nat.le_refl _, rfl⟩
  | attach t c iht ihc =>
    cases a with
    | old a => cases b with
      | old b =>
        obtain ⟨i, hlo, hhi, hv⟩ := iht a b h
        have hi : i < (tour t).length := Nat.lt_of_le_of_lt hhi (first_lt b)
        exact ⟨i, hlo, hhi, by simp [visit, hi, lca, hv]⟩
      | new b =>
        have ha := first_lt a
        have ht := tour_nonempty t
        refine ⟨(tour t).length - 1, ?_, ?_, ?_⟩
        · simp only [first]; omega
        · simp only [first]; omega
        · simp [visit, show (tour t).length - 1 < (tour t).length by omega, lca]
    | new a => cases b with
      | old b =>
        have hb := first_lt b
        simp only [first] at h
        omega
      | new b =>
        obtain ⟨i, hlo, hhi, hv⟩ := ihc a b (by simpa [first] using h)
        have hi := Nat.lt_of_le_of_lt hhi (first_lt b)
        refine ⟨(tour t).length + i, by simpa [first], by simpa [first], ?_⟩
        simp [visit, show ¬ (tour t).length + i < (tour t).length by omega,
          show (tour t).length + i < (tour t).length + (tour c).length by omega, hv, lca]

/-- Any minimum-depth position recovers the unique LCA. Equal-depth minima
    can use any consistent index tie policy: their recovered node is identical. -/
theorem rmq_recovers_lca {t : Tree} (a b : Node t) (k : Nat)
    (hlo : first a ≤ k) (hhi : k ≤ first b)
    (hmin : ∀ i, first a ≤ i → i ≤ first b → depth (visit t k) ≤ depth (visit t i)) :
    visit t k = lca a b := by
  obtain ⟨i, hi₁, hi₂, hv⟩ := interval_witness a b (Nat.le_trans hlo hhi)
  apply Eq.symm
  apply ancestor_eq_of_depth (interval_ancestor a b k hlo hhi)
  simpa [hv] using hmin i hi₁ hi₂



theorem lca_comm {t : Tree} (a b : Node t) : lca a b = lca b a := by
  have h := lca_spec b a
  exact (lca_spec a b).unique ⟨h.2.1, h.1, fun z ha hb => h.2.2 z hb ha⟩

/-- Query order is unrestricted; sorting the two first-occurrence indices is
    part of the constant-size query translation. -/
theorem rmq_recovers_lca_sorted {t : Tree} (a b : Node t) (k : Nat)
    (hlo : min (first a) (first b) ≤ k) (hhi : k ≤ max (first a) (first b))
    (hmin : ∀ i, min (first a) (first b) ≤ i → i ≤ max (first a) (first b) →
      depth (visit t k) ≤ depth (visit t i)) : visit t k = lca a b := by
  by_cases h : first a ≤ first b
  · simp only [Nat.min_eq_left h, Nat.max_eq_right h] at hlo hhi hmin
    exact rmq_recovers_lca a b k hlo hhi hmin
  · have h' : first b ≤ first a := by omega
    simp only [Nat.min_eq_right h', Nat.max_eq_left h'] at hlo hhi hmin
    rw [lca_comm a b]
    exact rmq_recovers_lca b a k hlo hhi hmin

@[simp] theorem visit_zero (t : Tree) : visit t 0 = root t := by
  induction t with
  | singleton => rfl
  | attach t c iht ihc => simp [visit, tour_nonempty t, iht, root]

/-- The indexed traversal reads the materialized Euler list. -/
theorem tour_getElem (t : Tree) (i : Nat) (h : i < (tour t).length) :
    (tour t)[i] = visit t i := by
  induction t generalizing i with
  | singleton =>
    have : i = 0 := by simpa [tour] using h
    subst i
    rfl
  | attach t c iht ihc =>
    by_cases ht : i < (tour t).length
    · simp only [tour, List.append_assoc]
      rw [List.getElem_append_left (by simpa using ht), List.getElem_map, iht]
      simp [visit, ht]
    · by_cases hc : i < (tour t).length + (tour c).length
      · simp only [tour, List.append_assoc]
        rw [List.getElem_append_right (by simp; omega)]
        rw [List.getElem_append_left (by simp; omega), List.getElem_map, ihc]
        simp [visit, ht, hc]
      · have hi : i = (tour t).length + (tour c).length := by
          simp only [tour, List.length_append, List.length_map, List.length_singleton] at h
          omega
        subst i
        simp [tour, visit, ht, hc, List.getElem_append_right]

/-- Every adjacent pair of depths differs by exactly one. -/
theorem adjacent_depth (t : Tree) (i : Nat) (h : i + 1 < (tour t).length) :
    depth (visit t (i + 1)) = depth (visit t i) + 1 ∨
    depth (visit t i) = depth (visit t (i + 1)) + 1 := by
  induction t generalizing i with
  | singleton => simp [tour] at h
  | attach t c iht ihc =>
    have ht := tour_nonempty t
    have hc := tour_nonempty c
    simp only [tour, List.length_append, List.length_map, List.length_singleton] at h
    by_cases hleft : i + 1 < (tour t).length
    · simpa [visit, hleft, show i < (tour t).length by omega, depth] using iht i hleft
    · by_cases hboundary : i + 1 = (tour t).length
      · have hi : i = (tour t).length - 1 := by omega
        left
        rw [hboundary]
        simp only [visit, Nat.lt_irrefl, ↓reduceIte,
          show (tour t).length < (tour t).length + (tour c).length by omega,
          show i < (tour t).length by omega, Nat.sub_self, visit_zero, depth, depth_root]
        rw [hi, visit_last, depth_root]
      · by_cases hmiddle : i + 1 < (tour t).length + (tour c).length
        · have hle : ¬ i < (tour t).length := by omega
          have he : i + 1 - (tour t).length = (i - (tour t).length) + 1 := by omega
          have hm : i < (tour t).length + (tour c).length := by omega
          have ih := ihc (i - (tour t).length) (by omega)
          simp only [visit, hleft, hle, hmiddle, hm, ↓reduceIte, depth, he]
          omega
        · have he : i + 1 = (tour t).length + (tour c).length := by omega
          have hi : i - (tour t).length = (tour c).length - 1 := by omega
          right
          simp [visit, hleft, hmiddle, show ¬ i < (tour t).length by omega,
            show i < (tour t).length + (tour c).length by omega, hi, depth]

/-- Dense identifiers for the node occurrences. No comparison or hash lookup
    is needed to use a prepared table indexed by this identifier. -/
def code : {t : Tree} → Node t → Nat
  | .singleton, .root => 0
  | .attach _ _, .old a => code a
  | .attach t _, .new a => size t + code a

theorem code_lt {t : Tree} (a : Node t) : code a < size t := by
  induction t with
  | singleton => cases a; simp [code, size]
  | attach t c iht ihc =>
    cases a with
    | old a => have := iht a; have := size_pos c; simp only [code, size]; omega
    | new a => have := ihc a; simp only [code, size]; omega

def encode {t : Tree} (a : Node t) : Fin (size t) := ⟨code a, code_lt a⟩

@[simp] theorem encode_old {t c : Tree} (a : Node t) :
    encode (Node.old (c := c) a) = (encode a).castAdd (size c) := rfl

@[simp] theorem encode_new {t c : Tree} (a : Node c) :
    encode (Node.new (t := t) a) = Fin.natAdd (size t) (encode a) := rfl

def decode : (t : Tree) → Fin (size t) → Node t
  | .singleton, _ => .root
  | .attach t c, i => if h : i.val < size t then .old (decode t ⟨i.val, h⟩)
      else .new (decode c ⟨i.val - size t, by have := i.isLt; simp only [size] at this; omega⟩)

@[simp] theorem decode_encode {t : Tree} (a : Node t) : decode t (encode a) = a := by
  induction t with
  | singleton => cases a; rfl
  | attach t c iht ihc => cases a with
    | old a => simp [encode_old, decode, (encode a).isLt, iht]
    | new a => simp [encode_new, decode, show ¬ size t + (encode a).val < size t by omega, ihc]

@[simp] theorem encode_decode (t : Tree) (i : Fin (size t)) : encode (decode t i) = i := by
  induction t with
  | singleton => apply Fin.ext; have := i.isLt; simp [size] at this; simp [decode, encode, code]; omega
  | attach t c iht ihc =>
    refine Fin.addCases (motive := fun i => encode (decode (.attach t c) i) = i) ?_ ?_ i
    · intro j; simp [decode, j.isLt, iht]; rfl
    · intro j; simp [decode, show ¬ size t + j.val < size t by omega, ihc]; rfl


/-- The node domain is finite and has exactly `size t` distinct identities. -/
def nodeEquiv (t : Tree) : Node t ≃ Fin (size t) where
  toFun := encode
  invFun := decode t
  left_inv := decode_encode
  right_inv := encode_decode t

/-- Preprocessing materializes both directions of the reduction as indexed lists.
    Costs of executing this reference construction are separate from the
    semantic reduction and must be refined by the selected target backend. -/
def firstTable (t : Tree) : List Nat := List.ofFn (fun i : Fin (size t) => first (decode t i))
def identityTable (t : Tree) : List (Fin (size t)) := (tour t).map encode
def depthTable (t : Tree) : List Nat := (tour t).map depth

@[simp] theorem firstTable_getElem (t : Tree) (i : Fin (size t)) :
    (firstTable t)[i.val]'(by simp [firstTable]) = first (decode t i) := by
  simp [firstTable]

theorem identityTable_getElem (t : Tree) (i : Nat) (h : i < (tour t).length) :
    (identityTable t)[i]'(by simpa [identityTable] using h) = encode (visit t i) := by
  simp [identityTable, tour_getElem t i h]

theorem depthTable_getElem (t : Tree) (i : Nat) (h : i < (tour t).length) :
    (depthTable t)[i]'(by simpa [depthTable] using h) = depth (visit t i) := by
  simp [depthTable, tour_getElem t i h]


@[simp] theorem code_root (t : Tree) : code (root t) = 0 := by
  induction t <;> simp_all [root, code]

/-- A preprocessing pass caches subtree sizes. Each constructor stores a single
    count; the emitter reads it without traversing that subtree again. -/
inductive Cached where
  | singleton
  | attach (count : Nat) (trunk child : Cached)
  deriving Repr

namespace Cached

def count : Cached → Nat
  | .singleton => 1
  | .attach n _ _ => n

def erase : Cached → Tree
  | .singleton => .singleton
  | .attach _ t c => .attach (erase t) (erase c)

/-- Difference-list emitter. Each recursive call emits exactly one tour entry;
    there is no append, map, dictionary search, or recursive count computation. -/
def emit : Cached → Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | .singleton, base, d, tail => (base, d) :: tail
  | .attach _ t c, base, d, tail =>
      emit t base d (emit c (base + count t) (d + 1) ((base, d) :: tail))

/-- The number of recursive dispatches in `emit`, and of allocated cache nodes.
    This follows the actual control flow rather than a desired asymptotic tariff. -/
def calls : Cached → Nat
  | .singleton => 1
  | .attach _ t c => 1 + calls t + calls c

end Cached

def cache : Tree → Cached
  | .singleton => .singleton
  | .attach t c =>
      let ct := cache t
      let cc := cache c
      .attach (ct.count + cc.count) ct cc

@[simp] theorem cache_count (t : Tree) : (cache t).count = size t := by
  induction t <;> simp_all [cache, Cached.count, size]

@[simp] theorem cache_erase (t : Tree) : (cache t).erase = t := by
  induction t <;> simp_all [cache, Cached.erase]

theorem cache_calls (t : Tree) : (cache t).calls + 1 = 2 * size t := by
  induction t <;> simp_all [cache, Cached.calls, size]; omega

/-- The efficient emitter refines the independently defined Euler list, including
    dense node identity and depth, for every initial offset and continuation. -/
theorem emit_spec (t : Tree) (base d : Nat) (tail : List (Nat × Nat)) :
    (cache t).emit base d tail =
      (tour t).map (fun a => (base + code a, d + depth a)) ++ tail := by
  induction t generalizing base d tail with
  | singleton => simp [cache, Cached.emit, tour, code, depth]
  | attach t c iht ihc =>
    simp only [cache, Cached.emit, cache_count]
    rw [iht, ihc]
    simp only [tour, List.map_append, List.map_map, List.map_cons, List.map_nil,
      code, depth, code_root, depth_root, Nat.add_zero, List.append_assoc]
    congr 1
    congr 1
    apply List.map_congr_left
    intro a ha
    simp only [Function.comp_apply, code, depth]
    congr 1 <;> omega

/-- There is exactly one emitted entry for each dispatch of the cached emitter. -/
theorem emit_length (t : Tree) (base d : Nat) (tail : List (Nat × Nat)) :
    ((cache t).emit base d tail).length = (cache t).calls + tail.length := by
  rw [emit_spec, List.length_append, List.length_map]
  have := cache_calls t
  have := tour_length t
  omega


/-- Emitted words fit the symbolic node/depth bounds. The backend can discharge
    finite word-width obligations from these inequalities. -/
theorem emit_entry_bounds (t : Tree) (base d : Nat) (x : Nat × Nat)
    (h : x ∈ (cache t).emit base d []) :
    base ≤ x.1 ∧ x.1 < base + size t ∧ d ≤ x.2 ∧ x.2 < d + size t := by
  rw [emit_spec] at h
  simp only [List.append_nil, List.mem_map] at h
  obtain ⟨a, _, rfl⟩ := h
  have := code_lt a
  have := depth_lt_size a
  dsimp
  omega

end Tree
end Applications.Sequences.LCA
