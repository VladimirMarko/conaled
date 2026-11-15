import Applications.Sequences.LCA.TreeMaps

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.LCA.TreeBackend

/-- Owned cached-node words: one leaf tag, or a count and two child pointers. -/
def cachedWords : Tree.Cached → Nat
  | .singleton => 1
  | .attach _ t c => 3 + cachedWords t + cachedWords c

theorem cachedWords_bound (t : Tree.Cached) : cachedWords t ≤ 3*t.calls := by
  induction t <;> simp_all [cachedWords, Tree.Cached.calls]; omega

theorem emit_length_cached (t : Tree.Cached) (base d : Nat) (tail : List (Nat × Nat)) :
    (t.emit base d tail).length = t.calls + tail.length := by
  induction t generalizing base d tail with
  | singleton => simp [Tree.Cached.emit, Tree.Cached.calls]; omega
  | attach n t c iht ihc => simp [Tree.Cached.emit, Tree.Cached.calls, iht, ihc]; omega

/-- Storage interpretation of the emitter's actual recursive evaluation.
    Four continuation words remain live while a recursive call executes. Output
    entries use two words; tail entries are shared, not copied. -/
def emitStorage : Tree.Cached → Nat → Nat → List (Nat × Nat) → List (Nat × Nat) × Nat
  | .singleton, base, d, tail =>
      let out := (base,d)::tail
      (out, 2*out.length + 4)
  | .attach _ t c, base, d, tail =>
      let child := emitStorage c (base+t.count) (d+1) ((base,d)::tail)
      let trunk := emitStorage t base d child.1
      (trunk.1, max (child.2+4) (trunk.2+4))

theorem emitStorage_value (t : Tree.Cached) (base d : Nat) (tail : List (Nat × Nat)) :
    (emitStorage t base d tail).1 = t.emit base d tail := by
  induction t generalizing base d tail with
  | singleton => rfl
  | attach n t c iht ihc => simp [emitStorage, Tree.Cached.emit, iht, ihc]

theorem emitStorage_bound (t : Tree.Cached) (base d : Nat) (tail : List (Nat × Nat)) :
    (emitStorage t base d tail).2 ≤ 2*tail.length + 6*t.calls := by
  induction t generalizing base d tail with
  | singleton => simp [emitStorage, Tree.Cached.calls]; omega
  | attach n t c iht ihc =>
    have ht := iht base d (emitStorage c (base+t.count) (d+1) ((base,d)::tail)).1
    have hc := ihc (base+t.count) (d+1) ((base,d)::tail)
    rw [emitStorage_value, emit_length_cached] at ht
    simp only [List.length_cons] at ht hc
    simp only [emitStorage, emitStorage_value, Tree.Cached.calls, Nat.max_le]
    constructor <;> omega

/-- Storage interpretation of count caching. The completed trunk remains live
    while the child is constructed; only one cached copy of each subtree exists. -/
def cacheStorage : Tree → Tree.Cached × Nat
  | .singleton => (.singleton, 5)
  | .attach t c =>
      let trunk := cacheStorage t
      let child := cacheStorage c
      let result := Tree.Cached.attach (trunk.1.count + child.1.count) trunk.1 child.1
      (result, max (trunk.2 + 4) (max (cachedWords trunk.1 + child.2 + 4) (cachedWords result + 4)))

theorem cacheStorage_value (t : Tree) : (cacheStorage t).1 = t.cache := by
  induction t <;> simp_all [cacheStorage, Tree.cache]

theorem cacheStorage_bound (t : Tree) : (cacheStorage t).2 ≤ 7*t.cache.calls := by
  induction t with
  | singleton => decide
  | attach t c iht ihc =>
    have hwt := cachedWords_bound t.cache
    have hwc := cachedWords_bound c.cache
    simp only [cacheStorage, cacheStorage_value, cachedWords, Tree.cache, Tree.Cached.calls, Nat.max_le]
    constructor
    · omega
    · constructor <;> omega

/-- Actual stage lifetimes. Caching releases its continuation frames before
    emission; cached nodes are released after emission. The raw stream remains
    live while the tour and first-position stores are initialized. Initialization
    reserves two frame words per unfinished slot. Copy/first scans are iterative
    target loops with eight scalar words, not growing recursive target stacks.

    The caller's borrowed source tree is excluded; composition must retain it
    separately when the caller still owns it. This describes the target storage
    interpretation, not Lean's allocator or native call stack. -/
def preparationPeak (t : Tree) : Nat :=
  let cached := cacheStorage t
  let emitted := emitStorage cached.1 0 0 []
  let m := emitted.1.length
  max cached.2
    (max (cachedWords cached.1 + emitted.2)
      (max (6*m + 8) (4*m + 3*t.size + 8)))

theorem preparationPeak_bound (t : Tree) : preparationPeak t ≤ 9*t.tour.length + 8 := by
  have hc := cacheStorage_bound t
  have hw := cachedWords_bound t.cache
  have he := emitStorage_bound t.cache 0 0 []
  have hcN : t.cache.calls = t.tour.length := by
    have := Tree.cache_calls t
    have := Tree.tour_length t
    omega
  have hs : t.size ≤ t.tour.length := by
    have := Tree.size_pos t
    have := Tree.tour_length t
    omega
  simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, hcN] at he
  rw [hcN] at hc hw
  simp only [preparationPeak, cacheStorage_value, emitStorage_value, emit_length_cached,
    List.length_nil, Nat.add_zero, hcN, Nat.max_le]
  constructor
  · omega
  · constructor
    · omega
    · constructor <;> omega

/-- Flat addressing and all stored words are representable under this explicit
    sufficient backend eligibility condition. Capacity is owned working memory;
    the source input's borrowed arena is a separate caller obligation. -/
def Eligible (t : Tree) (width capacity : Nat) : Prop :=
  9*t.tour.length + 8 ≤ capacity ∧ capacity < 2^width

instance (t : Tree) (width capacity : Nat) : Decidable (Eligible t width capacity) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem eligible_capacity (t : Tree) (width capacity : Nat) (h : Eligible t width capacity) :
    preparationPeak t ≤ capacity ∧ retainedWords t + 4 ≤ capacity := by
  have hs : t.size ≤ t.tour.length := by
    have := Tree.size_pos t
    have := Tree.tour_length t
    omega
  have hp := preparationPeak_bound t
  simp only [Eligible] at h
  unfold retainedWords
  omega

theorem eligible_words (t : Tree) (width capacity : Nat) (h : Eligible t width capacity) :
    (∀ j : Fin t.size, Dijkstra.Store.lookup (prepareMapsM t).1.first j < 2^width) ∧
    (∀ i : Fin t.tour.length,
      (Dijkstra.Store.lookup (prepareMapsM t).1.tour i).1 < 2^width ∧
      (Dijkstra.Store.lookup (prepareMapsM t).1.tour i).2 < 2^width) := by
  apply prepared_word_bounds
  simp only [Eligible] at h
  omega

/-- The operational primitives read the finite stores and return scalar
    registers; neither query translation nor recovery grows a store. -/
theorem query_work (t : Tree) (maps : Maps t) (a b : Fin t.size)
    (i : Fin t.tour.length) :
    (translateM maps a b).2 = 3 ∧ (recoverM maps i).2 = 1 := by
  simp [translateM_exact, recoverM, readWord]

end Sequences.LCA.TreeBackend
