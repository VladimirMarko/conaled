import Applications.Sequences.LCA.TreeEmission

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.LCA.TreeBackend
open Resources Dijkstra.Store

abbrev TourStore (m : Nat) := Store m (Nat × Nat)

def readPair (p : Nat × Nat) : Measured (Nat × Nat) Nat := (p, 2)
def writeTour {m : Nat} (mem : TourStore m) (i : Fin m) (p : Nat × Nat) :
    Measured (TourStore m) Nat := (write mem i p, 2)

def fillTourM : (m : Nat) → Measured (TourStore m) Nat
  | 0 => pure #v[]
  | m+1 => Resources.bind (fillTourM m) fun mem => (mem.push (0,0), 2)

theorem fillTourM_exact (m : Nat) : fillTourM m = (Vector.replicate m (0,0), 2*m) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [fillTourM, ih, Resources.bind, Vector.replicate_succ]; omega

def copyScan {m : Nat} : List (Nat × Nat) → Nat → TourStore m → TourStore m
  | [], _, mem => mem
  | p::ps, pos, mem =>
      copyScan ps (pos+1) (if h : pos < m then write mem ⟨pos,h⟩ p else mem)

def copyScanM {m : Nat} : List (Nat × Nat) → Nat → TourStore m → Measured (TourStore m) Nat
  | [], _, mem => pure mem
  | p::ps, pos, mem =>
      Resources.bind (readPair p) fun p =>
      Resources.bind (checkIndex pos m) fun valid =>
      Resources.bind (match valid with
        | some i => writeTour mem i p
        | none => pure mem) fun mem' =>
      Resources.bind (increment pos) fun pos' => copyScanM ps pos' mem'

theorem copyScanM_value {m : Nat} (xs : List (Nat × Nat)) (pos : Nat) (mem : TourStore m) :
    (copyScanM xs pos mem).1 = copyScan xs pos mem := by
  induction xs generalizing pos mem with
  | nil => rfl
  | cons p ps ih =>
    by_cases h : pos < m <;>
      simp [copyScanM, copyScan, readPair, writeTour, checkIndex, increment, h,
        Resources.bind, Resources.pure, ih]

theorem copyScanM_cost {m : Nat} (xs : List (Nat × Nat)) (pos : Nat) (mem : TourStore m) :
    (copyScanM xs pos mem).2 ≤ 6 * xs.length := by
  induction xs generalizing pos mem with
  | nil => simp [copyScanM, Resources.pure]
  | cons p ps ih =>
    by_cases h : pos < m
    · have hb := ih (pos+1) (write mem ⟨pos,h⟩ p)
      simp only [copyScanM, readPair, writeTour, checkIndex, increment, h,
        ↓reduceDIte, Resources.bind, List.length_cons]
      omega
    · have hb := ih (pos+1) mem
      simp only [copyScanM, readPair, checkIndex, increment, h,
        ↓reduceDIte, Resources.bind, Resources.pure, List.length_cons]
      omega

theorem copyScan_before {m : Nat} (xs : List (Nat × Nat)) (pos : Nat)
    (mem : TourStore m) (j : Fin m) (hj : j.val < pos) :
    lookup (copyScan xs pos mem) j = lookup mem j := by
  induction xs generalizing pos mem with
  | nil => rfl
  | cons p ps ih =>
    simp only [copyScan]
    rw [ih _ _ (by omega)]
    by_cases h : pos < m
    · have hne : (⟨pos,h⟩ : Fin m) ≠ j := by intro he; have hx : pos = j.val := congrArg Fin.val he; omega
      simp [h, lookup_write, hne]
    · simp [h]

theorem copyScan_at {m : Nat} (xs : List (Nat × Nat)) (pos : Nat)
    (mem : TourStore m) (i : Nat) (hi : i < xs.length) (hb : pos + xs.length ≤ m) :
    lookup (copyScan xs pos mem) ⟨pos+i, by omega⟩ = xs[i] := by
  induction xs generalizing pos mem i with
  | nil => simp at hi
  | cons p ps ih =>
    have hp : pos < m := by simp only [List.length_cons] at hb; omega
    simp only [copyScan, hp, ↓reduceDIte]
    cases i with
    | zero =>
      rw [copyScan_before _ _ _ _ (by simp)]
      simp [lookup_write]
    | succ i =>
      have hi' : i < ps.length := by simpa using hi
      have hb' : pos+1+ps.length ≤ m := by simp only [List.length_cons] at hb; omega
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using ih (pos+1) (write mem ⟨pos,hp⟩ p) i hi' hb'

/-- Fixed-size initialized output; every write is bounds-checked before its
    `Fin` address is passed to the store primitive. -/
def prepareTourM (m : Nat) (xs : List (Nat × Nat)) : Measured (TourStore m) Nat :=
  Resources.bind (fillTourM m) fun initial => copyScanM xs 0 initial

theorem prepareTourM_at (xs : List (Nat × Nat)) (i : Fin xs.length) :
    lookup (prepareTourM xs.length xs).1 i = xs[i.val] := by
  simp only [prepareTourM, Resources.bind, fillTourM_exact, copyScanM_value]
  simpa using copyScan_at xs 0 (Vector.replicate xs.length (0,0)) i.val i.isLt (by omega)

theorem prepareTourM_cost (m : Nat) (xs : List (Nat × Nat)) :
    (prepareTourM m xs).2 ≤ 2*m + 6*xs.length := by
  simp only [prepareTourM, Resources.bind, fillTourM_exact]
  have := copyScanM_cost xs 0 (Vector.replicate m (0,0))
  omega


/-- Read the identity field directly from each emitted pair. This avoids
    allocating an uncharged intermediate list of projected node identifiers. -/
def firstPairsM {n : Nat} (missing : Nat) :
    List (Nat × Nat) → Nat → Store n Nat → Measured (Store n Nat) Nat
  | [], _, mem => pure mem
  | p :: rest, pos, mem =>
      Resources.bind (readWord p.1) fun a =>
      Resources.bind (checkIndex a n) fun valid =>
      let update : Measured (Store n Nat) Nat :=
        match valid with
        | some i =>
          Resources.bind (readSlot mem i) fun old =>
          Resources.bind (compareWord old missing) fun unset =>
          if unset then writeSlot mem i pos else pure mem
        | none => pure mem
      Resources.bind update fun mem' =>
      Resources.bind (increment pos) fun pos' => firstPairsM missing rest pos' mem'

theorem firstPairsM_eq {n : Nat} (xs : List (Nat × Nat)) (missing pos : Nat) (mem : Store n Nat) :
    firstPairsM missing xs pos mem = firstScanM missing (xs.map Prod.fst) pos mem := by
  induction xs generalizing pos mem with
  | nil => rfl
  | cons p ps ih => simp only [firstPairsM, firstScanM, List.map_cons, Resources.bind, ih]; rfl

structure Maps (t : Tree) where
  first : Store t.size Nat
  tour : TourStore t.tour.length

/-- The same produced stream feeds the finite tour store and the first-position
    scan. No node-position map is recomputed recursively from the tree. -/
def prepareMapsM (t : Tree) : Measured (Maps t) Nat :=
  Resources.bind (prepareEmissionM t) fun raw =>
  Resources.bind (prepareTourM t.tour.length raw) fun tour =>
  Resources.bind (fillM t.tour.length t.size) fun initial =>
  Resources.bind (firstPairsM t.tour.length raw 0 initial) fun first =>
    pure ⟨first, tour⟩

theorem prepareEmissionM_raw (t : Tree) : (prepareEmissionM t).1 = t.cache.emit 0 0 [] := by
  simp [prepareEmissionM, Resources.bind, cacheM_value, emitM_value]

theorem raw_length (t : Tree) : (t.cache.emit 0 0 []).length = t.tour.length := by
  simp [Tree.emit_spec]

theorem prepareMapsM_first (t : Tree) (j : Fin t.size) :
    lookup (prepareMapsM t).1.first j = Tree.first (t.decode j) := by
  change lookup (firstPairsM t.tour.length (prepareEmissionM t).1 0 (fillM t.tour.length t.size).1).1 j = _
  rw [firstPairsM_eq, prepareEmissionM_raw]
  exact prepareFirstM_lookup t j

theorem prepareMapsM_tour (t : Tree) (i : Fin t.tour.length) :
    lookup (prepareMapsM t).1.tour i = (Tree.code (t.visit i.val), Tree.depth (t.visit i.val)) := by
  change lookup (prepareTourM t.tour.length (prepareEmissionM t).1).1 i = _
  rw [prepareEmissionM_raw]
  have hi : i.val < (t.cache.emit 0 0 []).length := by rw [raw_length]; exact i.isLt
  have hh := copyScan_at (t.cache.emit 0 0 []) 0
    (Vector.replicate t.tour.length (0,0)) i.val hi (by rw [raw_length]; omega)
  simp only [prepareTourM, Resources.bind, fillTourM_exact, copyScanM_value]
  have hf : (⟨0+i.val, by omega⟩ : Fin t.tour.length) = i := Fin.ext (Nat.zero_add _)
  rw [hf] at hh
  rw [hh]
  simp [Tree.emit_spec, Tree.tour_getElem]

theorem prepareMapsM_cost (t : Tree) :
    (prepareMapsM t).2 ≤ t.size + 25 * t.tour.length := by
  have hc := prepareEmissionM_cost t
  have he : t.cache.calls = t.tour.length := by
    have := Tree.cache_calls t
    have := Tree.tour_length t
    omega
  rw [he] at hc
  have ht := prepareTourM_cost t.tour.length (prepareEmissionM t).1
  have hf := firstScanM_cost ((prepareEmissionM t).1.map Prod.fst)
    t.tour.length 0 (Vector.replicate t.size t.tour.length)
  have hl : (prepareEmissionM t).1.length = t.tour.length := by rw [prepareEmissionM_raw, raw_length]
  simp only [List.length_map, hl] at ht hf
  simp only [prepareMapsM, Resources.bind, firstPairsM_eq, fillM_exact, Resources.pure]
  omega


structure Valid (t : Tree) (maps : Maps t) : Prop where
  first : ∀ j, lookup maps.first j = Tree.first (t.decode j)
  tour : ∀ i, lookup maps.tour i = (Tree.code (t.visit i.val), Tree.depth (t.visit i.val))

theorem prepareMapsM_valid (t : Tree) : Valid t (prepareMapsM t).1 :=
  ⟨prepareMapsM_first t, prepareMapsM_tour t⟩

/-- All retained words fit whenever the tour sentinel fits. This includes
    node identities, depths and initialized first-occurrence positions. -/
theorem prepared_word_bounds (t : Tree) (width : Nat) (hw : t.tour.length < 2 ^ width) :
    (∀ j : Fin t.size, lookup (prepareMapsM t).1.first j < 2 ^ width) ∧
    (∀ i : Fin t.tour.length,
      (lookup (prepareMapsM t).1.tour i).1 < 2 ^ width ∧
      (lookup (prepareMapsM t).1.tour i).2 < 2 ^ width) := by
  have hs : t.size ≤ t.tour.length := by have := Tree.size_pos t; have := Tree.tour_length t; omega
  constructor
  · intro j
    rw [prepareMapsM_first]
    exact Nat.lt_trans (Tree.first_lt _) hw
  · intro i
    rw [prepareMapsM_tour]
    have hc := Tree.code_lt (t.visit i.val)
    have hd := Tree.depth_lt_size (t.visit i.val)
    dsimp
    omega

/-- Finite representation size: one word for each node's first position and
    two words for each tour entry. -/
def retainedWords (t : Tree) : Nat := t.size + 2 * t.tour.length

theorem retained_linear (t : Tree) : retainedWords t + 2 = 5 * t.size := by
  have := Tree.tour_length t
  unfold retainedWords
  omega

/-- Query translation reads two already stored positions and orders them. -/
def translateM {t : Tree} (maps : Maps t) (a b : Fin t.size) : Measured (Nat × Nat) Nat :=
  Resources.bind (readSlot maps.first a) fun i =>
  Resources.bind (readSlot maps.first b) fun j =>
  Resources.bind ((decide (i ≤ j), 1) : Measured Bool Nat) fun ordered =>
    pure (if ordered then (i,j) else (j,i))

theorem translateM_exact {t : Tree} (maps : Maps t) (a b : Fin t.size) :
    translateM maps a b =
      ((min (lookup maps.first a) (lookup maps.first b),
        max (lookup maps.first a) (lookup maps.first b)), 3) := by
  simp only [translateM, readSlot, Resources.bind, Resources.pure]
  by_cases h : lookup maps.first a ≤ lookup maps.first b <;> simp [h, Nat.min_def, Nat.max_def]

theorem translate_prepared (t : Tree) (a b : Fin t.size) :
    (translateM (prepareMapsM t).1 a b).1 =
      (min (Tree.first (t.decode a)) (Tree.first (t.decode b)),
       max (Tree.first (t.decode a)) (Tree.first (t.decode b))) := by
  simp [translateM_exact, prepareMapsM_first]

/-- Recovery is one indexed field read; no path traversal or dictionary lookup
    is used during operation. -/
def recoverM {t : Tree} (maps : Maps t) (i : Fin t.tour.length) : Measured Nat Nat :=
  readWord (lookup maps.tour i).1

theorem recover_prepared (t : Tree) (a b : Fin t.size) (i : Fin t.tour.length)
    (hlo : min (Tree.first (t.decode a)) (Tree.first (t.decode b)) ≤ i.val)
    (hhi : i.val ≤ max (Tree.first (t.decode a)) (Tree.first (t.decode b)))
    (hmin : ∀ k, min (Tree.first (t.decode a)) (Tree.first (t.decode b)) ≤ k →
      k ≤ max (Tree.first (t.decode a)) (Tree.first (t.decode b)) →
      Tree.depth (t.visit i.val) ≤ Tree.depth (t.visit k)) :
    recoverM (prepareMapsM t).1 i = (Tree.code (Tree.lca (t.decode a) (t.decode b)), 1) := by
  simp only [recoverM, readWord, prepareMapsM_tour]
  rw [Tree.rmq_recovers_lca_sorted _ _ _ hlo hhi hmin]


theorem translate_valid {t : Tree} (maps : Maps t) (hv : Valid t maps) (a b : Fin t.size) :
    translateM maps a b =
      ((min (Tree.first (t.decode a)) (Tree.first (t.decode b)),
        max (Tree.first (t.decode a)) (Tree.first (t.decode b))), 3) := by
  rw [translateM_exact, hv.first, hv.first]

theorem recover_valid {t : Tree} (maps : Maps t) (hv : Valid t maps)
    (a b : Fin t.size) (i : Fin t.tour.length)
    (hlo : min (Tree.first (t.decode a)) (Tree.first (t.decode b)) ≤ i.val)
    (hhi : i.val ≤ max (Tree.first (t.decode a)) (Tree.first (t.decode b)))
    (hmin : ∀ k, min (Tree.first (t.decode a)) (Tree.first (t.decode b)) ≤ k →
      k ≤ max (Tree.first (t.decode a)) (Tree.first (t.decode b)) →
      Tree.depth (t.visit i.val) ≤ Tree.depth (t.visit k)) :
    recoverM maps i = (Tree.code (Tree.lca (t.decode a) (t.decode b)), 1) := by
  simp only [recoverM, readWord, hv.tour]
  rw [Tree.rmq_recovers_lca_sorted _ _ _ hlo hhi hmin]

end Sequences.LCA.TreeBackend
