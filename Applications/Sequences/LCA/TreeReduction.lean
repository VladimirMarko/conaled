import Applications.Sequences.LCA.TreeStorage
import Applications.Resources.Prepared
import Applications.Sequences.LCA.Micro

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.LCA.TreeReduction
open Resources Resources.Prepared Dijkstra.Store TreeBackend

abbrev Source (n : Nat) := {t : Tree // t.size = n}
abbrev Query (n : Nat) := Fin n × Fin n

def tourSize (n : Nat) := 2*n-1

theorem source_length {n : Nat} (s : Source n) : s.val.tour.length = tourSize n := by
  have := Tree.tour_length s.val
  have := Tree.size_pos s.val
  rw [s.property] at *
  unfold tourSize
  omega

/-- The decoder retains only finite stores, not a runtime copy of the source
    tree. Reindexing by proven equal sizes changes no stored word. -/
structure Decoder (n : Nat) where
  first : Store n Nat
  tour : TourStore (tourSize n)

def reindex {n : Nat} (s : Source n) (maps : Maps s.val) : Decoder n :=
  ⟨maps.first.cast s.property, maps.tour.cast (source_length s)⟩

theorem reindex_first {n : Nat} (s : Source n) (maps : Maps s.val)
    (h : Valid s.val maps) (j : Fin n) :
    lookup (reindex s maps).first j = Tree.first (s.val.decode (Fin.cast s.property.symm j)) := by
  simp only [reindex, lookup, Vector.getElem_cast]
  exact h.first (Fin.cast s.property.symm j)

theorem reindex_tour {n : Nat} (s : Source n) (maps : Maps s.val)
    (h : Valid s.val maps) (i : Fin (tourSize n)) :
    lookup (reindex s maps).tour i = (Tree.code (s.val.visit i.val), Tree.depth (s.val.visit i.val)) := by
  simp only [reindex, lookup, Vector.getElem_cast]
  exact h.tour (Fin.cast (source_length s).symm i)

/-- Target inputs are actual finite Euler-depth stores with the proven ±1
    admission condition. Ordinary malformed arrays are not silently accepted. -/
structure Input (m : Nat) where
  cells : TourStore m
  positive : 0 < m
  bounded : ∀ i : Fin m, (lookup cells i).2 < m
  identityBound : ∀ i : Fin m, (lookup cells i).1 < m
  unit : ∀ i (hi : i+1 < m),
    (lookup cells ⟨i+1,hi⟩).2 = (lookup cells ⟨i,by omega⟩).2 + 1 ∨
    (lookup cells ⟨i,by omega⟩).2 = (lookup cells ⟨i+1,hi⟩).2 + 1

def Input.depth {m : Nat} (input : Input m) (i : Nat) : Nat :=
  if hi : i < m then (lookup input.cells ⟨i,hi⟩).2 else 0

def toInput {n : Nat} (s : Source n) (maps : Maps s.val) (hv : Valid s.val maps) : Input (tourSize n) where
  cells := (reindex s maps).tour
  positive := by rw [← source_length s]; exact Tree.tour_nonempty s.val
  bounded i := by
    rw [reindex_tour s maps hv]
    have hd := Tree.depth_lt_size (s.val.visit i.val)
    have hs := Tree.size_pos s.val
    have ht := Tree.tour_length s.val
    have hl := source_length s
    dsimp
    omega
  identityBound i := by
    rw [reindex_tour s maps hv]
    have hc := Tree.code_lt (s.val.visit i.val)
    have hs := Tree.size_pos s.val
    have ht := Tree.tour_length s.val
    have hl := source_length s
    dsimp
    omega
  unit i hi := by
    rw [reindex_tour s maps hv, reindex_tour s maps hv]
    exact Tree.adjacent_depth s.val i (by rw [source_length s]; exact hi)

theorem input_depth {n : Nat} (s : Source n) (maps : Maps s.val) (hv : Valid s.val maps)
    (i : Nat) (hi : i < tourSize n) :
    (toInput s maps hv).depth i = Tree.depth (s.val.visit i) := by
  simp only [Input.depth, hi, ↓reduceDIte, toInput, reindex_tour s maps hv]

/-- Inclusive RMQ semantics. The selected minimum may use any fixed tie policy;
    the Euler reduction proves that every minimum recovers the same LCA node. -/
def RMQCorrect {m : Nat} (g : Input m → (Nat × Nat) → Nat) : Prop :=
  ∀ input lo hi, lo ≤ hi → hi < m →
    let k := g input (lo,hi)
    lo ≤ k ∧ k ≤ hi ∧ ∀ j, lo ≤ j → j ≤ hi → input.depth k ≤ input.depth j


/-- Independent executable target specification, choosing the leftmost minimum. -/
def rmqSpec {m : Nat} (input : Input m) (q : Nat × Nat) : Nat :=
  argmin (fun i => (input.depth i : Int)) q.1 (q.2-q.1)

theorem rmqSpec_correct (m : Nat) : RMQCorrect (@rmqSpec m) := by
  intro input lo hi hlo _
  have h := argmin_correct (fun i => (input.depth i : Int)) lo (hi-lo)
  have he : lo + (hi-lo) = hi := by omega
  rw [he] at h
  refine ⟨h.1, h.2.1, ?_⟩
  intro j hjl hjh
  have hm := (h.2.2 j hjl hjh).1
  change (input.depth (rmqSpec input (lo,hi)) : Int) ≤ (input.depth j : Int) at hm
  omega

def sourceLCA {n : Nat} (s : Source n) (q : Query n) : Nat :=
  Tree.code (Tree.lca (s.val.decode (Fin.cast s.property.symm q.1))
    (s.val.decode (Fin.cast s.property.symm q.2)))


theorem sourceLCA_lt {n : Nat} (s : Source n) (q : Query n) : sourceLCA s q < n := by
  have := Tree.code_lt (Tree.lca (s.val.decode (Fin.cast s.property.symm q.1))
    (s.val.decode (Fin.cast s.property.symm q.2)))
  simpa [sourceLCA, s.property] using this

def convertM {n : Nat} (s : Source n) : Measured (Decoder n × Input (tourSize n)) Nat :=
  let run := prepareMapsM s.val
  ((reindex s run.1, toInput s run.1 (prepareMapsM_valid s.val)), run.2)

def encodeM {n : Nat} (decoder : Decoder n) (q : Query n) : Measured (Nat × Nat) Nat :=
  Resources.bind (readSlot decoder.first q.1) fun i =>
  Resources.bind (readSlot decoder.first q.2) fun j =>
  Resources.bind ((decide (i ≤ j),1) : Measured Bool Nat) fun ordered =>
    pure (if ordered then (i,j) else (j,i))

/-- The checked address handles arbitrary backend replies; correctness below
    proves that admitted RMQ replies always take the successful branch. -/
def decodeM {n : Nat} (decoder : Decoder n) (i : Nat) : Measured Nat Nat :=
  Resources.bind (checkIndex i (tourSize n)) fun address =>
    match address with
    | some j => readWord (lookup decoder.tour j).1
    | none => pure 0

def reduction (n : Nat) : Reduction (Source n) (Query n) Nat
    (Input (tourSize n)) (Nat × Nat) Nat (Decoder n) where
  convert := convertM
  encode := encodeM
  decode := decodeM

theorem encodeM_exact {n : Nat} (decoder : Decoder n) (q : Query n) :
    encodeM decoder q =
      ((min (lookup decoder.first q.1) (lookup decoder.first q.2),
        max (lookup decoder.first q.1) (lookup decoder.first q.2)),3) := by
  simp only [encodeM, readSlot, Resources.bind, Resources.pure]
  by_cases h : lookup decoder.first q.1 ≤ lookup decoder.first q.2 <;>
    simp [h, Nat.min_def, Nat.max_def]

theorem decodeM_at {n : Nat} (decoder : Decoder n) (i : Nat) (hi : i < tourSize n) :
    decodeM decoder i = ((lookup decoder.tour ⟨i,hi⟩).1,2) := by
  simp [decodeM, checkIndex, hi, Resources.bind, readWord]

theorem decodeM_cost {n : Nat} (decoder : Decoder n) (i : Nat) : (decodeM decoder i).2 ≤ 2 := by
  by_cases hi : i < tourSize n <;>
    simp [decodeM, checkIndex, hi, Resources.bind, readWord, Resources.pure]

theorem translation {n : Nat} (g : Input (tourSize n) → (Nat × Nat) → Nat)
    (hg : RMQCorrect g) (s : Source n) (q : Query n) :
    ((reduction n).decode ((reduction n).convert s).1.1
      (g ((reduction n).convert s).1.2
        ((reduction n).encode ((reduction n).convert s).1.1 q).1)).1 = sourceLCA s q := by
  let maps := (prepareMapsM s.val).1
  have hv : Valid s.val maps := prepareMapsM_valid s.val
  let a := s.val.decode (Fin.cast s.property.symm q.1)
  let b := s.val.decode (Fin.cast s.property.symm q.2)
  have ha : Tree.first a < tourSize n := by rw [← source_length s]; exact Tree.first_lt a
  have hb : Tree.first b < tourSize n := by rw [← source_length s]; exact Tree.first_lt b
  have he : (encodeM (reindex s maps) q).1 = (min (Tree.first a) (Tree.first b), max (Tree.first a) (Tree.first b)) := by
    simp [encodeM_exact, reindex_first s maps hv, a, b]
  change (decodeM (reindex s maps) (g (toInput s maps hv) (encodeM (reindex s maps) q).1)).1 = _
  rw [he]
  obtain ⟨hlo,hhi,hmin⟩ := hg (toInput s maps hv) (min (Tree.first a) (Tree.first b))
    (max (Tree.first a) (Tree.first b)) (by omega) (by omega)
  have hk := Nat.lt_of_le_of_lt hhi (show max (Tree.first a) (Tree.first b) < tourSize n by omega)
  rw [decodeM_at _ _ hk]
  simp only [reindex_tour s maps hv]
  change Tree.code (s.val.visit _) = Tree.code (Tree.lca a b)
  congr 1
  apply Tree.rmq_recovers_lca_sorted a b _ hlo hhi
  intro j hjl hjh
  have hj : j < tourSize n := by omega
  have hm := hmin j hjl hjh
  rw [input_depth s maps hv _ hk, input_depth s maps hv j hj] at hm
  exact hm

/-- A backend supplies its own RMQ law; the shared reduction composes it with
    the independently proved tree semantics and operational map construction. -/
theorem laws {n : Nat} {R : Type} (g : Input (tourSize n) → (Nat × Nat) → Nat)
    (hg : RMQCorrect g) (p : Ops (Input (tourSize n)) (Nat × Nat) Nat R)
    (V : Input (tourSize n) → R → Prop) (hp : Laws g p V) :
    Laws sourceLCA ((reduction n).apply p) ((reduction n).Valid V) :=
  (reduction n).laws hp (translation g hg)


/-- Two scalar fields per target input entry. The two views of the tour alias;
    the shared arena combinator conservatively counts both views. -/
def arena (n : Nat) : Reduction.Arena (Source n) (Decoder n) (Input (tourSize n)) (Nat × Nat) Nat where
  translatorCells _ := n + 2*tourSize n
  inputCells _ := 2*tourSize n
  queryCells _ := 2
  answerCells _ := 1
  conversionPeak s := cachedWords s.val.cache + preparationPeak s.val
  encodePeak _ := 8
  decodePeak _ := 4

def capacity (n : Nat) : Reduction.Capacity where
  conversion := 12*tourSize n + 8
  input := 2*tourSize n
  translator := n + 2*tourSize n
  encoded := 2
  answer := 1
  encodePeak := 8
  decodePeak := 4
  encodeWork := 3
  decodeWork := 2

/-- Capacity obligations are discharged for every backend state and reply.
    No assumption about a desired backend work or storage bound appears here. -/
theorem capacityLaws (n : Nat) {R : Type} (p : Ops (Input (tourSize n)) (Nat × Nat) Nat R)
    (V : Input (tourSize n) → R → Prop) :
    (reduction n).CapacityLaws p V (arena n) (capacity n) where
  conversion s := by
    have hw := cachedWords_bound s.val.cache
    have hc := Tree.cache_calls s.val
    have ht := Tree.tour_length s.val
    have hp := preparationPeak_bound s.val
    have hl := source_length s
    simp only [arena, capacity]
    omega
  input _ := Nat.le_refl _
  translator _ := Nat.le_refl _
  encoded _ _ := Nat.le_refl _
  answer _ _ _ _ := Nat.le_refl _
  encodePeak _ := Nat.le_refl _
  decodePeak _ := Nat.le_refl _
  encodeWork s q := by simp [reduction, encodeM_exact, capacity]
  decodeWork _ _ _ _ := decodeM_cost _ _

/-- Backend resource certificates compose through the same shared laws as
    correctness. Queries retain an explicit five-event translation overhead. -/
theorem bounds (n : Nat) {R : Type} {p : Ops (Input (tourSize n)) (Nat × Nat) Nat R}
    {V : Input (tourSize n) → R → Prop} {storage : Storage (Input (tourSize n)) R}
    {profile : Profile (Input (tourSize n))} (hp : Bounds p V storage profile) :
    Bounds ((reduction n).apply p) ((reduction n).Valid V)
      ((reduction n).storage p (arena n) storage)
      ((reduction n).profile profile (capacity n)) :=
  (reduction n).bounds hp (capacityLaws n p V)

theorem conversion_work {n : Nat} (s : Source n) :
    ((reduction n).convert s).2 ≤ 3*n + 31*tourSize n + 7 := by
  have := prepareMapsM_cost s.val
  simpa [reduction, convertM, s.property, source_length s] using this

theorem composed_query_work (n : Nat) {R : Type} (p : Ops (Input (tourSize n)) (Nat × Nat) Nat R)
    (state : Decoder n × R) (q : Query n) :
    (((reduction n).apply p).answer state q).2 ≤
      5 + (p.answer state.2 ((reduction n).encode state.1 q).1).2 := by
  rw [Reduction.query_work]
  have he : ((reduction n).encode state.1 q).2 = 3 := by simp [reduction, encodeM_exact]
  have hd := decodeM_cost state.1 (p.answer state.2 ((reduction n).encode state.1 q).1).1
  change ((reduction n).decode _ _).2 ≤ 2 at hd
  omega

end Sequences.LCA.TreeReduction
