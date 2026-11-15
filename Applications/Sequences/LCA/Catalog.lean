import Applications.Sequences.LCA.Backend

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.LCA.Catalog
open Resources Resources.Prepared Dijkstra.Store TreeReduction TreeBackend Backend
open Sequences.PreparedRMQ

abbrev Key := Int ×ₗ Nat

def keyM {m : Nat} (input : Input m) (i : Nat) : Measured Key Nat :=
  bind (checkIndex i m) fun address => dispatch <| match address with
  | some j => bind (readWord (lookup input.cells j).2) fun d =>
      bind (signedWord d) fun z => (toLex (z,i),2)
  | none => (toLex (0,i),2)

theorem keyM_value {m : Nat} (input : Input m) (i : Nat) :
    (keyM input i).1 = depthKey (fun j => (input.depth j : Int)) i := by
  by_cases hi : i<m <;>
    simp [keyM, checkIndex, hi, dispatch, readWord, signedWord, Resources.bind, depthKey, Input.depth]

theorem keyM_cost {m : Nat} (input : Input m) (i : Nat) : (keyM input i).2 ≤ 6 := by
  by_cases hi : i<m <;>
    simp [keyM, checkIndex, hi, dispatch, readWord, signedWord, Resources.bind]

/-- Tail-recursive direct scan: only the next address, remaining length, and
current two-word minimum cross an iteration boundary. -/
def scanM (read : Nat → Measured Key Nat) (next : Nat) (current : Key) : Nat → Measured Key Nat
  | 0 => dispatch (pure current)
  | k+1 => countDispatch <| bind (read next) fun x =>
      bind ((min current x,1) : Measured Key Nat) fun best =>
      bind (increment next) fun following => scanM read following best k

theorem scanM_value (read : Nat → Measured Key Nat) (start i n : Nat) :
    (scanM read (start+i+1) (rangeMin (fun j => (read j).1) start i) n).1 =
      rangeMin (fun j => (read j).1) start (i+n) := by
  induction n generalizing i with
  | zero => simp [scanM, dispatch, Resources.bind, Resources.pure]
  | succ n ih =>
    simp only [scanM, countDispatch, dispatch, Resources.bind, increment]
    have h := ih (i+1)
    rw [rangeMin] at h
    simpa only [Nat.add_assoc, Nat.add_comm 1 n] using h

theorem scanM_cost (read : Nat → Measured Key Nat) (c : Nat)
    (hc : ∀ i, (read i).2 ≤ c) (next : Nat) (current : Key) (n : Nat) :
    (scanM read next current n).2 ≤ (c+4)*n+1 := by
  induction n generalizing next current with
  | zero => simp [scanM, dispatch, Resources.bind, Resources.pure]
  | succ n ih =>
    simp only [scanM, countDispatch, dispatch, Resources.bind, increment]
    have hh := ih (next+1) (min current (read next).1)
    have hr := hc next
    nlinarith

def directAnswer {m : Nat} (input : Input m) (q : Nat × Nat) : Measured Nat Nat :=
  bind ((decide (q.1 ≤ q.2),1) : Measured Bool Nat) fun ordered =>
  bind ((decide (q.2 < m),1) : Measured Bool Nat) fun bounded =>
  dispatch <| if ordered && bounded then
    bind (subtractWord q.2 q.1) fun len =>
    bind (keyM input q.1) fun initial =>
    bind (increment q.1) fun next =>
    bind (scanM (keyM input) next initial len) fun best => ((ofLex best).2,1)
  else pure 0

def direct (m : Nat) : Ops (Input m) (Nat × Nat) Nat (Input m) where
  prepare := pure
  answer := directAnswer

theorem direct_laws (m : Nat) : Laws (@spec m) (direct m) (fun s r => r=s) where
  prepare _ := rfl
  answer input state hv q := by
    subst state
    have he := scanM_value (keyM input) q.1 0 (q.2-q.1)
    simp only [Nat.add_zero, rangeMin] at he
    simp only [keyM_value] at he
    by_cases h : q.1 ≤ q.2 ∧ q.2<m
    · simp [direct, directAnswer, Resources.bind, dispatch, h.1, h.2, spec,
        subtractWord, increment, he, keyM_value, rmqSpec, argmin]
    · have hb : (decide (q.1 ≤ q.2) && decide (q.2 < m)) = false := by
        by_cases hl : q.1 ≤ q.2 <;> by_cases hh : q.2 < m <;> simp_all
      simp [direct, directAnswer, Resources.bind, dispatch, hb, spec, h, Resources.pure]

theorem direct_cost {m : Nat} (input : Input m) (q : Nat × Nat) :
    (directAnswer input q).2 ≤ 10*m+13 := by
  have h := scanM_cost (keyM input) 6 (keyM_cost input) (q.1+1)
    (keyM input q.1).1 (q.2-q.1)
  have hk := keyM_cost input q.1
  simp only [directAnswer, Resources.bind, dispatch]
  split
  · rename_i ht
    have hhi : q.2<m := by simp only [Bool.and_eq_true, decide_eq_true_eq] at ht; exact ht.2
    simp only [subtractWord, increment]
    omega
  · simp [Resources.pure]

/-- Register state at a tail-loop boundary. Keys are conservatively represented
by two words here; six scratch registers cover a checked key load, comparison,
and next-address arithmetic. Tail calls replace this frame. -/
def scanFrame (next remaining : Nat) (current : Key) : Vector Int 4 :=
  #v[next,remaining,(ofLex current).1,(ofLex current).2]

def scanSpace (read : Nat → Key) (next : Nat) (current : Key) : Nat → Key × Nat
  | 0 => (current, (scanFrame next 0 current).toArray.size)
  | k+1 =>
    let rest := scanSpace read (next+1) (min current (read next)) k
    (rest.1, max ((scanFrame next (k+1) current).toArray.size+6) rest.2)

theorem scanSpace_value (read : Nat → Measured Key Nat) (next : Nat) (current : Key) (n : Nat) :
    (scanSpace (fun i => (read i).1) next current n).1 = (scanM read next current n).1 := by
  induction n generalizing next current with
  | zero => rfl
  | succ n ih => simp only [scanSpace, scanM, countDispatch, dispatch, Resources.bind, increment, ih]

theorem scanSpace_peak (read : Nat → Key) (next : Nat) (current : Key) (n : Nat) :
    (scanSpace read next current n).2 ≤ 10 := by
  induction n generalizing next current with
  | zero => simp [scanSpace]
  | succ n ih =>
    simp only [scanSpace, Vector.size_toArray, max_le_iff]
    exact ⟨by decide,ih _ _⟩

def inputWords {m : Nat} (input : Input m) : Nat := 2*input.cells.toArray.size

/-- Preparation transfers ownership of the finite input without a copy. Query
execution retains it, and reserves twelve scalar registers: the loop's ten,
plus the two interval endpoints. No query writes into the input. -/
def directStorage (m : Nat) : Resources.Prepared.Storage (Input m) (Input m) where
  retained := inputWords
  preparePeak := inputWords
  queryPeak input := inputWords input + 12

theorem direct_scan_fits {m : Nat} (input : Input m) (next : Nat) (current : Key) (n : Nat) :
    inputWords input + 2 + (scanSpace (fun i => (keyM input i).1) next current n).2 ≤
      (directStorage m).queryPeak input := by
  have hh := scanSpace_peak (fun i => (keyM input i).1) next current n
  simp only [directStorage]
  omega

def directProfile (m : Nat) : Profile (Input m) where
  preparation _ := 0
  query _ := 10*m+13
  maintenance _ := 0
  retained _ := 2*m
  peak _ := 2*m+12

theorem direct_bounds (m : Nat) : Bounds (direct m) (fun s r => r=s)
    (directStorage m) (directProfile m) where
  preparation _ := Nat.le_refl _
  query _ state _ q := direct_cost state q
  retained _ _ _ := by simp [directStorage, inputWords, directProfile]
  preparePeak _ := by simp [directStorage, inputWords, directProfile]
  queryPeak _ _ _ := by simp [directStorage, inputWords, directProfile]

end Sequences.LCA.Catalog
