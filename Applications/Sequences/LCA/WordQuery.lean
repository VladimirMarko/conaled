import Applications.Sequences.LCA.WordWithin
import Applications.Sequences.LCA.WordSummary

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace Sequences.LCA.WordQuery
open Resources PreparationBounds PackedBackend Dijkstra.Store
variable {m width capacity : Nat}

/-- Inner tests use one compare-and-branch primitive. The outer answer guard
uses two comparisons followed by a separate Boolean dispatch. -/
def reconstruct (m : Nat)
    (withinCallback : Nat → Nat → Nat → Measured (WordMachine.Word width) Nat)
    (summaryCallback : Nat → Nat → Measured (WordMachine.Word width) Nat)
    (lo hi : Nat) : Measured (WordMachine.Word width) Nat :=
  bind (WordMachine.scalar width (lo/blockSize m)) fun first =>
  bind (WordMachine.scalar width (hi/blockSize m)) fun last =>
  bind ((decide (first.val=last.val),1) : Measured Bool Nat) fun same =>
  if same then
    bind (WordMachine.scalar width (lo%blockSize m)) fun offset =>
    bind (WordMachine.scalar width (hi-lo)) fun len =>
    withinCallback first.val offset.val len.val
  else
    bind (WordMachine.scalar width (lo%blockSize m)) fun offset =>
    bind (WordMachine.scalar width ((blockSize m-1)-offset.val)) fun leftLen =>
    bind (withinCallback first.val offset.val leftLen.val) fun left =>
    bind (WordMachine.scalar width (hi%blockSize m)) fun rightLen =>
    bind (withinCallback last.val 0 rightLen.val) fun right =>
    bind (WordMachine.scalar width (first.val+1)) fun next =>
    bind ((decide (last.val=next.val),1) : Measured Bool Nat) fun adjacent =>
    if adjacent then WordMachine.minimum left right
    else
      bind (WordMachine.scalar width (last.val-first.val)) fun gap =>
      bind (WordMachine.scalar width (gap.val-2)) fun middleLen =>
      bind (summaryCallback next.val middleLen.val) fun middle =>
      bind (WordMachine.minimum middle right) fun rest => WordMachine.minimum left rest

def queryKey (m : Nat) (mem : Store capacity (WordMachine.Word width)) (lo hi : Nat) :=
  reconstruct m (WordWithin.within m mem) (WordSummary.run m mem) lo hi

def query (m : Nat) (mem : Store capacity (WordMachine.Word width))
    (lo hi : Nat) : Measured (WordMachine.Word width) Nat :=
  bind (queryKey m mem lo hi) fun key => WordMachine.scalar width (key.val % paddedCapacity m)

def answer (m : Nat) (mem : Store capacity (WordMachine.Word width))
    (lo hi : Nat) : Measured (WordMachine.Word width) Nat :=
  bind ((decide (lo≤hi),1) : Measured Bool Nat) fun ordered =>
  bind ((decide (hi<m),1) : Measured Bool Nat) fun bounded =>
  TreeBackend.dispatch <| if ordered && bounded then query m mem lo hi
    else Resources.pure (WordMachine.word width 0)

theorem queryKey_cost (m : Nat) (mem : Store capacity (WordMachine.Word width)) (lo hi : Nat) :
    (queryKey m mem lo hi).2 ≤ 53 := by
  simp only [queryKey, reconstruct, Resources.bind]
  split <;> simp only [WordWithin.within_cost, WordSummary.run_cost,
    WordMachine.scalar_cost, WordMachine.minimum_cost]
  · decide
  · split <;> simp only [WordMachine.minimum] <;> omega

theorem query_cost (m : Nat) (mem : Store capacity (WordMachine.Word width)) (lo hi : Nat) :
    (query m mem lo hi).2 ≤ 54 := by
  have hh := queryKey_cost m mem lo hi
  simp only [query, Resources.bind, WordMachine.scalar_cost]
  omega

theorem answer_cost (m : Nat) (mem : Store capacity (WordMachine.Word width)) (lo hi : Nat) :
    (answer m mem lo hi).2 ≤ 57 := by
  have hh := query_cost m mem lo hi
  simp only [answer, Resources.bind, TreeBackend.dispatch]
  split <;> (try dsimp only [Resources.pure]) <;> omega

def encode (m : Nat) (key : BlockedRMQ.Key) : Nat :=
  WordKey.encode 0 (paddedCapacity m) (ofLex key).1 (ofLex key).2

theorem scalar_value (h : MachineCapacity.WordEligible m width capacity) (hi : i ≤ 4*m+3) :
    (WordMachine.scalar width i).1.val = i :=
  WordMachine.word_of_lt (MachineCapacity.scalar_fits h hi)

theorem encode_min (ha : KeyBounds.Fits 0 (2*m) (paddedCapacity m) a)
    (hb : KeyBounds.Fits 0 (2*m) (paddedCapacity m) b) :
    min (encode m a) (encode m b) = encode m (min a b) := by
  exact (WordKey.encode_min (by simpa using ha.1) (by simpa using hb.1) ha.2.2 hb.2.2).symm

theorem bind_value {α β : Type} (a : Measured α Nat) (f : α → Measured β Nat) :
    (Resources.bind a f).1 = (f a.1).1 := rfl

theorem minimum_value (a b : WordMachine.Word width) :
    (WordMachine.minimum a b).1.val = min a.val b.val := rfl

theorem reconstruct_shape (h : MachineCapacity.WordEligible m width capacity)
    (withinCallback : Nat → Nat → Nat → Measured (WordMachine.Word width) Nat)
    (summaryCallback : Nat → Nat → Measured (WordMachine.Word width) Nat)
    (hlo : lo ≤ hi) (hhi : hi < m) :
    (reconstruct m withinCallback summaryCallback lo hi).1.val =
      blockedQuery (fun b o l => (withinCallback b o l).1.val)
        (fun s c => (summaryCallback s c).1.val) (blockSize m) lo hi := by
  unfold reconstruct
  have hb := blockSize_pos m
  have hbm := blockSize_le h.positive
  have hf : lo/blockSize m ≤ m := (Nat.div_le_self _ _).trans (by omega)
  have hl : hi/blockSize m < m := lt_of_le_of_lt (Nat.div_le_self _ _) hhi
  have hom := Nat.mod_lt lo hb
  have him := Nat.mod_lt hi hb
  have hfhl : lo/blockSize m ≤ hi/blockSize m := Nat.div_le_div_right hlo
  have hgap := Nat.sub_le (hi/blockSize m) (lo/blockSize m)
  have hmiddle := Nat.sub_le (hi/blockSize m-lo/blockSize m) 2
  have hs : ∀ i, i ≤ m → (WordMachine.scalar width i).1.val = i := by
    intro i hi
    exact scalar_value h (by omega)
  have hsf := hs _ hf
  have hsl := hs _ (by omega : hi/blockSize m ≤ m)
  have hso := hs _ (by omega : lo%blockSize m ≤ m)
  have hsz := hs _ (by omega : hi-lo ≤ m)
  have hsleft := hs _ (by omega : blockSize m-1-lo%blockSize m ≤ m)
  have hsright := hs _ (by omega : hi%blockSize m ≤ m)
  have hsnext := hs _ (by omega : lo/blockSize m+1 ≤ m)
  have hsgap := hs _ (by omega : hi/blockSize m-lo/blockSize m ≤ m)
  have hsmid := hs _ (by omega : hi/blockSize m-lo/blockSize m-2 ≤ m)
  by_cases same : lo/blockSize m=hi/blockSize m
  · simp only [bind_value, hsf, hsl]
    simp only [same, decide_true, ite_true, blockedQuery]
    simp only [bind_value, hso, hsz]
  · simp only [bind_value, hsf, hsl]
    simp only [same, decide_false, Bool.false_eq_true, ite_false, blockedQuery]
    simp only [bind_value, hso, hsleft, hsright, hsnext]
    by_cases adjacent : hi/blockSize m=lo/blockSize m+1
    · simp only [adjacent, decide_true, ite_true, minimum_value]
    · simp only [adjacent, decide_false, Bool.false_eq_true, ite_false]
      simp only [bind_value, hsgap, hsmid, minimum_value]

theorem queryKey_shape (h : MachineCapacity.WordEligible m width capacity)
    (mem : Store capacity (WordMachine.Word width)) (hlo : lo ≤ hi) (hhi : hi < m) :
    (queryKey m mem lo hi).1.val =
      blockedQuery (fun b o l => (WordWithin.within m mem b o l).1.val)
        (fun s c => (WordSummary.run m mem s c).1.val) (blockSize m) lo hi :=
  reconstruct_shape h _ _ hlo hhi

theorem queryKey_value (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (hlo : lo ≤ hi) (hhi : hi < m) :
    (queryKey m (arena input h) lo hi).1.val =
      encode m (BlockedRMQ.queryKey (state input) (blocks_pos m) lo hi) := by
  rw [queryKey_shape h.toWordEligible _ hlo hhi]
  have hb := blockSize_pos m
  have hp := paddedCapacity_covers input.positive
  have hlast : hi/blockSize m < blocks m := by
    apply (Nat.div_lt_iff_lt_mul hb).2
    change hi < paddedCapacity m
    omega
  have hfhl : lo/blockSize m ≤ hi/blockSize m := Nat.div_le_div_right hlo
  have hfirst : lo/blockSize m < blocks m := (Nat.div_le_div_right hlo).trans_lt hlast
  have hom := Nat.mod_lt lo hb
  have him := Nat.mod_lt hi hb
  have helo : lo/blockSize m*blockSize m+lo%blockSize m=lo := by
    simpa [Nat.mul_comm] using Nat.div_add_mod lo (blockSize m)
  have hehi : hi/blockSize m*blockSize m+hi%blockSize m=hi := by
    simpa [Nat.mul_comm] using Nat.div_add_mod hi (blockSize m)
  change blockedQuery _ _ (blockSize m) lo hi =
    encode m (blockedQuery _ _ (blockSize m-1+1) lo hi)
  rw [dimension]
  unfold blockedQuery
  by_cases same : lo/blockSize m=hi/blockSize m
  · have heq : lo/blockSize m*blockSize m=hi/blockSize m*blockSize m := congrArg (· * blockSize m) same
    have hint : lo%blockSize m+(hi-lo)<blockSize m := by omega
    simp only [ite_eq_left same]
    exact WordWithin.within_value input h (by omega) hint
  · simp only [ite_eq_right same]
    have hleft : lo%blockSize m+(blockSize m-1-lo%blockSize m)<blockSize m := by omega
    have hright : 0+hi%blockSize m<blockSize m := by omega
    have wl := WordWithin.within_value input h hfirst hleft
    have wr := WordWithin.within_value input h hlast hright
    have fl := WordWithin.within_fits input hfirst hleft
    have fr := WordWithin.within_fits input hlast hright
    change (WordWithin.within _ _ _ _ _).1.val = encode m _ at wl
    change (WordWithin.within _ _ _ _ _).1.val = encode m _ at wr
    rw [wl,wr]
    by_cases adjacent : hi/blockSize m=lo/blockSize m+1
    · simp only [ite_eq_left adjacent]
      exact encode_min fl fr
    · simp only [ite_eq_right adjacent]
      have hmiddle : (lo/blockSize m+1)+(hi/blockSize m-lo/blockSize m-2)<blocks m := by omega
      rw [WordSummary.run_value input h _ _ hmiddle]
      change min (encode m _) (min (encode m _) (encode m _)) = encode m _
      have fm := WordSummary.summary_fits input _ _ hmiddle
      rw [encode_min fm fr, encode_min fl (KeyBounds.fits_min fm fr)]

theorem query_value (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords)
    (hlo : lo ≤ hi) (hhi : hi < m) :
    (query m (arena input h) lo hi).1.val = BlockedRMQ.query (state input) (blocks_pos m) lo hi := by
  have ha := BlockedRMQ.query_padded (fun i => (input.depth i : Int)) input.positive
    (Backend.input_steps input) (blockSize m-1) hlo hhi
  have hh : BlockedRMQ.query (state input) (blocks_pos m) lo hi ≤ hi := by
    rw [state_eq]
    exact ha.2.1
  have hp := paddedCapacity_covers input.positive
  have hind : (ofLex (BlockedRMQ.queryKey (state input) (blocks_pos m) lo hi)).2 < paddedCapacity m := by
    change BlockedRMQ.query (state input) (blocks_pos m) lo hi < paddedCapacity m
    omega
  simp only [query, Resources.bind]
  rw [queryKey_value input h hlo hhi]
  unfold encode WordKey.encode
  rw [WordKey.pack_mod hind]
  exact scalar_value h.toWordEligible (by change BlockedRMQ.query _ _ _ _ ≤ _; omega)

theorem answer_refines (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) (lo hi : Nat) :
    (answer m (arena input h) lo hi).1.val = ((Backend.ops m).answer (state input) (lo,hi)).1 := by
  by_cases valid : lo ≤ hi ∧ hi < m
  · simp only [answer, Backend.ops, Backend.answerM, Resources.bind, TreeBackend.dispatch,
      valid.1, valid.2, decide_true, Bool.and_self, ite_true]
    rw [BlockedRMQ.queryMeasured_value]
    exact query_value input h valid.1 valid.2
  · have hb : (decide (lo ≤ hi) && decide (hi < m)) = false := by
      by_cases hl : lo ≤ hi <;> by_cases hh : hi < m <;> simp_all
    simp [answer, Backend.ops, Backend.answerM, Resources.bind, TreeBackend.dispatch,
      hb, Resources.pure, WordMachine.word]

theorem answer_spec (input : TreeReduction.Input m)
    (h : MachineCapacity.Eligible m width capacity inputWords frameWords) (lo hi : Nat) :
    (answer m (arena input h) lo hi).1.val = Backend.spec input (lo,hi) := by
  rw [answer_refines input h]
  exact (Backend.laws m).answer input (state input) (Backend.prepare_valid input) (lo,hi)

end Sequences.LCA.WordQuery
