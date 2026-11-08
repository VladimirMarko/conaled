import Applications.Sequences.LCA.PreparationCertificate
import Applications.Sequences.LCA.WordMachine

/-! Finite-word scalar execution used while constructing tables. Canonical
heights are shifted before storage; arithmetic wraps explicitly, and the
refinement proves that admitted executions do not wrap. -/
namespace Sequences.LCA.PreparationScalars
open Resources WordMachine Dijkstra.Store

/-- A finite counter value; the two events are the loop test and increment. -/
def counter (width i : Nat) : Measured (Word width) Nat := (word width i,2)

def relativeWord (steps : Nat) (code : Word width) : Nat → Measured (Word width) Nat
  | 0 => pure (word width steps)
  | i+1 => bind (relativeWord steps code i) fun height =>
    bind (counter width i) fun j =>
    bind (scalar width (code.val / 2^j.val)) fun shifted =>
    bind ((decide (shifted.val % 2 = 1),1) : Measured Bool Nat) fun up =>
    scalar width (if up then height.val+1 else height.val-1)

theorem relativeWord_cost (steps : Nat) (code : Word width) (i : Nat) :
    (relativeWord steps code i).2 = (MicroExecution.relativeCodeM code.val i).2 := by
  rw [MicroExecution.relativeCodeM_cost]
  induction i with
  | zero => rfl
  | succ i ih => simp [relativeWord,Resources.bind,scalar,counter,ih]; omega

theorem relativeWord_value (steps : Nat) (code : Word width)
    (hw : 2*steps < 2^width) (i : Nat) (hi : i ≤ steps) :
    ((relativeWord steps code i).1.val : Int) =
      (MicroExecution.relativeCodeM code.val i).1 + steps := by
  induction i with
  | zero => simp [relativeWord,MicroExecution.relativeCodeM,Resources.pure,
      word_of_lt (show steps < 2^width by omega)]
  | succ i ih =>
    have hp := ih (by omega)
    have hb := PreparationInvariants.relativeCodeM_bounds i code.val i le_rfl
    have hj : i < 2^width := by omega
    have hs : code.val / 2^i < 2^width := (Nat.div_le_self _ _).trans_lt code.isLt
    have hv : 0 < (relativeWord steps code i).1.val ∧
        (relativeWord steps code i).1.val+1 < 2^width := by omega
    dsimp only [relativeWord,Resources.bind,counter,scalar,
      MicroExecution.relativeCodeM,MicroExecution.counter,MicroExecution.shiftWord,
      MicroExecution.lowBit,MicroExecution.stepHeight]
    rw [word_of_lt hj,word_of_lt hs]
    change ((word width (if decide (code.val / 2^i % 2 = 1) then
      (relativeWord steps code i).1.val+1 else (relativeWord steps code i).1.val-1)).val : Int) =
      (MicroExecution.relativeCodeM code.val i).1 +
        (if decide (code.val / 2^i % 2 = 1) then 1 else -1) + steps
    split <;> rw [word_of_lt (by omega)] <;> omega


def canonicalWord (steps : Nat) (code : Word width) :=
  TableExecution.tabulate (word width steps) (fun i : Fin (steps+1) => relativeWord steps code i.val)

def shiftHeight (steps : Nat) (height : Int) : Nat := (height+steps).toNat

theorem relativeWord_refines (steps : Nat) (code : Word width)
    (hw : 2*steps < 2^width) (i : Nat) (hi : i ≤ steps) :
    TableTransport.transport Fin.val (relativeWord steps code i) =
      TableTransport.transport (shiftHeight steps) (MicroExecution.relativeCodeM code.val i) := by
  apply Prod.ext
  · have hv := relativeWord_value steps code hw i hi
    simp only [TableTransport.transport,shiftHeight]
    omega
  · exact relativeWord_cost steps code i

theorem canonicalWord_refines (steps : Nat) (code : Word width)
    (hw : 2*steps < 2^width) :
    TableTransport.transport (Vector.map Fin.val) (canonicalWord steps code) =
      TableTransport.transport (Vector.map (shiftHeight steps)) (MicroExecution.canonicalM steps code.val) := by
  unfold canonicalWord MicroExecution.canonicalM
  rw [← TableTransport.tabulate_transport,← TableTransport.tabulate_transport]
  have hs : (word width steps).val = shiftHeight steps 0 := by
    simp [shiftHeight,word_of_lt (show steps < 2^width by omega)]
  rw [hs]
  congr 1
  funext i
  exact relativeWord_refines steps code hw i.val (by have := i.isLt; omega)

/-- The all-down class reaches zero without unsigned underflow. -/
example : (relativeWord 2 (word 4 0) 2).1.val = 0 := by decide
example : (relativeWord 2 (word 4 3) 2).1.val = 4 := by decide
example : (relativeWord 2 (word 4 0) 2).2 = 10 := by decide
example : TableTransport.transport (Vector.map Fin.val) (canonicalWord 2 (word 4 0)) =
    TableTransport.transport (Vector.map (shiftHeight 2)) (MicroExecution.canonicalM 2 0) :=
  canonicalWord_refines 2 (word 4 0) (by decide)

/-- The floor-log loop stores finite words and reads the earlier half-index. -/
def logsWord (width : Nat) : (n : Nat) → Measured (Vector (Word width) (n+1)) Nat
  | 0 => (#v[word width 0],1)
  | k+1 => bind (logsWord width k) fun prev =>
    bind (if k = 0 then (word width 0,1) else
      bind ((⟨(k+1)/2,by omega⟩,1) : Measured (Fin (k+1)) Nat) fun j =>
      bind (TableExecution.read prev j) fun v => (word width (v.val+1),2)) fun v =>
    (prev.push v,3)

theorem logsWord_refines (n : Nat) (hw : n < 2^width) :
    TableTransport.transport (Vector.map Fin.val) (logsWord width n) = SparseExecution.logs n := by
  induction n with
  | zero => simp [logsWord,SparseExecution.logs,TableTransport.transport,word]
  | succ k ih =>
    have ih := ih (by omega)
    have hv := congrArg Prod.fst ih
    have hc := congrArg Prod.snd ih
    simp only [TableTransport.transport] at hv hc
    have hread : ∀ j : Fin (k+1),
        ((logsWord width k).1[j.val]).val = (SparseExecution.logs k).1[j.val] := by
      intro j
      have h := congrArg (fun v => v[j.val]) hv
      simpa only [Vector.getElem_map] using h
    by_cases hk : k = 0
    · subst k
      simp [logsWord,SparseExecution.logs,Resources.bind,TableTransport.transport,word]
    · have hj : (k+1)/2 < k+1 := by omega
      have hf : (SparseExecution.logs k).1[(k+1)/2]+1 < 2^width := by
        rw [SparseExecution.logs_get k ⟨(k+1)/2,hj⟩]
        change Nat.log 2 ((k+1)/2)+1 < 2^width
        have hl := Nat.log_le_self 2 ((k+1)/2)
        omega
      simp only [logsWord,SparseExecution.logs,Resources.bind,hk,ite_false,
        TableExecution.read,lookup,TableTransport.transport]
      rw [hread ⟨(k+1)/2,hj⟩,Vector.map_push,word_of_lt hf,hv,hc]

/-- Stored sparse spans are produced by repeated finite-word doubling. -/
def spanWord (width : Nat) : Nat → Measured (Word width) Nat
  | 0 => pure (word width 1)
  | k+1 => bind (spanWord width k) fun span => scalar width (span.val+span.val)

theorem spanWord_exact (k : Nat) (hw : 2^k < 2^width) :
    (spanWord width k).1.val = 2^k ∧ (spanWord width k).2 = k := by
  induction k with
  | zero => exact ⟨word_of_lt (by simpa only [pow_zero] using hw),rfl⟩
  | succ k ih =>
    have hp := Nat.two_pow_pos k
    have hk : 2^k < 2^width := by rw [pow_succ] at hw; omega
    obtain ⟨hv,hc⟩ := ih hk
    change (word width ((spanWord width k).1.val+(spanWord width k).1.val)).val = 2^(k+1) ∧
      (spanWord width k).2+1=k+1
    rw [hv,hc]
    constructor
    · rw [word_of_lt (by rw [pow_succ] at hw; omega),pow_succ]
      omega
    · omega

example : TableTransport.transport (Vector.map Fin.val) (logsWord 4 8) = SparseExecution.logs 8 :=
  logsWord_refines 8 (by decide)
example : (spanWord 4 3).1.val = 8 ∧ (spanWord 4 3).2 = 3 :=
  spanWord_exact 3 (by decide)

def eraseSource (source : Nat → Measured (Word width) Nat) (i : Nat) : Measured Int Nat :=
  ((source i).1.val, (source i).2)

/-- Classification executes on finite source words and finite intermediate
codes. The source callback is an already initialized indexed load. -/
def codeWord (source : Nat → Measured (Word width) Nat) (offset : Nat) :
    Nat → Measured (Word width) Nat
  | 0 => pure (word width 0)
  | k+1 => bind (counter width offset) fun here =>
    bind (scalar width (here.val+1)) fun next =>
    bind (source here.val) fun a =>
    bind (source next.val) fun b =>
    bind ((decide (a.val < b.val),1) : Measured Bool Nat) fun up =>
    bind (codeWord source next.val k) fun rest =>
    bind (scalar width (2*rest.val)) fun doubled => scalar width ((if up then 1 else 0)+doubled.val)

theorem codeWord_refines (source : Nat → Measured (Word width) Nat) (offset steps : Nat)
    (ho : offset+steps < 2^width) (hc : 2^steps ≤ 2^width) :
    TableTransport.transport Fin.val (codeWord source offset steps) =
      MicroExecution.codeM (eraseSource source) offset steps := by
  induction steps generalizing offset with
  | zero => simp [codeWord,MicroExecution.codeM,Resources.pure,TableTransport.transport,word]
  | succ k ih =>
    have hp := Nat.two_pow_pos k
    have hk : 2^k ≤ 2^width := by rw [pow_succ] at hc; omega
    have hi := ih (offset+1) (by omega) hk
    have hv := congrArg Prod.fst hi
    have ht := congrArg Prod.snd hi
    simp only [TableTransport.transport] at hv ht
    have hr := PreparationInvariants.codeM_lt (eraseSource source) (offset+1) k
    have hd : 2*(codeWord source (offset+1) k).1.val < 2^width := by
      rw [hv]; rw [pow_succ] at hc; omega
    have ha : (if (source offset).1.val < (source (offset+1)).1.val then 1 else 0) +
        2*(codeWord source (offset+1) k).1.val < 2^width := by
      rw [hv]; rw [pow_succ] at hc; split_ifs <;> omega
    dsimp only [codeWord,MicroExecution.codeM,Resources.bind,Resources.pure,
      counter,scalar,MicroExecution.counter,MicroExecution.addIndex,MicroExecution.goesUp,
      MicroExecution.doubleWord,eraseSource,TableTransport.transport]
    rw [word_of_lt (show offset < 2^width by omega),word_of_lt (show offset+1 < 2^width by omega)]
    simp only [decide_eq_true_eq]
    rw [word_of_lt hd,word_of_lt ha,hv,ht]
    simp

/-- All scalar loops used by the selected construction admit their actual
finite counter domains. This includes the final loop-test value. -/
theorem selected_envelopes (h : MachineCapacity.WordEligible m width capacity) :
    2*(blockSize m-1) < 2^width ∧ PreparationBounds.blocks m < 2^width ∧
      2^(PreparationBounds.levels m) < 2^width ∧ 2^(blockSize m-1) < 2^width := by
  have hb := blockSize_le h.positive
  have hn := PreparationBounds.blocks_le h.positive
  have hp : 2^(PreparationBounds.levels m) ≤ PreparationBounds.blocks m :=
    Nat.pow_log_le_self 2 (Nat.ne_of_gt (PreparationBounds.blocks_pos m))
  exact ⟨MachineCapacity.scalar_fits h (by omega),MachineCapacity.scalar_fits h (by omega),
    MachineCapacity.scalar_fits h (by omega),MachineCapacity.class_count_fits h⟩

theorem selected_canonical (h : MachineCapacity.WordEligible m width capacity) (code : Word width) :
    TableTransport.transport (Vector.map Fin.val) (canonicalWord (blockSize m-1) code) =
      TableTransport.transport (Vector.map (shiftHeight (blockSize m-1)))
        (MicroExecution.canonicalM (blockSize m-1) code.val) :=
  canonicalWord_refines _ _ (selected_envelopes h).1

theorem selected_logs (h : MachineCapacity.WordEligible m width capacity) :
    TableTransport.transport (Vector.map Fin.val) (logsWord width (PreparationBounds.blocks m)) =
      SparseExecution.logs (PreparationBounds.blocks m) :=
  logsWord_refines _ (selected_envelopes h).2.1

theorem selected_span (h : MachineCapacity.WordEligible m width capacity)
    (k : Nat) (hk : k ≤ PreparationBounds.levels m) :
    (spanWord width k).1.val = 2^k ∧ (spanWord width k).2 = k :=
  spanWord_exact k ((Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk).trans_lt (selected_envelopes h).2.2.1)

example : TableTransport.transport Fin.val
    (codeWord (fun i => (word 4 (if i=1 then 4 else 3),1)) 0 2) =
    MicroExecution.codeM (eraseSource (fun i => (word 4 (if i=1 then 4 else 3),1))) 0 2 :=
  codeWord_refines _ 0 2 (by decide) (by decide)

theorem selected_classifier (h : MachineCapacity.WordEligible m width capacity)
    (source : Nat → Measured (Word width) Nat) (offset steps : Nat)
    (ho : offset+steps < PreparationBounds.paddedCapacity m) (hs : steps ≤ blockSize m-1) :
    TableTransport.transport Fin.val (codeWord source offset steps) =
      MicroExecution.codeM (eraseSource source) offset steps := by
  have hp := PreparationBounds.paddedCapacity_le h.positive
  exact codeWord_refines source offset steps (MachineCapacity.scalar_fits h (by omega))
    ((Nat.pow_le_pow_right (by decide : 1 ≤ 2) hs).trans (MachineCapacity.class_count_fits h).le)

/-- The sparse-row address computation includes the addition before remainder. -/
def rowIndexWord (width n i span : Nat) : Measured (Word width) Nat :=
  bind (scalar width (i+span)) fun next => scalar width (next.val % n)

theorem rowIndexWord_refines (n i span : Nat) (hw : i+span < 2^width) :
    TableTransport.transport Fin.val (rowIndexWord width n i span) = ((i+span)%n,2) := by
  have hr : (i+span)%n < 2^width := (Nat.mod_le _ _).trans_lt hw
  simp [rowIndexWord,Resources.bind,scalar,TableTransport.transport,word_of_lt hw,word_of_lt hr]

theorem selected_rowIndex (h : MachineCapacity.WordEligible m width capacity)
    (i : Fin (PreparationBounds.blocks m)) (k : Nat) (hk : k ≤ PreparationBounds.levels m) :
    TableTransport.transport Fin.val
      (rowIndexWord width (PreparationBounds.blocks m) i.val (2^k)) =
      ((i.val+2^k)%PreparationBounds.blocks m,2) := by
  have hs : 2^k ≤ PreparationBounds.blocks m :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk).trans
      (Nat.pow_log_le_self 2 (Nat.ne_of_gt (PreparationBounds.blocks_pos m)))
  have hn := PreparationBounds.blocks_le h.positive
  have hi := i.isLt
  exact rowIndexWord_refines _ _ _ (MachineCapacity.scalar_fits h (by omega))

example : TableTransport.transport Fin.val (rowIndexWord 4 3 2 2) = (1,2) :=
  rowIndexWord_refines 3 2 2 (by decide)

end Sequences.LCA.PreparationScalars
