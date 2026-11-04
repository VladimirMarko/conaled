import Applications.Sequences.LCA.TreeReduction
import Applications.Sequences.LCA.Preparation
import Applications.Sequences.LCA.PreparationBounds

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.LCA.Backend
open Resources Resources.Prepared Dijkstra.Store TreeReduction TreeBackend

/-- The size is a backend specialization parameter. Block dimensions and their
logarithms are compile-time configuration, shared by every input of this size. -/
abbrev State (m : Nat) := BlockedRMQ.Data (blockSize m-1)
  (PreparationBounds.blocks m) (PreparationBounds.levels m)

def subtractWord (a b : Nat) : Measured Nat Nat := (a-b,1)
def lastIndex (m : Nat) (hm : 0 < m) : Measured (Fin m) Nat := (⟨m-1, by omega⟩,1)
def signedWord (a : Nat) : Measured Int Nat := (a,1)
def addSigned (a b : Int) : Measured Int Nat := (a+b,1)

/-- Checked depth load, or upward padding from the last cell. Each arithmetic,
read, signed conversion, and branch dispatch contributes to the tariff. -/
def sourceM {m : Nat} (input : Input m) (i : Nat) : Measured Int Nat :=
  bind (checkIndex i m) fun address => dispatch <| match address with
  | some j => bind (readWord (lookup input.cells j).2) signedWord
  | none =>
    bind (lastIndex m input.positive) fun last =>
    bind (readWord (lookup input.cells last).2) fun depth =>
    bind (subtractWord i last) fun delta =>
    bind (signedWord depth) fun d =>
    bind (signedWord delta) fun offset => addSigned d offset

theorem sourceM_value {m : Nat} (input : Input m) (i : Nat) :
    (sourceM input i).1 = paddedDepth (fun j => (input.depth j : Int)) m i := by
  have hp := input.positive
  by_cases hi : i < m <;>
    simp [sourceM, checkIndex, hi, dispatch, readWord, signedWord, subtractWord, lastIndex,
      addSigned, Resources.bind, paddedDepth, Input.depth, show m-1<m by omega]

theorem sourceM_cost {m : Nat} (input : Input m) (i : Nat) : (sourceM input i).2 ≤ 8 := by
  by_cases hi : i < m <;>
    simp [sourceM, checkIndex, hi, dispatch, readWord, signedWord, subtractWord, lastIndex,
      addSigned, Resources.bind]

theorem input_steps {m : Nat} (input : Input m) :
    UnitSteps (m-1) (fun i => (input.depth i : Int)) := by
  intro i hi
  have hn : i+1<m := by omega
  have hc := input.unit i hn
  simp only [Input.depth, hn, show i<m by omega, ↓reduceDIte]
  rcases hc with h | h <;> [left; right] <;> omega

/-- Invalid intervals have the explicit total result zero. -/
def spec {m : Nat} (input : Input m) (q : Nat × Nat) : Nat :=
  if q.1 ≤ q.2 ∧ q.2 < m then rmqSpec input q else 0

theorem spec_correct (m : Nat) : RMQCorrect (@spec m) := by
  intro input lo hi hlo hhi
  simpa only [spec, hlo, hhi, and_self, ite_true] using
    rmqSpec_correct m input lo hi hlo hhi

def answerM {m : Nat} (state : State m) (q : Nat × Nat) : Measured Nat Nat :=
  bind ((decide (q.1 ≤ q.2),1) : Measured Bool Nat) fun ordered =>
  bind ((decide (q.2 < m),1) : Measured Bool Nat) fun bounded =>
  dispatch <| if ordered && bounded then
    BlockedRMQ.queryMeasured state (PreparationBounds.blocks_pos m) q.1 q.2
  else pure 0

def ops (m : Nat) : Ops (Input m) (Nat × Nat) Nat (State m) where
  prepare input := Preparation.prepare (sourceM input) (blockSize m-1)
    (PreparationBounds.blocks m) (PreparationBounds.levels m) (PreparationBounds.blocks_pos m)
  answer := answerM

def Valid {m : Nat} (input : Input m) (state : State m) : Prop :=
  state = BlockedRMQ.buildPadded (fun i => (input.depth i : Int)) m (blockSize m-1)

theorem prepare_valid {m : Nat} (input : Input m) : Valid input ((ops m).prepare input).1 := by
  unfold Valid ops
  rw [Preparation.prepare_value]
  simp only [sourceM_value]
  rfl

theorem answer_cost {m : Nat} (state : State m) (q : Nat × Nat) : (answerM state q).2 ≤ 57 := by
  have h := BlockedRMQ.queryMeasured_cost state (PreparationBounds.blocks_pos m) q.1 q.2
  simp only [answerM, Resources.bind, dispatch]
  split <;> (try dsimp only [Resources.pure]) <;> omega

theorem laws (m : Nat) : Laws (@spec m) (ops m) Valid where
  prepare := prepare_valid
  answer input state hv q := by
    subst state
    by_cases h : q.1 ≤ q.2 ∧ q.2 < m
    · have he := BlockedRMQ.query_padded_eq (fun i => (input.depth i : Int))
        input.positive (input_steps input) (blockSize m-1) h.1 h.2
      dsimp only [ops, answerM, Resources.bind, dispatch]
      simp only [h.1, h.2, decide_true, Bool.and_self, ite_true]
      change (BlockedRMQ.queryMeasured _ (BlockedRMQ.blockCount_pos m (blockSize m-1)) q.1 q.2).1 = _
      dsimp only [PreparationBounds.levels, PreparationBounds.blocks]
      exact (BlockedRMQ.queryMeasured_value _ _ _ _).trans
        (by simpa [spec, h, rmqSpec] using he)
    · have hb : (decide (q.1 ≤ q.2) && decide (q.2 < m)) = false := by
        by_cases hl : q.1 ≤ q.2 <;> by_cases hh : q.2 < m <;> simp_all
      simp [ops, answerM, Resources.bind, dispatch, spec, h, hb, Resources.pure]

theorem prepare_cost {m : Nat} (input : Input m) : ((ops m).prepare input).2 ≤ 1024*m := by
  have h := Preparation.prepare_cost (sourceM input) (blockSize m-1)
    (PreparationBounds.blocks m) (PreparationBounds.levels m) 8
    (PreparationBounds.blocks_pos m) (sourceM_cost input)
  have hb := blockSize_pos m
  have hw : Preparation.work (blockSize m-1) (PreparationBounds.blocks m)
      (PreparationBounds.levels m) 8 = PreparationBounds.preparationWork m := by
    simp [Preparation.work, Preparation.microWork, PreparationBounds.preparationWork,
      PreparationBounds.sourceWork, PreparationBounds.classificationWork,
      PreparationBounds.sharedWork, PreparationBounds.macroWork,
      PreparationBounds.paddedCapacity, show blockSize m-1+1=blockSize m by omega, Nat.mul_comm]
  rw [hw] at h
  exact h.trans (PreparationBounds.preparationWork_le input.positive)

def lcaOps (n : Nat) := (TreeReduction.reduction n).apply (ops (tourSize n))

theorem lca_laws (n : Nat) : Laws sourceLCA (lcaOps n)
    ((TreeReduction.reduction n).Valid Valid) :=
  TreeReduction.laws _ (spec_correct _) _ _ (laws _)

theorem lca_answer_cost {n : Nat} (state : Decoder n × State (tourSize n)) (q : Query n) :
    ((lcaOps n).answer state q).2 ≤ 62 := by
  have ht := composed_query_work n (ops (tourSize n)) state q
  have hb := answer_cost state.2 ((TreeReduction.reduction n).encode state.1 q).1
  change ((ops (tourSize n)).answer _ _).2 ≤ 57 at hb
  exact ht.trans (by omega)

theorem lca_prepare_cost {n : Nat} (s : Source n) :
    ((lcaOps n).prepare s).2 ≤ 2*n + 1054*tourSize n + 7 := by
  have ht := conversion_work s
  have hb := prepare_cost ((TreeReduction.reduction n).convert s).1.2
  rw [lcaOps, Reduction.preparation_work]
  omega

end Sequences.LCA.Backend
