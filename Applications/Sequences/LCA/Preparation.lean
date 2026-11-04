import Applications.Sequences.LCA.MicroExecution
import Applications.Sequences.LCA.BlockedRMQ

/-! Full measured preprocessing: finite depth copy, effective classification,
shared class tables, block minima and macro sparse construction. -/
namespace Sequences.LCA.Preparation
open Resources Dijkstra.Store TableExecution MicroExecution BlockedRMQ

def multiplyWord (a b : Nat) : Measured Nat Nat := (a*b,1)

def addressM (source : Nat → Measured Int Nat) (offset steps : Nat) :
    Measured (Fin (2^steps)) Nat :=
  let run := codeM source offset steps
  (⟨run.1, by rw [codeM_value]; exact shapeCode_lt _⟩, run.2)

theorem addressM_value (source : Nat → Measured Int Nat) (offset steps : Nat) :
    (addressM source offset steps).1 = classAddress steps (fun i => (source (offset+i)).1) := by
  apply Fin.ext
  exact codeM_value source offset steps

def blockAddressM (source : Nat → Measured Int Nat) (steps block : Nat) :
    Measured (Fin (2^steps)) Nat :=
  bind (multiplyWord block (steps+1)) fun offset => addressM source offset steps

def microM (source : Nat → Measured Int Nat) (steps blocks : Nat) :
    Measured (MicroData steps blocks) Nat :=
  bind (tabulate 0 (fun i : Fin (blocks*(steps+1)) => source i.val)) fun depths =>
  bind (tabulate (⟨0, Nat.two_pow_pos steps⟩ : Fin (2^steps))
    (fun block : Fin blocks => blockAddressM source steps block.val)) fun classes =>
  bind (sharedM steps) fun shared => pure ⟨depths, classes, shared⟩

theorem microM_value (source : Nat → Measured Int Nat) (steps blocks : Nat) :
    (microM source steps blocks).1 = buildMicro (fun i => (source i).1) steps blocks := by
  simp only [microM, Resources.bind, Resources.pure, tabulate_value, sharedM_value,
    blockAddressM, multiplyWord, addressM_value]
  rfl

def microWork (steps blocks c : Nat) : Nat :=
  blocks*(steps+1)*(c+6) + blocks*(steps*(2*c+6)+7) + 64*(steps+1)*(steps+1)*2^steps

theorem microM_cost (source : Nat → Measured Int Nat) (steps blocks c : Nat)
    (hc : ∀ i, (source i).2 ≤ c) : (microM source steps blocks).2 ≤ microWork steps blocks c := by
  have hd := tabulate_cost (n := blocks*(steps+1)) (0 : Int)
    (fun i : Fin (blocks*(steps+1)) => source i.val) c (fun i => hc i.val)
  have ha : ∀ block : Fin blocks, (blockAddressM source steps block.val).2 ≤ steps*(2*c+6)+1 := by
    intro block
    simp only [blockAddressM, multiplyWord, Resources.bind, addressM]
    have hh := codeM_cost source (block.val*(steps+1)) steps c hc
    omega
  have hb := tabulate_cost (⟨0, Nat.two_pow_pos steps⟩ : Fin (2^steps))
    (fun block : Fin blocks => blockAddressM source steps block.val) (steps*(2*c+6)+1) ha
  have hs := sharedM_cost steps
  simp only [microM, Resources.bind, Resources.pure, microWork]
  nlinarith

def minimaM (micro : MicroData steps blocks) (hb : 0 < blocks) : Measured (Vector Key blocks) Nat :=
  tabulate (toLex (0,0)) (fun block : Fin blocks => withinMeasured micro hb block.val 0 steps)

theorem minimaM_value (micro : MicroData steps blocks) (hb : 0 < blocks) :
    (minimaM micro hb).1 = blockMinima micro hb := by
  simp only [minimaM, tabulate_value, withinMeasured_value]
  rfl

theorem minimaM_cost (micro : MicroData steps blocks) (hb : 0 < blocks) :
    (minimaM micro hb).2 ≤ 20*blocks := by
  have hh := tabulate_cost (toLex ((0 : Int),(0 : Nat)))
    (fun block : Fin blocks => withinMeasured micro hb block.val 0 steps) 14
    (fun block => (withinMeasured_cost micro hb block.val 0 steps).le)
  simpa [minimaM, Nat.mul_comm] using hh

def prepare (source : Nat → Measured Int Nat) (steps blocks levels : Nat) (hb : 0 < blocks) :
    Measured (Data steps blocks levels) Nat :=
  bind (microM source steps blocks) fun micro =>
  bind (minimaM micro hb) fun minima =>
  bind (SparseExecution.prepare (toLex (0,0)) minima levels) fun tables =>
  pure ⟨micro, tables.1, tables.2⟩

theorem prepare_value (source : Nat → Measured Int Nat) (steps blocks levels : Nat) (hb : 0 < blocks) :
    (prepare source steps blocks levels hb).1 = build (fun i => (source i).1) steps blocks hb levels := by
  simp only [prepare, Resources.bind, Resources.pure, microM_value, minimaM_value]
  rfl

def work (steps blocks levels c : Nat) :=
  microWork steps blocks c + 20*blocks + (14*blocks+3+levels*(11*blocks+7))

theorem prepare_cost (source : Nat → Measured Int Nat) (steps blocks levels c : Nat)
    (hb : 0 < blocks) (hc : ∀ i, (source i).2 ≤ c) :
    (prepare source steps blocks levels hb).2 ≤ work steps blocks levels c := by
  have hm := microM_cost source steps blocks c hc
  have hb' := minimaM_cost (microM source steps blocks).1 hb
  have hs := SparseExecution.prepare_cost (toLex ((0 : Int),(0 : Nat)))
    (minimaM (microM source steps blocks).1 hb).1 levels
  simp only [prepare, Resources.bind, Resources.pure, work]
  omega

end Sequences.LCA.Preparation
