import Applications.Sequences.LCA.Control
import Applications.Sequences.LCA.MachineCapacity
import Applications.Sequences.LCA.Catalog

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.LCA.BackendBounds
open Resources.Prepared TreeReduction Backend Dijkstra.Store

/-- The source callback's live scalar values. The input array is a borrowed
reference; its cells are accounted separately. Every padding intermediate is
retained here, so the observation does not depend on register reuse. -/
def sourceControl {m : Nat} (input : Input m) (i : Nat) : Control.Run Int :=
  if h : i<m then
    let d := (lookup input.cells ⟨i,h⟩).2
    Control.scope [.ref input.cells,.nat i,.nat m,.bit true]
      (Control.note (d : Int) [.nat d,.integer d])
  else
    let last := m-1
    let d := (lookup input.cells ⟨last,by have := input.positive; omega⟩).2
    let delta := i-last
    Control.scope [.ref input.cells,.nat i,.nat m,.bit false]
      (Control.note ((d : Int)+(delta : Int))
        [.nat last,.nat d,.nat delta,.integer d,.integer delta,.integer ((d : Int)+(delta : Int))])

theorem sourceControl_value {m : Nat} (input : Input m) (i : Nat) :
    (sourceControl input i).value = (sourceM input i).1 := by
  rw [sourceM_value]
  have hm := input.positive
  by_cases hi : i<m <;>
    simp [sourceControl, hi, Control.scope, Control.note, paddedDepth, Input.depth,
      show m-1<m by omega]

theorem sourceControl_peak {m : Nat} (input : Input m) (i : Nat) :
    (sourceControl input i).peak ≤ 10 := by
  by_cases hi : i<m <;> simp [sourceControl, hi, Control.scope, Control.note]

theorem workspace_value {m : Nat} (input : Input m) :
    (Workspace.selectedRun (sourceM input) m).value = ((ops m).prepare input).1 :=
  Workspace.prepareRun_value _ _ _ _ _

theorem control_value {m : Nat} (input : Input m) :
    (Control.selectedRun (sourceControl input) m).value = ((ops m).prepare input).1 := by
  rw [Control.selectedRun_value]
  simp only [sourceControl_value, ops, Preparation.prepare_value]

def preparationPeak {m : Nat} (input : Input m) : Nat :=
  Catalog.inputWords input + Workspace.words (Workspace.selectedRun (sourceM input) m) +
    (Control.selectedRun (sourceControl input) m).peak

/-- The packed layout preserves the block-minimum reservation after sparse
construction. Observe the live arrays plus that blocks-sized reserved gap. -/
def retainedWords {m : Nat} (state : State m) : Nat :=
  Storage.dataWords state + state.micro.classes.toArray.size

theorem retainedWords_eq {m : Nat} (state : State m) :
    retainedWords state = PreparationBounds.retainedSlots m := by
  have hb := blockSize_pos m
  simp only [retainedWords, Storage.dataWords_eq, Vector.size_toArray,
    show blockSize m-1+1=blockSize m by omega]
  unfold PreparationBounds.retainedSlots PreparationBounds.paddedCapacity PreparationBounds.sharedSlots
  omega

def queryPeak {m : Nat} (state : State m) : Nat := retainedWords state + QueryStorage.answerPeak state

def storage (m : Nat) : Resources.Prepared.Storage (Input m) (State m) where
  retained := retainedWords
  preparePeak := preparationPeak
  queryPeak := queryPeak

def profile (m : Nat) : Profile (Input m) where
  preparation _ := 1024*m
  query _ := 57
  maintenance _ := 0
  retained _ := 36*m
  peak _ := 512*m

theorem preparationPeak_le {m : Nat} (input : Input m) : preparationPeak input ≤ 512*m := by
  have hw := Workspace.prepareRun_linear (sourceM input) input.positive
  have hc := Control.selectedRun_peak (sourceControl input) input.positive (sourceControl_peak input)
  simp only [preparationPeak, Catalog.inputWords, Vector.size_toArray]
  omega

theorem bounds (m : Nat) : Bounds (ops m) Valid (storage m) (profile m) where
  preparation := prepare_cost
  query _ state _ q := answer_cost state q
  retained input state _ := by
    change retainedWords state ≤ 36*m
    rw [retainedWords_eq]
    exact PreparationBounds.retainedSlots_le input.positive
  preparePeak := preparationPeak_le
  queryPeak input state _ := by
    have hr := PreparationBounds.retainedSlots_le input.positive
    have hs := QueryStorage.answerPeak_le state
    have hp := input.positive
    change retainedWords state + QueryStorage.answerPeak state ≤ 512*m
    rw [retainedWords_eq]
    omega

/-- Eligibility includes the operation-derived preparation peak and all online
scalar traces, alongside the packed key/address width requirements. -/
structure Machine {m : Nat} (input : Input m) (width capacity : Nat) : Prop where
  words : MachineCapacity.WordEligible m width capacity
  preparation : preparationPeak input ≤ capacity
  query : queryPeak ((ops m).prepare input).1 ≤ capacity

theorem machine_arena {m width capacity : Nat} {input : Input m} (h : Machine input width capacity) :
    MachineCapacity.Eligible m width capacity (Catalog.inputWords input)
      (Control.selectedRun (sourceControl input) m).peak := by
  refine ⟨h.words,?_⟩
  have hp := h.preparation
  rw [preparationPeak, Workspace.selectedRun_words] at hp
  unfold MachineCapacity.requiredSlots
  omega

theorem exists_machine {m : Nat} (input : Input m) : ∃ width, Machine input width (512*m) := by
  obtain ⟨width, hw⟩ := MachineCapacity.exists_width input.positive (512*m)
  refine ⟨width,hw,preparationPeak_le input,?_⟩
  exact (bounds m).queryPeak input _ (prepare_valid input)

def lcaStorage (n : Nat) := (TreeReduction.reduction n).storage (ops (tourSize n))
  (TreeReduction.arena n) (storage (tourSize n))

def lcaProfile (n : Nat) := (TreeReduction.reduction n).profile (profile (tourSize n))
  (TreeReduction.capacity n)

theorem lca_bounds (n : Nat) : Bounds (lcaOps n) ((TreeReduction.reduction n).Valid Valid)
    (lcaStorage n) (lcaProfile n) := TreeReduction.bounds n (bounds (tourSize n))

/-- Arbitrarily slow startup is admitted, while every later LCA query has the
same deadline. Capacity includes the translator, backend and peak scratch. -/
def realtime (n : Nat) : Requirements where
  startup := none
  deadline := 62
  maintenance := 0
  capacity := n+38*tourSize n
  peak := n+516*tourSize n+8

theorem realtime_feasible {n : Nat} (s : Source n) : Feasible (realtime n) (lcaProfile n) s := by
  have hp := s.val.size_pos
  have hn : 0<n := by simpa only [s.property] using hp
  have hm : 0<tourSize n := by unfold tourSize; omega
  simp only [Feasible, realtime, lcaProfile, Reduction.profile, TreeReduction.capacity, profile]
  simp only [Option.mem_def, reduceCtorEq, false_implies, forall_const, true_and]
  omega

end Sequences.LCA.BackendBounds
