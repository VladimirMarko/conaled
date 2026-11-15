import Applications.Sequences.LCA.KeyBounds
import Applications.Sequences.LCA.Storage
import Applications.Sequences.LCA.Workspace

/-! Finite-word eligibility for sized RMQ machines. Memory requirements are
supplied by the preparation lifetime certificate; word requirements cover
packed keys and scalar arithmetic independently of that memory budget. -/
namespace Sequences.LCA.MachineCapacity
open PreparationBounds

structure WordEligible (m width capacity : Nat) : Prop where
  positive : 0 < m
  addresses : capacity ≤ 2^width
  keys : KeyBounds.wordCapacity m ≤ 2^width

/-- A finite machine exists for any chosen finite arena capacity. -/
theorem exists_width (hm : 0 < m) (capacity : Nat) :
    ∃ width, WordEligible m width capacity := by
  refine ⟨max capacity (KeyBounds.wordCapacity m), hm, ?_, ?_⟩
  · exact (Nat.le_max_left _ _).trans (Nat.le_of_lt Nat.lt_two_pow_self)
  · exact (Nat.le_max_right _ _).trans (Nat.le_of_lt Nat.lt_two_pow_self)

theorem address_fits (h : WordEligible m width capacity) (i : Fin capacity) :
    i.val < 2^width := i.isLt.trans_le h.addresses

/-- This scalar envelope includes padded lengths and additions of two padded
indices. Packed keys have their separate quadratic envelope. -/
theorem scalar_fits (h : WordEligible m width capacity) (hi : i ≤ 4*m+3) :
    i < 2^width := by
  have hk := h.keys
  unfold KeyBounds.wordCapacity at hk
  nlinarith

theorem padded_index_fits (h : WordEligible m width capacity)
    (i : Fin (paddedCapacity m)) : i.val < 2^width := by
  have hp := paddedCapacity_le h.positive
  apply scalar_fits h
  have := i.isLt
  omega

theorem query_add_fits (h : WordEligible m width capacity)
    (hi : i < paddedCapacity m) (hj : j ≤ paddedCapacity m) :
    i+j < 2^width := by
  have hp := paddedCapacity_le h.positive
  apply scalar_fits h
  omega

theorem class_count_fits (h : WordEligible m width capacity) :
    2^(blockSize m-1) < 2^width := by
  have hb := blockSize_pos m
  have he := class_entries_le h.positive
  have hs : 1 ≤ blockSize m * blockSize m := by nlinarith
  have hc := Nat.mul_le_mul_right (2^(blockSize m-1)) hs
  apply scalar_fits h
  omega

theorem sparse_eligible (h : WordEligible m width capacity)
    (hm : SparseExecution.peakSlots (blocks m) (levels m) ≤ capacity) :
    SparseExecution.Eligible (blocks m) (levels m) width capacity := by
  refine ⟨hm, h.addresses, ?_⟩
  have hp : 2^(levels m) ≤ blocks m :=
    Nat.pow_log_le_self 2 (Nat.ne_of_gt (blocks_pos m))
  have hb := blocks_le h.positive
  apply scalar_fits h
  omega

theorem micro_word_fits (h : WordEligible m width capacity)
    (code : Fin (2^(blockSize m-1))) (start len : Fin (blockSize m-1+1)) :
    (KeyBounds.encodedMicroRow code start)[len.val].val < 2^width := by
  have hb := blockSize_pos m
  exact (KeyBounds.encodedMicroRow_fits
    (show blockSize m-1+1 ≤ m by have := blockSize_le h.positive; omega)
    code start len).trans_le h.keys

example : WordEligible 1 8 128 := by constructor <;> decide
example : ¬ WordEligible 1 5 16 := by
  intro h
  have := h.keys
  norm_num [KeyBounds.wordCapacity] at this

/-- Required memory under the monotone allocation interpretation. The caller
supplies its borrowed input and separately established scalar/control frame. -/
def requiredSlots (m inputWords frameWords : Nat) : Nat :=
  retainedSlots m + Workspace.temporaryWords m + inputWords + frameWords

structure Eligible (m width capacity inputWords frameWords : Nat) : Prop
    extends WordEligible m width capacity where
  memory : requiredSlots m inputWords frameWords ≤ capacity

theorem preparation_fits (h : Eligible m width capacity inputWords frameWords)
    (source : Nat → Resources.Measured Int Nat) :
    Workspace.words (Workspace.selectedRun source m) + inputWords + frameWords ≤ capacity := by
  rw [Workspace.selectedRun_words]
  exact h.memory

/-- Every operation-produced allocation, including all retained temporaries,
fits together with the caller's separately accounted input and scalar frame. -/
theorem allocation_prefix_fits (h : Eligible m width capacity inputWords frameWords)
    (source : Nat → Resources.Measured Int Nat) (k : Nat) :
    ((Workspace.selectedRun source m).allocations.take k).sum + inputWords + frameWords ≤ capacity := by
  have hp : ((Workspace.selectedRun source m).allocations.take k).sum ≤
      (Workspace.selectedRun source m).allocations.sum := by
    have he := List.sum_take_add_sum_drop (Workspace.selectedRun source m).allocations k
    omega
  have hf := preparation_fits h source
  unfold Workspace.words at hf
  omega

theorem exists_machine (hm : 0 < m) (inputWords frameWords : Nat) :
    ∃ width capacity, Eligible m width capacity inputWords frameWords := by
  obtain ⟨width,hw⟩ := exists_width hm (requiredSlots m inputWords frameWords)
  exact ⟨width,requiredSlots m inputWords frameWords,hw,le_rfl⟩

/-- A singleton machine with four borrowed words and a sixty-four-word frame
has a concrete memory/word witness. The separate caller proves its frame use. -/
example : Eligible 1 8 128 4 64 := by
  constructor
  · constructor <;> decide
  · decide

example : ¬ Eligible 1 8 16 4 64 := by
  intro h
  have hh := h.memory
  norm_num [requiredSlots, retainedSlots, paddedCapacity, blocks,
    BlockedRMQ.blockCount, sharedSlots, levels, blockSize,
    SparseExecution.retainedSlots, Workspace.temporaryWords, Nat.log] at hh

end Sequences.LCA.MachineCapacity
