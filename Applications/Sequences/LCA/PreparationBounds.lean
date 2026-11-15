import Applications.Sequences.LCA.BlockBounds
import Applications.Sequences.LCA.BlockedRMQ

/-! Arithmetic bounds for the selected block parameters. These formulas are
budgets to be connected to measured preparation and memory phases; none of the
lemmas in this module asserts that an implementation performs the operations
or has the storage lifetime described by a formula. -/
namespace Sequences.LCA.PreparationBounds

def blocks (n : Nat) : Nat := BlockedRMQ.blockCount n (blockSize n-1)
def levels (n : Nat) : Nat := Nat.log 2 (blocks n)
def paddedCapacity (n : Nat) : Nat := blocks n * blockSize n

theorem blocks_eq (hn : 0 < n) : blocks n = Sequences.LCA.blockCount n := by
  have hb := blockSize_pos n
  unfold blocks BlockedRMQ.blockCount Sequences.LCA.blockCount
  rw [show blockSize n-1+1 = blockSize n by omega]
  rw [show n+blockSize n-1 = (n-1)+blockSize n by omega, Nat.add_div_right _ hb]

theorem blocks_pos (n : Nat) : 0 < blocks n := BlockedRMQ.blockCount_pos _ _

theorem blocks_le (hn : 0 < n) : blocks n ≤ n := by
  rw [blocks_eq hn]
  exact blockCount_le hn

theorem paddedCapacity_le (hn : 0 < n) : paddedCapacity n ≤ 2*n := by
  unfold paddedCapacity
  rw [blocks_eq hn]
  have hh := blockCount_mul_le n
  have hb := blockSize_le hn
  omega

theorem paddedCapacity_covers (hn : 0 < n) : n ≤ paddedCapacity n := by
  have hh := BlockedRMQ.blockCount_covers (blockSize n-1) hn
  have hb := blockSize_pos n
  simpa only [paddedCapacity, blocks, show blockSize n-1+1 = blockSize n by omega] using hh

theorem macro_entries_le (hn : 0 < n) : blocks n*(levels n+1) ≤ 8*n := by
  simpa only [levels, blocks_eq hn] using macro_entries_linear hn

/-- The small-input branch keeps one-cell blocks. -/
theorem class_entries_le (hn : 0 < n) :
    blockSize n * blockSize n * 2^(blockSize n-1) ≤ 2*n := by
  by_cases hlarge : 4 ≤ n
  · have hp : 2^(blockSize n-1) ≤ 2^blockSize n :=
      Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.mul_le_mul_left (blockSize n * blockSize n) hp).trans
      (class_entries_linear hlarge)
  · interval_cases n <;> norm_num [blockSize, Nat.log] at *

/-- The shared-table execution tariff includes canonical heights, cumulative
rows, allocation initialization, and the surrounding index loops. -/
def sharedWork (n : Nat) : Nat := 64 * blockSize n * blockSize n * 2^(blockSize n-1)

theorem sharedWork_le (hn : 0 < n) : sharedWork n ≤ 128*n := by
  have hh := class_entries_le hn
  unfold sharedWork
  nlinarith

/-- Finite sparse execution's proven tariff evaluated at the macro dimensions. -/
def macroWork (n : Nat) : Nat :=
  14*blocks n + 3 + levels n*(11*blocks n+7)

theorem macroWork_le (hn : 0 < n) : macroWork n ≤ 200*n := by
  have he := macro_entries_le hn
  have hb := blocks_le hn
  have hp := blocks_pos n
  have hl : levels n ≤ blocks n * levels n := by
    simpa using Nat.mul_le_mul_right (levels n) hp
  unfold macroWork
  nlinarith

/-- Reading/padding each source depth costs at most eight operations; the
finite tabulation adds six. Classifying a block uses two source reads and six
other operations per step, plus its block-base multiplication and tabulation. -/
def sourceWork (n : Nat) : Nat := paddedCapacity n * 14

def classificationWork (n : Nat) : Nat := blocks n * (22*(blockSize n-1)+7)

def preparationWork (n : Nat) : Nat :=
  sourceWork n + classificationWork n + sharedWork n + 20*blocks n + macroWork n

theorem sourceWork_le (hn : 0 < n) : sourceWork n ≤ 28*n := by
  have hh := paddedCapacity_le hn
  unfold sourceWork
  omega

theorem classificationWork_le (hn : 0 < n) : classificationWork n ≤ 51*n := by
  have hh := paddedCapacity_le hn
  have hk := blocks_le hn
  have hm := Nat.mul_le_mul_left (blocks n) (show blockSize n-1 ≤ blockSize n by omega)
  unfold classificationWork paddedCapacity at *
  nlinarith

theorem preparationWork_le (hn : 0 < n) : preparationWork n ≤ 1024*n := by
  have hs := sourceWork_le hn
  have hc := classificationWork_le hn
  have ht := sharedWork_le hn
  have hm := macroWork_le hn
  have hk := blocks_le hn
  unfold preparationWork
  omega

/-- Shared keys plus one row pointer per row and one pointer per class. -/
def sharedSlots (n : Nat) : Nat :=
  2^(blockSize n-1) * (blockSize n*blockSize n + blockSize n + 1)

theorem sharedSlots_le (hn : 0 < n) : sharedSlots n ≤ 6*n := by
  have hb := blockSize_pos n
  have he := class_entries_le hn
  have hx : blockSize n + 1 ≤ 2*(blockSize n*blockSize n) := by nlinarith
  have hm := Nat.mul_le_mul_left (2^(blockSize n-1)) hx
  unfold sharedSlots
  nlinarith

theorem sparseSlots_le (hn : 0 < n) :
    SparseExecution.retainedSlots (blocks n) (levels n) ≤ 26*n := by
  have he := macro_entries_le hn
  have hb := blocks_le hn
  have hp := blocks_pos n
  have hl : levels n+1 ≤ blocks n*(levels n+1) := by
    simpa using Nat.mul_le_mul_right (levels n+1) hp
  unfold SparseExecution.retainedSlots
  nlinarith

/-- Conservatively retains the block-minimum input even though sparse
preparation owns a second copy. This avoids assuming early reclamation. -/
def retainedSlots (n : Nat) : Nat :=
  paddedCapacity n + blocks n + sharedSlots n + blocks n +
    SparseExecution.retainedSlots (blocks n) (levels n)

theorem retainedSlots_le (hn : 0 < n) : retainedSlots n ≤ 36*n := by
  have hp := paddedCapacity_le hn
  have hb := blocks_le hn
  have hs := sharedSlots_le hn
  have hm := sparseSlots_le hn
  unfold retainedSlots
  omega

/-- One temporary class-sized square, three block vectors and sixteen scalar
slots. The final machine must justify that these are its live temporaries. -/
def workspaceSlots (n : Nat) : Nat := blockSize n*blockSize n + 3*blockSize n + 16

theorem workspaceSlots_le (hn : 0 < n) : workspaceSlots n ≤ 21*n := by
  have he := class_entries_le hn
  have hb := blockSize_le hn
  have hp : 1 ≤ 2^(blockSize n-1) := Nat.one_le_two_pow
  have hm := Nat.mul_le_mul_left (blockSize n*blockSize n) hp
  unfold workspaceSlots
  nlinarith

def peakSlots (n inputSlots : Nat) : Nat := retainedSlots n + workspaceSlots n + inputSlots

theorem peakSlots_le (hn : 0 < n) (hi : inputSlots ≤ 4*n) : peakSlots n inputSlots ≤ 64*n := by
  have hr := retainedSlots_le hn
  have hw := workspaceSlots_le hn
  unfold peakSlots
  omega

example : preparationWork 1 = 122 := by decide
example : preparationWork 3 ≤ 1024*3 := preparationWork_le (by decide)
example : peakSlots 1 4 ≤ 64 := peakSlots_le (by decide) (by decide)

end Sequences.LCA.PreparationBounds
