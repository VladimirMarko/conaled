import Applications.Sequences.LCA.PreparationBounds
import Applications.Sequences.LCA.WordKeyStorage

/-! Bounds on keys in the actual shared and macro arrays, including cells
outside admitted query intervals. The word-store interpretation preserves
key order and exact leftmost identity through WordKeyStorage. -/
namespace Sequences.LCA.KeyBounds
open PreparedRMQ
abbrev Key := Int ×ₗ Nat

def Fits (offset : Int) (heights stride : Nat) (key : Key) : Prop :=
  0 ≤ (ofLex key).1 + offset ∧ (ofLex key).1 + offset < (heights : Int) ∧
    (ofLex key).2 < stride

theorem fits_min (ha : Fits offset heights stride a) (hb : Fits offset heights stride b) :
    Fits offset heights stride (min a b) := by
  by_cases h : a ≤ b
  · simpa only [min_eq_left h] using ha
  · simpa only [min_eq_right (le_of_not_ge h)] using hb

/-- Beyond its last step the canonical walk remains constant. -/
theorem relative_bounds (shape : Shape steps) (i : Nat) :
    -(↑(min i steps) : Int) ≤ relative shape i ∧ relative shape i ≤ (↑(min i steps) : Int) := by
  induction i with
  | zero => simp [relative]
  | succ i ih =>
    by_cases hi : i < steps
    · have hm : min i steps = i := Nat.min_eq_left (by omega)
      have hm' : min (i+1) steps = i+1 := Nat.min_eq_left (by omega)
      simp only [hm] at ih
      simp only [relative, hi, dite_true, hm']
      cases shape ⟨i,hi⟩ <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    · have hm : min i steps = steps := Nat.min_eq_right (by omega)
      have hm' : min (i+1) steps = steps := Nat.min_eq_right (by omega)
      simpa only [relative, hi, dite_false, hm, hm', add_zero] using ih

theorem canonical_bounds (steps code i : Nat) :
    -(steps : Int) ≤ boundedDepth (canonicalHeights steps code) i ∧
      boundedDepth (canonicalHeights steps code) i ≤ (steps : Int) := by
  simp only [boundedDepth, canonicalHeights, vectorGet_ofFn]
  have hh := relative_bounds (decodeShape steps code) (min i steps)
  have hm : min (min i steps) steps ≤ steps := Nat.min_le_right _ _
  omega

theorem classCell_fits (steps code : Nat) (start len : Fin (steps+1)) :
    Fits (steps : Int) (2*steps+1) (2*(steps+1))
      (((buildClass (canonicalHeights steps code)).get start).get len) := by
  simp only [buildClass, vectorGet_ofFn, prefixRow_get]
  obtain ⟨i, hi, he⟩ := rangeMin_occurs
    (depthKey (boundedDepth (canonicalHeights steps code))) start.val len.val
  rw [he]
  have hh := canonical_bounds steps code (start.val+i)
  simp only [Fits, depthKey, ofLex_toLex]
  constructor
  · omega
  constructor
  · omega
  · have := start.isLt; have := len.isLt; omega

theorem sharedCell_fits (code : Fin (2^steps)) (start len : Fin (steps+1)) :
    Fits (steps : Int) (2*steps+1) (2*(steps+1))
      ((((prepareShared steps).get code).get start).get len) := by
  simpa only [prepareShared, vectorGet_ofFn] using classCell_fits steps code.val start len

def microCells (code : Fin (2^steps)) (start : Fin (steps+1)) :
    Vector (WordKey.Cell (steps : Int) (2*steps+1) (2*(steps+1))) (steps+1) :=
  Vector.ofFn fun len =>
    ⟨((((prepareShared steps).get code).get start).get len), sharedCell_fits code start len⟩

def encodedMicroRow (code : Fin (2^steps)) (start : Fin (steps+1)) :
    Vector (Fin ((2*steps+1)*(2*(steps+1)))) (steps+1) :=
  WordKey.encodeStore (microCells code start)

theorem encodedMicroRow_read (code : Fin (2^steps)) (start len : Fin (steps+1)) :
    (encodedMicroRow code start)[len.val].val =
      WordKey.encode (steps : Int) (2*(steps+1))
        (ofLex ((((prepareShared steps).get code).get start).get len)).1
        (ofLex ((((prepareShared steps).get code).get start).get len)).2 := by
  simp [encodedMicroRow, WordKey.encodeStore, microCells, WordKey.cellWord, Vector.get]

theorem paddedDepth_bounds (depth : Nat → Int) (hn : 0 < n)
    (hdepth : ∀ i, i < n → 0 ≤ depth i ∧ depth i < (n : Int))
    (hcap : capacity ≤ 2*n) (hi : i < capacity) :
    0 ≤ paddedDepth depth n i ∧ paddedDepth depth n i < (2*n : Nat) := by
  by_cases hin : i < n
  · rw [paddedDepth_eq depth hin]
    have hh := hdepth i hin
    omega
  · have hh := hdepth (n-1) (by omega)
    simp only [paddedDepth, hin, ite_false]
    omega

theorem paddedKey_fits (depth : Nat → Int) (hn : 0 < n)
    (hdepth : ∀ i, i < n → 0 ≤ depth i ∧ depth i < (n : Int))
    (hcap : capacity ≤ 2*n) (hi : i < capacity) :
    Fits 0 (2*n) capacity (depthKey (paddedDepth depth n) i) := by
  have hh := paddedDepth_bounds depth hn hdepth hcap hi
  simpa only [Fits, depthKey, ofLex_toLex, add_zero] using ⟨hh.1,hh.2,hi⟩

theorem rangeMin_fits (read : Nat → Key)
    (h : ∀ i, i ≤ len → Fits offset heights stride (read (start+i))) :
    Fits offset heights stride (rangeMin read start len) := by
  obtain ⟨i, hi, he⟩ := rangeMin_occurs read start len
  rw [he]
  exact h i hi

theorem blockMinima_fits (depth : Nat → Int) (hb : 0 < blocks)
    (hsteps : ∀ block, block < blocks → UnitSteps steps (fun i => depth (block*(steps+1)+i)))
    (hdepth : ∀ i, i < blocks*(steps+1) → Fits offset heights stride (depthKey depth i))
    (block : Fin blocks) :
    Fits offset heights stride
      (BlockedRMQ.blockMinima (BlockedRMQ.buildMicro depth steps blocks) hb)[block.val] := by
  rw [BlockedRMQ.blockMinima_build depth hb hsteps block]
  unfold blockMinimum
  apply rangeMin_fits
  intro i hi
  apply hdepth
  have hm := Nat.mul_le_mul_right (steps+1) (show block.val+1 ≤ blocks by omega)
  simp only [Nat.add_sub_cancel] at hi
  nlinarith [block.isLt]

theorem finiteRow_fits (input : Vector Key n)
    (hinput : ∀ i : Fin n, Fits offset heights stride input[i.val])
    (level : Nat) (i : Fin n) : Fits offset heights stride (finiteRow input level)[i.val] := by
  induction level generalizing i with
  | zero => exact hinput i
  | succ level ih =>
    simp only [finiteRow, nextSparseRow, Vector.getElem_ofFn]
    exact fits_min (ih i) (ih ⟨(i.val+2^level)%n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

theorem sparseCell_fits (input : Vector Key n)
    (hinput : ∀ i : Fin n, Fits offset heights stride input[i.val])
    (level : Fin (levels+1)) (i : Fin n) :
    Fits offset heights stride ((buildSparse input levels)[level.val])[i.val] := by
  rw [buildSparse_get input levels level]
  exact finiteRow_fits input hinput level.val i

def sparseCells (input : Vector Key n)
    (hinput : ∀ i : Fin n, Fits offset heights stride input[i.val])
    (level : Fin (levels+1)) : Vector (WordKey.Cell offset heights stride) n :=
  Vector.ofFn fun i => ⟨((buildSparse input levels)[level.val])[i.val],
    sparseCell_fits input hinput level i⟩

def encodedSparseRow (input : Vector Key n)
    (hinput : ∀ i : Fin n, Fits offset heights stride input[i.val])
    (level : Fin (levels+1)) : Vector (Fin (heights*stride)) n :=
  WordKey.encodeStore (sparseCells input hinput level)

theorem encodedSparseRow_read (input : Vector Key n)
    (hinput : ∀ i : Fin n, Fits offset heights stride input[i.val])
    (level : Fin (levels+1)) (i : Fin n) :
    (encodedSparseRow input hinput level)[i.val].val =
      WordKey.encode offset stride (ofLex ((buildSparse input levels)[level.val])[i.val]).1
        (ofLex ((buildSparse input levels)[level.val])[i.val]).2 := by
  simp [encodedSparseRow, WordKey.encodeStore, sparseCells, WordKey.cellWord]

theorem paddedDepths_bounds (depth : Nat → Int) (hn : 0 < n)
    (hdepth : ∀ i, i < n → 0 ≤ depth i ∧ depth i < (n : Int))
    (hcap : blocks*(steps+1) ≤ 2*n) (i : Fin (blocks*(steps+1))) :
    0 ≤ (BlockedRMQ.buildMicro (paddedDepth depth n) steps blocks).depths[i.val] ∧
      (BlockedRMQ.buildMicro (paddedDepth depth n) steps blocks).depths[i.val] < (2*n : Nat) := by
  simp only [BlockedRMQ.buildMicro, Vector.getElem_ofFn]
  exact paddedDepth_bounds depth hn hdepth hcap i.isLt

theorem paddedBlockMinima_fits (depth : Nat → Int) (hn : 0 < n) (hb : 0 < blocks)
    (hsteps : UnitSteps (n-1) depth)
    (hdepth : ∀ i, i < n → 0 ≤ depth i ∧ depth i < (n : Int))
    (hcap : blocks*(steps+1) ≤ 2*n) (block : Fin blocks) :
    Fits 0 (2*n) (blocks*(steps+1))
      (BlockedRMQ.blockMinima (BlockedRMQ.buildMicro (paddedDepth depth n) steps blocks) hb)[block.val] := by
  apply blockMinima_fits _ hb _ _ block
  · intro block _
    simpa only [Nat.add_sub_cancel] using padded_block_steps depth hn hsteps block (steps+1)
  · intro i hi
    exact paddedKey_fits depth hn hdepth hcap hi

/-- This covers every retained macro row cell, including wrapped tail cells
that are never read by a valid sparse-table query. -/
theorem macroCell_fits (depth : Nat → Int) (hn : 0 < n) (hb : 0 < blocks)
    (hsteps : UnitSteps (n-1) depth)
    (hdepth : ∀ i, i < n → 0 ≤ depth i ∧ depth i < (n : Int))
    (hcap : blocks*(steps+1) ≤ 2*n) (level : Fin (levels+1)) (i : Fin blocks) :
    Fits 0 (2*n) (blocks*(steps+1))
      (((BlockedRMQ.build (paddedDepth depth n) steps blocks hb levels).macroRows[level.val]).1)[i.val] := by
  simp only [BlockedRMQ.build, SparseExecution.prepare, Resources.bind, Resources.pure]
  simp only [SparseExecution.build_get _ _ levels level]
  exact finiteRow_fits _ (paddedBlockMinima_fits depth hn hb hsteps hdepth hcap) level.val i

def macroCells (depth : Nat → Int) (hn : 0 < n) (hb : 0 < blocks)
    (hsteps : UnitSteps (n-1) depth)
    (hdepth : ∀ i, i < n → 0 ≤ depth i ∧ depth i < (n : Int))
    (hcap : blocks*(steps+1) ≤ 2*n) (level : Fin (levels+1)) :
    Vector (WordKey.Cell 0 (2*n) (blocks*(steps+1))) blocks :=
  Vector.ofFn fun i =>
    ⟨(((BlockedRMQ.build (paddedDepth depth n) steps blocks hb levels).macroRows[level.val]).1)[i.val],
      macroCell_fits depth hn hb hsteps hdepth hcap level i⟩

def encodedMacroRow (depth : Nat → Int) (hn : 0 < n) (hb : 0 < blocks)
    (hsteps : UnitSteps (n-1) depth)
    (hdepth : ∀ i, i < n → 0 ≤ depth i ∧ depth i < (n : Int))
    (hcap : blocks*(steps+1) ≤ 2*n) (level : Fin (levels+1)) :
    Vector (Fin ((2*n)*(blocks*(steps+1)))) blocks :=
  WordKey.encodeStore (macroCells depth hn hb hsteps hdepth hcap level)

theorem encodedMacroRow_read (depth : Nat → Int) (hn : 0 < n) (hb : 0 < blocks)
    (hsteps : UnitSteps (n-1) depth)
    (hdepth : ∀ i, i < n → 0 ≤ depth i ∧ depth i < (n : Int))
    (hcap : blocks*(steps+1) ≤ 2*n) (level : Fin (levels+1)) (i : Fin blocks) :
    (encodedMacroRow depth hn hb hsteps hdepth hcap level)[i.val].val =
      WordKey.encode 0 (blocks*(steps+1))
        (ofLex (((BlockedRMQ.build (paddedDepth depth n) steps blocks hb levels).macroRows[level.val]).1)[i.val]).1
        (ofLex (((BlockedRMQ.build (paddedDepth depth n) steps blocks hb levels).macroRows[level.val]).1)[i.val]).2 := by
  simp [encodedMacroRow, WordKey.encodeStore, macroCells, WordKey.cellWord]

/-- One common rectangle bound covers canonical signed keys and absolute
padded keys. A word width whose capacity exceeds this bound is sufficient. -/
def wordCapacity (n : Nat) : Nat := (4*n+4)^2

theorem micro_capacity_le (hb : b ≤ n) :
    (2*(b-1)+1)*(2*b) ≤ wordCapacity n := by
  unfold wordCapacity
  nlinarith [Nat.sub_le b 1]

theorem macro_capacity_le (hp : capacity ≤ 2*n) :
    (2*n)*capacity ≤ wordCapacity n := by
  unfold wordCapacity
  nlinarith

theorem encodedMicroRow_fits (hsize : steps+1 ≤ n)
    (code : Fin (2^steps)) (start len : Fin (steps+1)) :
    (encodedMicroRow code start)[len.val].val < wordCapacity n := by
  have hh := micro_capacity_le hsize
  simp only [Nat.add_sub_cancel] at hh
  exact ((encodedMicroRow code start)[len.val]).isLt.trans_le hh

theorem encodedMacroRow_fits (depth : Nat → Int) (hn : 0 < n) (hb : 0 < blocks)
    (hsteps : UnitSteps (n-1) depth)
    (hdepth : ∀ i, i < n → 0 ≤ depth i ∧ depth i < (n : Int))
    (hcap : blocks*(steps+1) ≤ 2*n) (level : Fin (levels+1)) (i : Fin blocks) :
    (encodedMacroRow depth hn hb hsteps hdepth hcap level)[i.val].val < wordCapacity n :=
  ((encodedMacroRow depth hn hb hsteps hdepth hcap level)[i.val]).isLt.trans_le
    (macro_capacity_le hcap)

/-- Decoding the stored relative index preserves every micro cell, including
unused tails; admitted queries get their original exact argmin witness. -/
theorem encodedMicroRow_index (code : Fin (2^steps)) (start len : Fin (steps+1)) :
    (encodedMicroRow code start)[len.val].val % (2*(steps+1)) =
      (ofLex ((((prepareShared steps).get code).get start).get len)).2 := by
  rw [encodedMicroRow_read]
  exact WordKey.pack_mod (sharedCell_fits code start len).2.2

theorem encodedMacroRow_index (depth : Nat → Int) (hn : 0 < n) (hb : 0 < blocks)
    (hsteps : UnitSteps (n-1) depth)
    (hdepth : ∀ i, i < n → 0 ≤ depth i ∧ depth i < (n : Int))
    (hcap : blocks*(steps+1) ≤ 2*n) (level : Fin (levels+1)) (i : Fin blocks) :
    (encodedMacroRow depth hn hb hsteps hdepth hcap level)[i.val].val % (blocks*(steps+1)) =
      (ofLex (((BlockedRMQ.build (paddedDepth depth n) steps blocks hb levels).macroRows[level.val]).1)[i.val]).2 := by
  rw [encodedMacroRow_read]
  exact WordKey.pack_mod (macroCell_fits depth hn hb hsteps hdepth hcap level i).2.2

/-- Store reads and minimum reuse the word interpretation's local law. -/
theorem encodedMicroRow_min (code : Fin (2^steps)) (start i j : Fin (steps+1)) :
    min (encodedMicroRow code start)[i.val] (encodedMicroRow code start)[j.val] =
      WordKey.cellWord (min (microCells code start)[i.val] (microCells code start)[j.val]) :=
  WordKey.encodeStore_read_min _ i j

theorem encodedMacroRow_min (depth : Nat → Int) (hn : 0 < n) (hb : 0 < blocks)
    (hsteps : UnitSteps (n-1) depth)
    (hdepth : ∀ i, i < n → 0 ≤ depth i ∧ depth i < (n : Int))
    (hcap : blocks*(steps+1) ≤ 2*n) (level : Fin (levels+1)) (i j : Fin blocks) :
    min (encodedMacroRow depth hn hb hsteps hdepth hcap level)[i.val]
      (encodedMacroRow depth hn hb hsteps hdepth hcap level)[j.val] =
      WordKey.cellWord (min (macroCells depth hn hb hsteps hdepth hcap level)[i.val]
        (macroCells depth hn hb hsteps hdepth hcap level)[j.val]) :=
  WordKey.encodeStore_read_min _ i j

example : (encodedMicroRow (steps := 2) 1 1)[(1 : Fin 3).val].val = 14 := by
  rw [encodedMicroRow_read (steps := 2) 1 1 1]
  decide

/-- The unused tail of a shared row is also an encodable stored key. -/
example : (encodedMicroRow (steps := 2) 1 2)[(2 : Fin 3).val].val = 14 := by
  rw [encodedMicroRow_read (steps := 2) 1 2 2]
  decide

/-- Negative canonical depth -2 is translated to nonnegative height zero. -/
example : (encodedMicroRow (steps := 2) 0 0)[(2 : Fin 3).val].val = 2 := by
  rw [encodedMicroRow_read (steps := 2) 0 0 2]
  decide

private def smallDepth (i : Nat) : Int := if i = 1 then 0 else 1
private theorem smallSteps : UnitSteps (3-1) smallDepth := by
  intro i hi
  interval_cases i <;> decide
private theorem smallBounds : ∀ i, i < 3 → 0 ≤ smallDepth i ∧ smallDepth i < (3 : Int) := by
  intro i _
  unfold smallDepth
  split_ifs <;> omega

/-- The second cell of macro level one wraps to the first block. It is an
unused sparse-query tail cell, but its key is still bounded and encodable. -/
example :
    (encodedMacroRow (steps := 1) (blocks := 2) smallDepth (by decide) (by decide)
      smallSteps smallBounds (by decide) (1 : Fin 2))[(1 : Fin 2).val].val = 1 := by
  rw [encodedMacroRow_read smallDepth (by decide) (by decide) smallSteps smallBounds
    (show 2*(1+1) ≤ 2*3 by decide) (1 : Fin 2) (1 : Fin 2)]
  decide

end Sequences.LCA.KeyBounds
