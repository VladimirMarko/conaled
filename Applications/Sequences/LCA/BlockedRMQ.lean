import Applications.Sequences.LCA.BlockQuery
import Applications.Sequences.LCA.Padding
import Applications.Sequences.LCA.SharedTable
import Applications.Sequences.LCA.SparseExecution
import Applications.Sequences.LCA.ArgminTransport

/-! Complete static blocked RMQ representation. The shared micro tables retain
relative leftmost argmin indices; the macro sparse table stores absolute keys,
so ties across different blocks also choose the first input position. -/
namespace Sequences.LCA.BlockedRMQ
open PreparedRMQ
abbrev Key := Int ×ₗ Nat

structure MicroData (steps blocks : Nat) where
  depths : Vector Int (blocks*(steps+1))
  classes : Vector (Fin (2^steps)) blocks
  shared : SharedTable steps

def buildMicro (depth : Nat → Int) (steps blocks : Nat) : MicroData steps blocks where
  depths := Vector.ofFn fun i => depth i.val
  classes := Vector.ofFn fun block => classAddress steps (fun i => depth (block.val*(steps+1)+i))
  shared := prepareShared steps

def readDepth (data : MicroData steps blocks) (hb : 0 < blocks) (i : Nat) : Int :=
  data.depths[min i (blocks*(steps+1)-1)]'(by
    have hp : 0 < blocks*(steps+1) := Nat.mul_pos hb (by omega)
    omega)

theorem readDepth_build (depth : Nat → Int) (hb : 0 < blocks)
    (hi : i < blocks*(steps+1)) :
    readDepth (buildMicro depth steps blocks) hb i = depth i := by
  simp [readDepth, buildMicro, min_eq_left (show i ≤ blocks*(steps+1)-1 by omega)]

/-- Total callbacks use clipped addresses, which are inactive on admitted
queries. The local shared answer is translated to an absolute key. -/
def within (data : MicroData steps blocks) (hb : 0 < blocks)
    (block offset len : Nat) : Key :=
  let code := data.classes[min block (blocks-1)]'(by omega)
  let relativeIndex := lookupShared data.shared code ⟨min offset steps, by omega⟩ ⟨min len steps, by omega⟩
  let global := block*(steps+1)+relativeIndex
  depthKey (readDepth data hb) global

theorem within_build (depth : Nat → Int) (hb : 0 < blocks)
    (hsteps : ∀ block, block < blocks → UnitSteps steps (fun i => depth (block*(steps+1)+i)))
    (hblock : block < blocks) (hi : offset+len ≤ steps) :
    within (buildMicro depth steps blocks) hb block offset len =
      rangeMin (depthKey depth) (block*(steps+1)+offset) len := by
  have ho : offset ≤ steps := by omega
  have hl : len ≤ steps := by omega
  simp only [within, buildMicro, Vector.getElem_ofFn,
    min_eq_left (show block ≤ blocks-1 by omega), min_eq_left ho, min_eq_left hl]
  rw [lookupShared_correct _ (hsteps block hblock) ⟨offset, by omega⟩ ⟨len, by omega⟩ hi]
  have ha := argmin_correct (fun i => depth (block*(steps+1)+i)) offset len
  have hg : block*(steps+1)+argmin (fun i => depth (block*(steps+1)+i)) offset len <
      blocks*(steps+1) := by
    have hm := Nat.mul_le_mul_right (steps+1) (show block+1 ≤ blocks by omega)
    nlinarith [ha.2.1]
  rw [rangeMin_depthKey]
  rw [argmin_shift]
  unfold depthKey
  congr 1
  congr 1
  apply readDepth_build depth hb
  simpa only [argmin_shift] using hg

def blockMinima (data : MicroData steps blocks) (hb : 0 < blocks) : Vector Key blocks :=
  Vector.ofFn fun block => within data hb block.val 0 steps

structure Data (steps blocks levels : Nat) where
  micro : MicroData steps blocks
  macroRows : Vector (Vector Key blocks × Nat) (levels+1)
  macroLogs : Vector Nat (blocks+1)

def build (depth : Nat → Int) (steps blocks : Nat) (hb : 0 < blocks)
    (levels : Nat := Nat.log 2 blocks) : Data steps blocks levels :=
  let micro := buildMicro depth steps blocks
  let tables := (SparseExecution.prepare (toLex (0,0)) (blockMinima micro hb) levels).1
  ⟨micro, tables.1, tables.2⟩

def summary (data : Data steps blocks levels) (hb : 0 < blocks) (start count : Nat) : Key :=
  (SparseExecution.query data.macroRows data.macroLogs
    ⟨min start (blocks-1), by omega⟩ ⟨min (count+1) blocks, by omega⟩).1

def queryKey (data : Data steps blocks levels) (hb : 0 < blocks) (lo hi : Nat) : Key :=
  blockedQuery (within data.micro hb) (summary data hb) (steps+1) lo hi

def query (data : Data steps blocks levels) (hb : 0 < blocks) (lo hi : Nat) : Nat :=
  (ofLex (queryKey data hb lo hi)).2

theorem blockMinima_build (depth : Nat → Int) (hb : 0 < blocks)
    (hsteps : ∀ block, block < blocks → UnitSteps steps (fun i => depth (block*(steps+1)+i)))
    (block : Fin blocks) :
    (blockMinima (buildMicro depth steps blocks) hb)[block.val] =
      blockMinimum (depthKey depth) (steps+1) block.val := by
  simp only [blockMinima, Vector.getElem_ofFn]
  rw [within_build depth hb hsteps block.isLt (by omega)]
  simp [blockMinimum]

theorem summary_build (depth : Nat → Int) (hb : 0 < blocks)
    (hsteps : ∀ block, block < blocks → UnitSteps steps (fun i => depth (block*(steps+1)+i)))
    (hk : Nat.log 2 blocks ≤ levels) (hbound : start+count < blocks) :
    summary (build depth steps blocks hb levels) hb start count =
      rangeMin (blockMinimum (depthKey depth) (steps+1)) start count := by
  simp only [summary, build, min_eq_left (show start ≤ blocks-1 by omega),
    min_eq_left (show count+1 ≤ blocks by omega)]
  rw [SparseExecution.query_prepared _ _ levels ⟨start, by omega⟩ ⟨count+1, by omega⟩
    (by change 0 < count+1; omega) (by change start+(count+1) ≤ blocks; omega) hk]
  simp only [Nat.add_sub_cancel]
  apply rangeMin_congr_interval
  intro i hi
  have hj : start+i < blocks := by omega
  simp only [vectorRead, Nat.mod_eq_of_lt hj]
  exact blockMinima_build depth hb hsteps ⟨start+i,hj⟩

theorem queryKey_build (depth : Nat → Int) (hb : 0 < blocks)
    (hsteps : ∀ block, block < blocks → UnitSteps steps (fun i => depth (block*(steps+1)+i)))
    (hk : Nat.log 2 blocks ≤ levels) (hq : lo ≤ hi) (hhi : hi < blocks*(steps+1)) :
    queryKey (build depth steps blocks hb levels) hb lo hi =
      rangeMin (depthKey depth) lo (hi-lo) := by
  have hbhi : hi/(steps+1) < blocks := (Nat.div_lt_iff_lt_mul (by omega)).mpr hhi
  apply blockedQuery_correct _ _ _ (steps+1) lo hi (by omega) hq
  · intro block offset len hblock hinterval
    exact within_build depth hb hsteps (by omega) (by omega)
  · intro start count hbound
    exact summary_build depth hb hsteps hk (by omega)

theorem query_build (depth : Nat → Int) (hb : 0 < blocks)
    (hsteps : ∀ block, block < blocks → UnitSteps steps (fun i => depth (block*(steps+1)+i)))
    (hk : Nat.log 2 blocks ≤ levels) (hq : lo ≤ hi) (hhi : hi < blocks*(steps+1)) :
    LeftmostMinimum depth lo hi (query (build depth steps blocks hb levels) hb lo hi) := by
  unfold query
  rw [queryKey_build depth hb hsteps hk hq hhi]
  have he : lo+(hi-lo) = hi := by omega
  simpa only [argmin, he] using argmin_correct depth lo (hi-lo)

/-- For nonempty inputs this is ceil(n/(steps+1)). The final block may be
short; upward padding completes its class without adding admitted queries. -/
def blockCount (n steps : Nat) : Nat := (n-1)/(steps+1)+1

theorem blockCount_pos (n steps : Nat) : 0 < blockCount n steps := by
  exact Nat.zero_lt_succ _

theorem blockCount_covers (steps : Nat) (hn : 0 < n) : n ≤ blockCount n steps*(steps+1) := by
  have hh : (n-1)/(steps+1) < blockCount n steps := Nat.lt_succ_self _
  have hh' := (Nat.div_lt_iff_lt_mul (show 0 < steps+1 by omega)).mp hh
  omega

def buildPadded (depth : Nat → Int) (n steps : Nat) :
    Data steps (blockCount n steps) (Nat.log 2 (blockCount n steps)) :=
  build (paddedDepth depth n) steps (blockCount n steps) (blockCount_pos n steps)

theorem query_padded (depth : Nat → Int) (hn : 0 < n) (h : UnitSteps (n-1) depth)
    (steps : Nat) (hq : lo ≤ hi) (hhi : hi < n) :
    LeftmostMinimum depth lo hi
      (query (buildPadded depth n steps) (blockCount_pos n steps) lo hi) := by
  apply leftmostMinimum_congr (paddedDepth depth n) depth
  · intro i hil hih
    exact paddedDepth_eq depth (by omega)
  · have hs : ∀ block, block < blockCount n steps →
        UnitSteps steps (fun i => paddedDepth depth n (block*(steps+1)+i)) := by
      intro block _
      simpa only [Nat.add_sub_cancel] using padded_block_steps depth hn h block (steps+1)
    exact query_build _ _ hs le_rfl hq (by have hh := blockCount_covers steps hn; omega)

theorem query_padded_eq (depth : Nat → Int) (hn : 0 < n) (h : UnitSteps (n-1) depth)
    (steps : Nat) (hq : lo ≤ hi) (hhi : hi < n) :
    query (buildPadded depth n steps) (blockCount_pos n steps) lo hi = argmin depth lo (hi-lo) := by
  apply leftmostMinimum_unique depth (lo := lo) (hi := hi)
  · exact query_padded depth hn h steps hq hhi
  · simpa only [show lo+(hi-lo) = hi by omega] using argmin_correct depth lo (hi-lo)

private def exampleDepth : Nat → Int
  | 0 => 2
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | _ => 0

private theorem exampleSteps : UnitSteps (5-1) exampleDepth := by
  intro i hi
  interval_cases i <;> decide

/-- Three blocks, a nonempty macro middle, duplicate minima in distinct blocks,
and a short final block. The answer is the first of the tied zero depths. -/
example : query (buildPadded exampleDepth 5 1) (blockCount_pos 5 1) 0 4 = 2 := by
  rw [query_padded_eq exampleDepth (by decide) exampleSteps 1 (by decide) (by decide)]
  decide

/-- The adjacent-block route includes the final original position. -/
example : query (buildPadded exampleDepth 5 1) (blockCount_pos 5 1) 3 4 = 4 := by
  rw [query_padded_eq exampleDepth (by decide) exampleSteps 1 (by decide) (by decide)]
  decide

/-- Equal endpoints take the shared within-block route. -/
example : query (buildPadded exampleDepth 5 1) (blockCount_pos 5 1) 3 3 = 3 := by
  rw [query_padded_eq exampleDepth (by decide) exampleSteps 1 (by decide) (by decide)]
  decide

example : query (buildPadded (fun _ => 7) 1 0) (blockCount_pos 1 0) 0 0 = 0 := by
  rw [query_padded_eq (fun _ => 7) (by decide) (by intro i hi; omega) 0 (by decide) (by decide)]
  decide

end Sequences.LCA.BlockedRMQ
