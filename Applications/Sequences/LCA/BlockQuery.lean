import Applications.Sequences.LCA.Sparse

/-! Query reconstruction from two boundary fragments and a nonempty middle
block interval. Empty middles are eliminated before querying the summary table. -/
namespace Sequences.LCA
open PreparedRMQ
variable {α : Type} [LinearOrder α]

def blockMinimum (read : Nat → α) (b block : Nat) : α :=
  rangeMin read (block*b) (b-1)

theorem rangeMin_blocks (read : Nat → α) (b start count : Nat) (hb : 0 < b) :
    rangeMin (blockMinimum read b) start count =
      rangeMin read (start*b) ((count+1)*b-1) := by
  induction count with
  | zero => simp [rangeMin, blockMinimum]
  | succ count ih =>
    rw [rangeMin, ih, blockMinimum]
    have hp : 0 < (count+1)*b := Nat.mul_pos (by omega) hb
    have hs : (start+count+1)*b = start*b+(count+1)*b := by ring
    rw [hs, ← rangeMin_split read (start*b) _ b hp hb]
    congr 1
    ring_nf

def blockedQuery (within : Nat → Nat → Nat → α) (summary : Nat → Nat → α)
    (b lo hi : Nat) : α :=
  let first := lo / b
  let last := hi / b
  if first = last then within first (lo % b) (hi-lo)
  else
    let left := within first (lo % b) (b-1-lo%b)
    let right := within last 0 (hi%b)
    if last = first+1 then min left right
    else min left (min (summary (first+1) (last-first-2)) right)

/-- The reconstruction law only asks the component operations to implement
inclusive interval minima. It can be reused by representations other than
shared ±1 tables. -/
theorem blockedQuery_correct (read : Nat → α)
    (within : Nat → Nat → Nat → α) (summary : Nat → Nat → α)
    (b lo hi : Nat) (hb : 0 < b) (hq : lo ≤ hi)
    (hw : ∀ block offset len, block ≤ hi/b → offset+len < b →
      within block offset len = rangeMin read (block*b+offset) len)
    (hm : ∀ start count, start+count < hi/b →
      summary start count = rangeMin (blockMinimum read b) start count) :
    blockedQuery within summary b lo hi = rangeMin read lo (hi-lo) := by
  have hlo : lo / b * b + lo % b = lo := by simpa [Nat.mul_comm] using Nat.div_add_mod lo b
  have hhi : hi / b * b + hi % b = hi := by simpa [Nat.mul_comm] using Nat.div_add_mod hi b
  have hlom : lo % b < b := Nat.mod_lt _ hb
  have hhim : hi % b < b := Nat.mod_lt _ hb
  have hblocks : lo / b ≤ hi / b := Nat.div_le_div_right hq
  dsimp only [blockedQuery]
  split
  · rename_i heq
    have heqm : lo/b*b = hi/b*b := congrArg (· * b) heq
    rw [hw _ _ _ hblocks (by omega), hlo]
  · rename_i hne
    have hstrict : lo / b < hi / b := by omega
    rw [hw _ _ _ hblocks (by omega), hw _ _ _ le_rfl (by omega)]
    simp only [Nat.add_zero]
    have hleft : 0 < b - lo % b := by omega
    have hright : 0 < hi % b + 1 := by omega
    have hend : lo + (b-lo%b) = (lo/b+1)*b := by
      have : (lo/b+1)*b = lo/b*b+b := by ring
      omega
    have hl : b - 1 - lo % b = (b - lo % b) - 1 := by omega
    rw [hlo, hl]
    split
    · rename_i hadj
      have hpos : hi / b * b = lo + (b-lo%b) := by rw [hadj]; omega
      rw [hpos]
      have hs := rangeMin_split read lo _ _ hleft hright
      simp only [Nat.add_sub_cancel] at hs
      rw [← hs]
      congr 1
      omega
    · rename_i hgap
      rw [hm _ _ (by omega), rangeMin_blocks _ _ _ _ hb]
      have hdiff : hi/b-lo/b-1 > 0 := by omega
      have hmid : 0 < (hi/b-lo/b-1)*b := Nat.mul_pos hdiff hb
      have hc : (hi/b-lo/b-2+1)*b = (hi/b-lo/b-1)*b := by congr 1; omega
      rw [hc]
      have hmul : (lo/b+1)*b + (hi/b-lo/b-1)*b = hi/b*b := by
        rw [← Nat.add_mul]
        congr 1
        omega
      rw [← hmul]
      have hs := rangeMin_split read ((lo/b+1)*b) _ _ hmid hright
      simp only [Nat.add_sub_cancel] at hs
      rw [← hs]
      rw [← hend, ← rangeMin_split read lo _ _ hleft (by omega)]
      congr 1
      omega

end Sequences.LCA
