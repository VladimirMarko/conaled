import Applications.Resources.Prepared
import Applications.Resources.BoundedSummary

namespace Resources.PreparedSummary
open Prepared Sequences.BoundedSummary Sequences.BoundedSummary.Buffer
namespace Cost
abbrev t : BoundedSummary.Tariff := {}
end Cost

def plain (N : Nat) : Ops (Buffer N) Unit Parity (Buffer N) where
  prepare b := (b,0)
  answer b _ := BoundedSummary.scanM Cost.t b.size.val b.read

def cached (N : Nat) : Ops (Buffer N) Unit Parity (Cached N) where
  prepare := BoundedSummary.convert Cost.t
  answer c _ := (c.2,1)

def PlainValid (s r : Buffer N) : Prop := r = s
def CachedValid (s : Buffer N) (r : Cached N) : Prop := r.1 = s ∧ Valid r

def meaning (s : Buffer N) (_ : Unit) := parity s.decode

theorem plain_laws : Laws (meaning (N := N)) (plain N) PlainValid where
  prepare _ := rfl
  answer s r h _ := by
    subst r
    exact congrArg Prod.fst (BoundedSummary.scanM_exact Cost.t s.size.val s.read) |>.trans (query_correct s)

theorem cached_laws : Laws (meaning (N := N)) (cached N) CachedValid where
  prepare s := by
    rw [show (cached N).prepare s = BoundedSummary.convert Cost.t s from rfl,
      BoundedSummary.convert_exact]
    exact ⟨rfl,cache_valid s⟩
  answer s r h _ := by
    change r.2 = parity s.decode
    rw [h.2.2,h.1]
    rfl

def profile (N : Nat) (cache : Bool) : Profile (Buffer N) where
  preparation b := if cache then 2*N+2*b.size.val+2 else 0
  query b := if cache then 1 else 2*b.size.val+1
  maintenance _ := if cache then 5 else 3
  retained _ := BoundedSummary.retained cache N
  peak _ := BoundedSummary.conversionWorkingPeak N + N + 1

def plainStorage (N : Nat) : Storage (Buffer N) (Buffer N) where
  retained _ := BoundedSummary.retained false N
  preparePeak _ := BoundedSummary.retained false N
  queryPeak b := BoundedSummary.operationPeak false N b.size.val

def cachedStorage (N : Nat) : Storage (Buffer N) (Cached N) where
  retained _ := BoundedSummary.retained true N
  preparePeak _ := BoundedSummary.conversionWorkingPeak N
  queryPeak _ := BoundedSummary.retained true N

theorem plain_bounds : Bounds (plain N) PlainValid (plainStorage N) (profile N false) where
  preparation _ := le_rfl
  query s r h _ := by
    subst r
    simp [plain,BoundedSummary.scanM_exact,profile,Cost.t]
    omega
  retained _ _ _ := le_rfl
  preparePeak _ := by simp [plainStorage,profile,BoundedSummary.conversionWorkingPeak,
    BoundedSummary.conversionPeak,BoundedSummary.retained,BoundedSummary.scanFrames]
  queryPeak s r h := by
    have := r.size.isLt
    simp [plainStorage,profile,BoundedSummary.operationPeak,BoundedSummary.conversionWorkingPeak,
      BoundedSummary.conversionPeak,BoundedSummary.retained,BoundedSummary.scanFrames]
    omega

theorem cached_bounds : Bounds (cached N) CachedValid (cachedStorage N) (profile N true) where
  preparation b := by
    simp [cached,BoundedSummary.convert_exact,profile,Cost.t] <;> omega
  query _ _ _ _ := le_rfl
  retained _ _ _ := le_rfl
  preparePeak _ := by simp [cachedStorage,profile] <;> omega
  queryPeak _ _ _ := by
    simp [cachedStorage,profile,BoundedSummary.conversionWorkingPeak,
      BoundedSummary.conversionPeak,BoundedSummary.retained,BoundedSummary.scanFrames]

/-- Overflow is a specified no-op, so maintenance covers capacity boundaries. -/
def update (b : Buffer N) (x : Bool) := (tryPush b x).1

def plainMaintenance : Maintenance (plain N) PlainValid (profile N false) update where
  run b x := ((tryPush b x).1,BoundedSummary.charge false Cost.t N (.append x) b.size.val)
  valid s r h x := by subst r; rfl
  bound s r _ x := by
    simp [BoundedSummary.charge,profile,Cost.t]; split <;> omega

def cachedMaintenance : Maintenance (cached N) CachedValid (profile N true) update where
  run c x := ((cachedPush c x).1,BoundedSummary.charge true Cost.t N (.append x) c.1.size.val)
  valid s r h x := by
    refine ⟨?_,cachedPush_valid h.2 x⟩
    simp only [cachedPush,update,tryPush]
    rw [h.1]
    split
    · rfl
    · exact h.1
  bound s r _ x := by
    simp [BoundedSummary.charge,profile,Cost.t]; split <;> omega

end Resources.PreparedSummary
