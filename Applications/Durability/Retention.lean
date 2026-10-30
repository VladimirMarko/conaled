import SquareKit.InteractionContracts
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

/-! Finite-lifetime retained Boolean histories. Histories in `Represents` are
specification witnesses; `Snapshot` contains only the retained suffix. -/
namespace Durability.Retention

def parity : List Bool → Bool
  | [] => false
  | b :: bs => xor b (parity bs)

@[simp] theorem parity_append (xs ys : List Bool) :
    parity (xs ++ ys) = xor (parity xs) (parity ys) := by
  induction xs with
  | nil => simp [parity]
  | cons b bs ih => simp only [List.cons_append, parity, ih]; cases b <;>
      cases (parity bs) <;> cases (parity ys) <;> rfl

structure Config where
  incarnation : Nat
  window : Nat
  limit : Nat
  positive : 0 < window
  bounded : window ≤ limit

structure Snapshot where
  position : Nat
  pastParity : Bool
  items : List Bool
  deriving DecidableEq, Repr

def Snapshot.lower (s : Snapshot) : Nat := s.position - s.items.length

def Snapshot.total (s : Snapshot) : Bool := xor s.pastParity (parity s.items)

def empty : Snapshot := ⟨0, false, []⟩

/-- No full history occurs in the stored snapshot. The existential prefix is
proof-side evidence for discarded effects. -/
def Represents (c : Config) (s : Snapshot) (history : List Bool) : Prop :=
  s.position = history.length ∧ s.position ≤ c.limit ∧
  s.items.length = min c.window s.position ∧
  ∃ pastParity, history = pastParity ++ s.items ∧ s.pastParity = parity pastParity

theorem represents_empty (c : Config) : Represents c empty [] := by
  simp [Represents, empty, parity]

/-- One append trims the oldest excess and folds it into the prefix summary. -/
def append (c : Config) (s : Snapshot) (p : Bool) : Snapshot :=
  let all := s.items ++ [p]
  let excess := all.length - c.window
  ⟨s.position + 1, xor s.pastParity (parity (all.take excess)), all.drop excess⟩

theorem append_represents {c : Config} {s : Snapshot} {h : List Bool}
    (r : Represents c s h) (room : s.position < c.limit) (p : Bool) :
    Represents c (append c s p) (h ++ [p]) := by
  obtain ⟨hn, hk, hl, pre, he, hp⟩ := r
  refine ⟨by simp [append, hn], by dsimp [append]; omega, ?_, ?_⟩
  · simp only [append, List.length_drop, List.length_append, List.length_singleton]
    have := c.positive
    omega
  · refine ⟨pre ++ (s.items ++ [p]).take ((s.items ++ [p]).length - c.window), ?_, ?_⟩
    · simp only [append, he, List.append_assoc, List.take_append_drop]
    · simp [append, hp]

theorem Represents.total {c : Config} {s : Snapshot} {h : List Bool}
    (r : Represents c s h) : s.total = parity h := by
  obtain ⟨_, _, _, pre, rfl, hp⟩ := r
  simp [Snapshot.total, hp]

theorem Represents.suffix {c : Config} {s : Snapshot} {h : List Bool}
    (r : Represents c s h) : h.drop s.lower = s.items := by
  obtain ⟨hn, _, _, pre, rfl, _⟩ := r
  have eq : s.lower = pre.length := by simp [Snapshot.lower, hn]
  simp [eq]

theorem Represents.lower {c : Config} {s : Snapshot} {h : List Bool}
    (r : Represents c s h) : s.lower = h.length - c.window := by
  dsimp [Snapshot.lower]
  rw [r.1, r.2.2.1, r.1]
  omega

def range (s : Snapshot) (a z : Nat) : List Bool :=
  (s.items.drop (a - s.lower)).take (z - a)

theorem Represents.range {c : Config} {s : Snapshot} {h : List Bool}
    (r : Represents c s h) {a z : Nat} (admitted : s.lower ≤ a) :
    range s a z = (h.drop a).take (z - a) := by
  rw [Durability.Retention.range, ← r.suffix, List.drop_drop]
  congr 2
  omega

inductive Reply where
  | unavailable | busy | invalidRange | expired (lower : Nat)
  | wrongIncarnation | invalidID | outOfOrder (next : Nat) | exhausted
  | conflict | acknowledged (incarnation id : Nat) | reserved
  | records (items : List Bool) | summary (incarnation position : Nat) (parity : Bool)
  | pinned | released | invalidHandle | notReady
  deriving DecidableEq, Repr

/-- Wire IDs outside 0..K are rejected, never reduced modulo a word size. -/
def classify (c : Config) (s : Snapshot) (e i : Nat) (p : Bool) : Reply :=
  if e ≠ c.incarnation then .wrongIncarnation
  else if i > c.limit then .invalidID
  else if i < s.lower then .expired s.lower
  else if i < s.position then
    if s.items[i - s.lower]? = some p then .acknowledged e i else .conflict
  else if i > s.position then .outOfOrder s.position
  else if s.position = c.limit then .exhausted else .reserved

def read (s : Snapshot) (a z : Nat) : Reply :=
  if a > z ∨ z > s.position then .invalidRange
  else if a < s.lower then .expired s.lower else .records (range s a z)

/-- Independent ghost observations use full history and its disclosed boundary. -/
def specRead (c : Config) (h : List Bool) (a z : Nat) : Reply :=
  if a > z ∨ z > h.length then .invalidRange
  else if a < h.length - c.window then .expired (h.length - c.window)
  else .records ((h.drop a).take (z - a))

theorem read_refines {c : Config} {s : Snapshot} {h : List Bool}
    (r : Represents c s h) (a z : Nat) : read s a z = specRead c h a z := by
  simp only [read, specRead, r.1, r.lower]
  split_ifs with bounds expired
  · rfl
  · rfl
  · congr 1
    exact r.range (by rw [r.lower]; omega)

def specClassify (c : Config) (h : List Bool) (e i : Nat) (p : Bool) : Reply :=
  if e ≠ c.incarnation then .wrongIncarnation
  else if i > c.limit then .invalidID
  else if i < h.length - c.window then .expired (h.length - c.window)
  else if i < h.length then
    if h[i]? = some p then .acknowledged e i else .conflict
  else if i > h.length then .outOfOrder h.length
  else if h.length = c.limit then .exhausted else .reserved

theorem classify_refines {c : Config} {s : Snapshot} {h : List Bool}
    (r : Represents c s h) (e i : Nat) (p : Bool) :
    classify c s e i p = specClassify c h e i p := by
  simp only [classify, specClassify, r.1, r.lower]
  split_ifs with incarnation domain expired old same other room
  all_goals try rfl
  all_goals
    have get : s.items[i - (h.length - c.window)]? = h[i]? := by
      rw [← r.suffix, List.getElem?_drop, r.lower]
      congr 1
      omega
    simp_all

/-- Freshness is determined by the bounded sequential position, not an unknown
key search that could mistake forgotten retry evidence for a fresh request. -/
theorem reserved_fresh {c : Config} {s : Snapshot} {e i : Nat} {p : Bool}
    (bounded : s.position ≤ c.limit) (ok : classify c s e i p = .reserved) :
    e = c.incarnation ∧ i = s.position ∧ s.position < c.limit := by
  unfold classify at ok
  split_ifs at ok; simp_all; omega

end Durability.Retention
