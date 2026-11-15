import Mathlib.Data.Finset.Basic
import SquareKit.AdjointModes.Compiler

/-! A finite owned-handle protocol. Live handles disappear from the observable
heap on consumption; retained slots are accounting receipts, not live resources. -/
namespace SquareKit.OwnedHandle

structure Cell where
  owner : Nat
  value : Nat
  live : Bool
  deriving DecidableEq

structure State where
  slots : Bool → Option Cell
  returned : List Nat
  failed : Bool

inductive Command where
  | transfer (handle : Bool) (source destination : Nat)
  | consume (handle : Bool) (owner : Nat)
  deriving DecidableEq

def target : Command → Bool
  | .transfer h _ _ => h
  | .consume h _ => h

def replace (s : State) (h : Bool) (c : Cell) : State :=
  {s with slots := Function.update s.slots h (some c)}

def liveHeap (s : State) (h : Bool) : Option (Nat × Nat) :=
  match s.slots h with
  | some c => if c.live then some (c.owner, c.value) else none
  | none => none

/-- Mathematical transition specification, independent of instruction tests. -/
inductive Acts : Command → State → State → Prop where
  | transfer (s : State) (h : Bool) (a b : Nat) (c : Cell)
      (present : s.slots h = some c) (live : c.live = true)
      (owner : c.owner = a) (ready : s.failed = false) :
      Acts (.transfer h a b) s (replace s h {c with owner := b})
  | consume (s : State) (h : Bool) (a : Nat) (c : Cell)
      (present : s.slots h = some c) (live : c.live = true)
      (owner : c.owner = a) (ready : s.failed = false) :
      Acts (.consume h a) s
        {replace s h {c with live := false} with returned := s.returned ++ [c.value]}

/-- Bounded executable instruction step; failure does not fabricate a result. -/
def step (cmd : Command) (s : State) : Option State := do
  if s.failed then none else
  match cmd with
  | .transfer h a b =>
    let c ← s.slots h
    if c.live && c.owner == a then some (replace s h {c with owner := b}) else none
  | .consume h a =>
    let c ← s.slots h
    if c.live && c.owner == a then
      some {replace s h {c with live := false} with returned := s.returned ++ [c.value]}
    else none

theorem step_acts (cmd : Command) (s t : State) : step cmd s = some t ↔ Acts cmd s t := by
  constructor
  · intro hs
    cases cmd with
    | transfer h a b =>
      simp only [step] at hs
      split at hs
      next hf => simp_all
      next hf =>
        cases hc : s.slots h with
        | none => simp [hc] at hs
        | some c =>
          simp only [hc] at hs
          dsimp only [Bind.bind, Option.bind] at hs
          split at hs
          next hp =>
            have hp' : c.live = true ∧ c.owner = a := by simpa using hp
            have ht : replace s h {c with owner := b} = t := by simpa using hs
            subst t
            exact .transfer s h a b c hc hp'.1 hp'.2 (by simpa using hf)
          next hp => simp_all
    | consume h a =>
      simp only [step] at hs
      split at hs
      next hf => simp_all
      next hf =>
        cases hc : s.slots h with
        | none => simp [hc] at hs
        | some c =>
          simp only [hc] at hs
          dsimp only [Bind.bind, Option.bind] at hs
          split at hs
          next hp =>
            have hp' : c.live = true ∧ c.owner = a := by simpa using hp
            have ht : {replace s h {c with live := false} with returned := s.returned ++ [c.value]} = t := by simpa using hs
            subst t
            exact .consume s h a c hc hp'.1 hp'.2 (by simpa using hf)
          next hp => simp_all
  · intro h
    cases h with
    | transfer s h a b c hp hl ho hf => simp [step, hp, hl, ho, hf]
    | consume s h a c hp hl ho hf => simp [step, hp, hl, ho, hf]

inductive Runs : List Command → State → State → Prop where
  | nil (s) : Runs [] s s
  | cons {c cs s t u} : Acts c s t → Runs cs t u → Runs (c :: cs) s u

def run : List Command → State → Option State
  | [], s => some s
  | c :: cs, s => (step c s).bind (run cs)

theorem run_spec (cs : List Command) (s t : State) : run cs s = some t ↔ Runs cs s t := by
  induction cs generalizing s with
  | nil => simp only [run, Option.some.injEq]; constructor
           · rintro rfl; exact .nil s
           · intro h; cases h; rfl
  | cons c cs ih =>
    constructor
    · intro h
      cases hs : step c s with
      | none => simp [run, hs] at h
      | some u =>
        have hu : run cs u = some t := by simpa [run, hs] using h
        exact .cons ((step_acts c s u).mp hs) ((ih u).mp hu)
    · intro h
      cases h with
      | cons ha hr => simp [run, (step_acts _ _ _).mpr ha, (ih _).mpr hr]

theorem run_append (xs ys : List Command) (s : State) :
    run (xs ++ ys) s = (run xs s).bind (run ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp [run, ih, Option.bind_assoc]

/-- Consumed data is returned, and the handle no longer belongs to the live heap. -/
theorem consumed_absent {s t : State} {h : Bool} {a : Nat}
    (ha : Acts (.consume h a) s t) : liveHeap t h = none := by
  cases ha
  simp [liveHeap, replace]

theorem transfer_owner {s t : State} {h : Bool} {a b : Nat}
    (ha : Acts (.transfer h a b) s t) :
    ∃ v, liveHeap s h = some (a,v) ∧ liveHeap t h = some (b,v) := by
  cases ha with
  | transfer s h a b c hp hl ho hf =>
    exact ⟨c.value, by simp [liveHeap, hp, hl, ho], by simp [liveHeap, replace, hl]⟩

/-- Separation's local frame condition: a different handle is untouched. -/
theorem frame_slot {cmd : Command} {s t : State} (ha : Acts cmd s t) (k : Bool)
    (apart : match cmd with | .transfer h _ _ => k ≠ h | .consume h _ => k ≠ h) :
    t.slots k = s.slots k := by
  cases ha <;> simp_all [replace]

end SquareKit.OwnedHandle
