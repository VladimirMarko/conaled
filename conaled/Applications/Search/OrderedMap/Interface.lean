import Squares

/-!
# Finite-map operations and observation laws

The minimal interface of PFDS Exercise 2.6 keeps missing-key failure visible as
`none`. A successful lookup of a stored optional value is `some none`, not a
failure. Keys and payloads have independent types; no structure is required of
payloads. Function update describes meaning, without choosing a search tree.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedMap
universe u
variable {κ ν M : Type u}

structure Ops (κ ν M : Type u) where
  empty : M
  bind : κ → ν → M → M
  lookup : κ → M → Option ν

abbrev Meaning (κ ν : Type u) := κ → Option ν

def write [DecidableEq κ] (key : κ) (value : ν) (m : Meaning κ ν) : Meaning κ ν :=
  fun query => if query = key then some value else m query

/-- Operations and their semantic evidence are separate. No order on values
or representation equality is part of this observational contract. -/
structure Laws [DecidableEq κ] (ops : Ops κ ν M)
    (observe : M → Meaning κ ν) : Prop where
  empty : observe ops.empty = fun _ => none
  bind : ∀ key value m, observe (ops.bind key value m) = write key value (observe m)
  lookup : ∀ key m, ops.lookup key m = observe m key

def representation (observe : M → Meaning κ ν) : Squares.Rep :=
  ⟨M, Meaning κ ν, observe⟩

def Laws.bindSquare [DecidableEq κ] {ops : Ops κ ν M} {observe : M → Meaning κ ν}
    (h : Laws ops observe) (key : κ) (value : ν) :
    Squares.Square (representation observe) (representation observe) where
  impl := ops.bind key value
  spec := write key value
  commutes := h.bind key value

def Laws.lookupSquare [DecidableEq κ] {ops : Ops κ ν M}
    {observe : M → Meaning κ ν} (h : Laws ops observe) (key : κ) :
    Squares.Square (representation observe) ⟨Option ν, Option ν, id⟩ where
  impl := ops.lookup key
  spec := fun m => m key
  commutes := h.lookup key

/-- Bindings execute from left to right, so later equal keys overwrite earlier
ones. The client uses only the abstract operations. -/
def bindAll (ops : Ops κ ν M) : List (κ × ν) → M → M
  | [], m => m
  | (key, value) :: rest, m => bindAll ops rest (ops.bind key value m)

def writeAll [DecidableEq κ] : List (κ × ν) → Meaning κ ν → Meaning κ ν
  | [], m => m
  | (key, value) :: rest, m => writeAll rest (write key value m)

theorem Laws.bindAll_correct [DecidableEq κ] {ops : Ops κ ν M}
    {observe : M → Meaning κ ν} (h : Laws ops observe)
    (bindings : List (κ × ν)) (m : M) :
    observe (bindAll ops bindings m) = writeAll bindings (observe m) := by
  induction bindings generalizing m with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      simp only [bindAll, writeAll, ih, h.bind]

theorem Laws.lookup_bindAll [DecidableEq κ] {ops : Ops κ ν M}
    {observe : M → Meaning κ ν} (h : Laws ops observe)
    (bindings : List (κ × ν)) (m : M) (query : κ) :
    ops.lookup query (bindAll ops bindings m) = writeAll bindings (observe m) query := by
  rw [h.lookup, h.bindAll_correct]

end Search.OrderedMap
