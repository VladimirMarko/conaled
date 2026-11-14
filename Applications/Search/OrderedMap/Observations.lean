import Applications.Search.OrderedMap.Interface
import Mathlib.Logic.Function.Basic

/-!
# Default lookup and presence over partial map meaning

These observations recover the corresponding VFA `TableObservations.lean`
draft (SHA-256 `0233781d210056e9a61ae9a355120429e55007e72713434d25a5338aa6489b57`)
inside the existing partial-map owner. Default lookup forgets absence; presence
and default lookup together recover partial meaning. No default, equality or
order on payloads is imposed on the underlying map interface.

The original generic total-table contract remains a distinct, weaker capability:
these bridges do not assume every total table supplies a partial observation.
The draft's historical focused check and bounded review do not confer current
integration acceptance. Current validation belongs to the integration record.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedMap
universe u v

section Algebra
variable {κ : Type u} {ν : Type v}

def withDefault (default : ν) (m : Meaning κ ν) : κ → ν :=
  fun query => (m query).getD default

def hasBinding (m : Meaning κ ν) (query : κ) : Bool := (m query).isSome

/-- The existing write and ordinary function update describe the same complete
partial meaning, without a representation or payload equality assumption. -/
theorem write_eq_update [DecidableEq κ] (key : κ) (value : ν) (m : Meaning κ ν) :
    write key value m = Function.update m key (some value) := by
  funext query
  simp [write, Function.update_apply]

theorem withDefault_update [DecidableEq κ] (default : ν) (m : Meaning κ ν)
    (key : κ) (value : ν) :
    withDefault default (Function.update m key (some value)) =
      Function.update (withDefault default m) key value := by
  funext query
  by_cases h : query = key <;> simp [withDefault, h]

theorem withDefault_write [DecidableEq κ] (default : ν) (m : Meaning κ ν)
    (key : κ) (value : ν) :
    withDefault default (write key value m) =
      Function.update (withDefault default m) key value := by
  rw [write_eq_update, withDefault_update]

theorem hasBinding_write [DecidableEq κ] (m : Meaning κ ν) (key : κ) (value : ν) :
    hasBinding (write key value m) = Function.update (hasBinding m) key true := by
  funext query
  by_cases h : query = key <;> simp [hasBinding, write, h]

/-- A bound bit and default-valued lookup together recover an actual binding. -/
theorem binding_iff (default : ν) (m : Meaning κ ν) (query : κ) (value : ν) :
    m query = some value ↔
      hasBinding m query = true ∧ withDefault default m query = value := by
  cases h : m query <;> simp [hasBinding, withDefault, h]

/-- Joint observation reflects equality; neither an injective representation
decoder nor an equality decision on values is needed. -/
theorem meaning_eq_iff (default : ν) (m n : Meaning κ ν) :
    m = n ↔ hasBinding m = hasBinding n ∧
      withDefault default m = withDefault default n := by
  constructor
  · intro h
    subst n
    exact ⟨rfl, rfl⟩
  · rintro ⟨presence, values⟩
    funext query
    have present := congrFun presence query
    have value := congrFun values query
    cases hm : m query with
    | none =>
        cases hn : n query with
        | none => rfl
        | some b => simp [hasBinding, hm, hn] at present
    | some a =>
        cases hn : n query with
        | none => simp [hasBinding, hm, hn] at present
        | some b =>
            have same : a = b := by simpa [withDefault, hm, hn] using value
            exact congrArg some same

/-- A supplied key and default witness the information lost by total lookup.
The statement makes no nonempty-key or inhabited-payload assumption implicit. -/
theorem forget_default_not_injective [DecidableEq κ] (key : κ) (default : ν) :
    ∃ m n : Meaning κ ν, m ≠ n ∧ withDefault default m = withDefault default n := by
  let m : Meaning κ ν := fun _ => none
  let n := Function.update m key (some default)
  refine ⟨m, n, ?_, ?_⟩
  · intro eq
    have h := congrFun eq key
    simp [m, n] at h
  · change withDefault default m =
      withDefault default (Function.update m key (some default))
    rw [withDefault_update]
    exact (Function.update_eq_self key (withDefault default m)).symm

/-- Chronological binding execution transports to ordinary total function
updates. The existing client and its order are retained for every list. -/
theorem withDefault_writeAll [DecidableEq κ] (default : ν)
    (bindings : List (κ × ν)) (m : Meaning κ ν) :
    withDefault default (writeAll bindings m) =
      bindings.foldl (fun f binding => Function.update f binding.1 binding.2)
        (withDefault default m) := by
  induction bindings generalizing m with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      simp only [writeAll, List.foldl, ih, withDefault_write]

end Algebra

section Squares
variable {κ ν M : Type u}

def defaultWriteSquare [DecidableEq κ] (default : ν) (bindings : List (κ × ν)) :
    Squares.Square ⟨Meaning κ ν, κ → ν, withDefault default⟩
      ⟨Meaning κ ν, κ → ν, withDefault default⟩ where
  impl := writeAll bindings
  spec := fun f => bindings.foldl
    (fun old binding => Function.update old binding.1 binding.2) f
  commutes := withDefault_writeAll default bindings

/-- The library's vertical pasting changes the observation of an existing
implementation. This is a one-way weakening to total lookup, not an inverse. -/
def Laws.defaultBindAllSquare [DecidableEq κ] {ops : Ops κ ν M}
    {observe : M → Meaning κ ν} (h : Laws ops observe)
    (default : ν) (bindings : List (κ × ν)) :
    Squares.Square ((representation observe).after (withDefault default))
      ((representation observe).after (withDefault default)) :=
  Squares.vertical (A := representation observe) (B := representation observe)
    (AS := κ → ν) (BS := κ → ν)
    (withDefault default : Meaning κ ν → κ → ν)
    (withDefault default : Meaning κ ν → κ → ν)
    (h.bindAllSquare bindings)
    (defaultWriteSquare (κ := κ) (ν := ν) default bindings) (fun _ => rfl)

end Squares
end Search.OrderedMap
