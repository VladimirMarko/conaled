import Applications.Search.OrderedMap.Interface

/-!
# Valid-state realizations of the existing map interface

The FDSA Map contract conditions mutation laws on representation validity.
Packaging valid states turns exactly those observation obligations into the
existing unconditional `Laws`; it does not assert equations on invalid inputs.
This bridge adds no alternative map operations or client executor. Deletion is
an additional capability and is not required of every existing map realization.

The source correspondence is the valid-state part of retained FDSA-XA01 donor
`20a5b5537a704be016d09e4eb31db0dad8a12d61`, `Applications/Collections/Map.lean`.
Its six-law update/delete interface remains a stronger, separately preserved
capability. This module recovers its validity/observation bridge for empty and
binding through the current shared owner.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedMap
universe u v w
variable {κ : Type u} {ν : Type v} {M : Type w}

/-- The actual operations on valid states retain the raw computation and its
preserved invariant. Constructing them requires no key decision procedure. -/
def Ops.restrict (ops : Ops κ ν M) (Valid : M → Prop)
    (empty_valid : Valid ops.empty)
    (bind_valid : ∀ key value m, Valid m → Valid (ops.bind key value m)) :
    Ops κ ν {m : M // Valid m} where
  empty := ⟨ops.empty, empty_valid⟩
  bind key value m := ⟨ops.bind key value m.1, bind_valid key value m.1 m.2⟩
  lookup key m := ops.lookup key m.1

/-- Unrestricted laws on the valid subtype are equivalent to the raw laws
only on valid inputs, with the same independent observation. Closure evidence
is explicit on both sides and supplies an inhabited valid starting domain. -/
theorem Laws.restrict_iff [DecidableEq κ] (ops : Ops κ ν M)
    (Valid : M → Prop) (observe : M → Meaning κ ν)
    (empty_valid : Valid ops.empty)
    (bind_valid : ∀ key value m, Valid m → Valid (ops.bind key value m)) :
    Laws (ops.restrict Valid empty_valid bind_valid) (fun m => observe m.1) ↔
      observe ops.empty = (fun _ => none) ∧
      (∀ key value m, Valid m →
        observe (ops.bind key value m) = write key value (observe m)) ∧
      (∀ key m, Valid m → ops.lookup key m = observe m key) := by
  constructor
  · intro h
    exact ⟨h.empty, fun key value m hm => h.bind key value ⟨m, hm⟩,
      fun key m hm => h.lookup key ⟨m, hm⟩⟩
  · rintro ⟨he, hb, hl⟩
    exact ⟨he, fun key value m => hb key value m.1 m.2,
      fun key m => hl key m.1 m.2⟩

/-- A convenient constructor for existing raw implementations with a proved
invariant. All subsequent arbitrary binding-list clients reuse `Laws`. -/
theorem Laws.of_valid [DecidableEq κ] {ops : Ops κ ν M}
    {Valid : M → Prop} {observe : M → Meaning κ ν}
    (empty_valid : Valid ops.empty)
    (bind_valid : ∀ key value m, Valid m → Valid (ops.bind key value m))
    (empty_observe : observe ops.empty = fun _ => none)
    (bind_observe : ∀ key value m, Valid m →
      observe (ops.bind key value m) = write key value (observe m))
    (lookup_observe : ∀ key m, Valid m → ops.lookup key m = observe m key) :
    Laws (ops.restrict Valid empty_valid bind_valid) (fun m => observe m.1) :=
  (Laws.restrict_iff ops Valid observe empty_valid bind_valid).2
    ⟨empty_observe, bind_observe, lookup_observe⟩

end Search.OrderedMap
