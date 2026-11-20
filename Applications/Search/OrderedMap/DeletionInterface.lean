import Applications.Search.OrderedMap.Interface

/-! An additive deletion capability for finite maps. Keys, payloads and
carriers have independent universes. Existing bind-only clients use `toOps`
and `toLaws`; successful optional payloads remain distinct from missing keys. -/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedMap
universe u v w
variable {κ : Type u} {ν : Type v} {M : Type w}

structure DeleteOps (κ : Type u) (ν : Type v) (M : Type w) extends Ops κ ν M where
  delete : κ → M → M

def erase [DecidableEq κ] (key : κ) (m : Meaning κ ν) : Meaning κ ν :=
  fun query => if query = key then none else m query

structure DeleteLaws [DecidableEq κ] (ops : DeleteOps κ ν M)
    (observe : M → Meaning κ ν) : Prop extends Laws ops.toOps observe where
  delete : ∀ key m, observe (ops.delete key m) = erase key (observe m)

theorem DeleteLaws.lookup_delete [DecidableEq κ] {ops : DeleteOps κ ν M}
    {observe : M → Meaning κ ν} (laws : DeleteLaws ops observe)
    (key query : κ) (m : M) :
    ops.lookup query (ops.delete key m) = if query = key then none else ops.lookup query m := by
  rw [laws.lookup, laws.delete, laws.lookup]
  rfl

/-- A polymorphic client uses deletion and the original binding capability. -/
theorem DeleteLaws.lookup_delete_bind [DecidableEq κ] {ops : DeleteOps κ ν M}
    {observe : M → Meaning κ ν} (laws : DeleteLaws ops observe)
    (query key : κ) (value : ν) (m : M) :
    ops.lookup query (ops.delete key (ops.bind query value m)) =
      if query = key then none else some value := by
  rw [laws.lookup, laws.delete, laws.bind]
  simp [erase, write]

/-- The original binding-list executor is recovered by the interface projection. -/
theorem DeleteLaws.lookup_bindAll [DecidableEq κ] {ops : DeleteOps κ ν M}
    {observe : M → Meaning κ ν} (laws : DeleteLaws ops observe)
    (bindings : List (κ × ν)) (m : M) (query : κ) :
    ops.lookup query (bindAll ops.toOps bindings m) = writeAll bindings (observe m) query :=
  laws.toLaws.lookup_bindAll bindings m query

end Search.OrderedMap
