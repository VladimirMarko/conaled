import Applications.Suspensions.Machine

/-!
# Effective addresses of recursive bindings

Only the first binding for an identifier participates in its environment
lookup. This characterizes the machine's SRec targets through that public
lookup operation, including environments with shadowed entries.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core
variable {Primitive : Type}

theorem Env.lookup_mem {bindings : Env Primitive} {name : Nat} {v : Value Primitive}
    (found : lookup bindings name = some v) : (name, v) ∈ bindings := by
  induction bindings with
  | nil => simp at found
  | cons pair rest ih =>
      rcases pair with ⟨key, entry⟩
      by_cases same : name = key
      · subst key
        simp only [lookup_cons_eq, Option.some.injEq] at found
        subst entry
        exact List.mem_cons_self
      · rw [lookup_cons_ne name key entry rest same] at found
        exact List.mem_cons_of_mem _ (ih found)

@[simp] theorem Env.lookup_rec_address_iff (bindings : Env Primitive) (name address : Nat) :
    lookup (rec bindings) name = some (.address address) ↔
      lookup bindings name = some (.address address) := by
  rw [lookup_rec]
  cases found : lookup bindings name with
  | none => simp
  | some v => cases v <;> simp [unrollValue]

namespace Machine

theorem mem_addressRange (bindings : Env Primitive) (address : Nat) :
    address ∈ addressRange bindings ↔
      ∃ name, Env.lookup bindings name = some (.address address) := by
  constructor
  · intro present
    obtain ⟨⟨name, entry⟩, _, selected⟩ :=
      List.mem_filterMap.mp (List.mem_toFinset.mp present)
    refine ⟨name, ?_⟩
    cases found : Env.lookup bindings name with
    | none => simp [found] at selected
    | some v => cases v <;> simp_all
  · rintro ⟨name, found⟩
    apply List.mem_toFinset.mpr
    apply List.mem_filterMap.mpr
    exact ⟨(name, .address address), Env.lookup_mem found, by simp [found]⟩

@[simp] theorem addressRange_rec (bindings : Env Primitive) :
    addressRange (Env.rec bindings) = addressRange bindings := by
  ext address
  simp only [mem_addressRange, Env.lookup_rec_address_iff]

end Machine
end Suspensions.Core
