import Applications.Suspensions.AddressRange

/-!
# Relocating runtime addresses

Source syntax contains identifiers, not runtime addresses. Relocation acts on
values, captured environments and memory. A related memory can have private
cells outside the image of the injection; lookup at every represented address
must still agree. The operations and their injectivity/frontier laws are kept
separate. This algebra alone is not a machine simulation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Renaming
open Machine

variable {Primitive : Type}

mutual
  def value (rename : Nat → Nat) : Value Primitive → Value Primitive
    | .atom atom => .atom atom
    | .constructor tag argument => .constructor tag (optional rename argument)
    | .record fields => .record (environment rename fields)
    | .address address => .address (rename address)
    | .closure clauses captured recursive =>
        .closure clauses (environment rename captured) (environment rename recursive)
    | .primitive operation => .primitive operation
    | .exception tag argument => .exception tag (optional rename argument)
  termination_by v => sizeOf v
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def optional (rename : Nat → Nat) : Option (Value Primitive) → Option (Value Primitive)
    | none => none
    | some v => some (value rename v)
  termination_by argument => sizeOf argument
  decreasing_by simp_wf

  def environment (rename : Nat → Nat) : Env Primitive → Env Primitive
    | [] => []
    | (name, v) :: rest => (name, value rename v) :: environment rename rest
  termination_by bindings => sizeOf bindings
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

@[simp] theorem optional_eq_map (rename : Nat → Nat) (argument : Option (Value Primitive)) :
    optional rename argument = argument.map (value rename) := by
  cases argument <;> rfl

@[simp] theorem environment_nil (rename : Nat → Nat) :
    environment rename ([] : Env Primitive) = [] := rfl

@[simp] theorem environment_cons (rename : Nat → Nat) (name : Nat)
    (v : Value Primitive) (rest : Env Primitive) :
    environment rename ((name, v) :: rest) =
      (name, value rename v) :: environment rename rest := rfl

theorem environment_eq_map (rename : Nat → Nat) (bindings : Env Primitive) :
    environment rename bindings = bindings.map (fun (name, v) => (name, value rename v)) := by
  induction bindings with
  | nil => rfl
  | cons pair rest ih => rcases pair with ⟨name, v⟩; simp [ih]

@[simp] theorem environment_append (rename : Nat → Nat) (first second : Env Primitive) :
    environment rename (first ++ second) =
      environment rename first ++ environment rename second := by
  simp only [environment_eq_map, List.map_append]

@[simp] theorem environment_extend (rename : Nat → Nat) (base additions : Env Primitive) :
    environment rename (Env.extend base additions) =
      Env.extend (environment rename base) (environment rename additions) := by
  exact environment_append rename additions base

@[simp] theorem environment_lookup (rename : Nat → Nat) (bindings : Env Primitive)
    (name : Nat) :
    Env.lookup (environment rename bindings) name =
      (Env.lookup bindings name).map (value rename) := by
  induction bindings with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨key, v⟩
      by_cases same : name = key <;> simp [Env.lookup, same, ih]

@[simp] theorem value_unroll (rename : Nat → Nat) (bindings : Env Primitive)
    (v : Value Primitive) :
    value rename (Env.unrollValue bindings v) =
      Env.unrollValue (environment rename bindings) (value rename v) := by
  cases v <;> rfl

@[simp] theorem environment_rec (rename : Nat → Nat) (bindings : Env Primitive) :
    environment rename (Env.rec bindings) = Env.rec (environment rename bindings) := by
  have general : ∀ entries : Env Primitive,
      environment rename (entries.map fun (name, v) => (name, Env.unrollValue bindings v)) =
        (environment rename entries).map fun (name, v) =>
          (name, Env.unrollValue (environment rename bindings) v) := by
    intro entries
    induction entries with
    | nil => rfl
    | cons pair rest ih => rcases pair with ⟨name, v⟩; simp [ih]
  simpa only [Env.rec, Env.unrollValue] using general bindings

def cell (rename : Nat → Nat) : Cell (Expr Primitive) (Env Primitive) (Value Primitive) →
    Cell (Expr Primitive) (Env Primitive) (Value Primitive)
  | .value v => .value (value rename v)
  | .thunk body captured => .thunk body (environment rename captured)

/-- No condition is imposed on private cells outside the address map's image. -/
structure MemoryRel (rename : Nat → Nat) (before after : Memory Primitive) : Prop where
  frontier : after.next = rename before.next
  exceptionNames : after.exceptionNames = before.exceptionNames
  lookup : ∀ address, after.memory (rename address) = (before.memory address).map (cell rename)

theorem MemoryRel.replace {rename : Nat → Nat} (injective : Function.Injective rename)
    {before after : Memory Primitive} (related : MemoryRel rename before after)
    (address : Nat) (entry : Cell (Expr Primitive) (Env Primitive) (Value Primitive)) :
    MemoryRel rename (Suspensions.replace before address entry)
      (Suspensions.replace after (rename address) (cell rename entry)) where
  frontier := related.frontier
  exceptionNames := related.exceptionNames
  lookup other := by
    by_cases same : other = address
    · subst other
      simp
    · have separate : rename other ≠ rename address := fun eq => same (injective eq)
      simp only [Suspensions.replace_other _ _ _ separate,
        Suspensions.replace_other _ _ _ same, related.lookup]

theorem MemoryRel.memoize {rename : Nat → Nat} (injective : Function.Injective rename)
    {before after : Memory Primitive} (related : MemoryRel rename before after)
    (address : Nat) (v : Value Primitive) :
    MemoryRel rename (Suspensions.memoize before address v)
      (Suspensions.memoize after (rename address) (value rename v)) :=
  related.replace injective address (.value v)

theorem MemoryRel.allocate {rename : Nat → Nat} (injective : Function.Injective rename)
    {before after : Memory Primitive} (related : MemoryRel rename before after)
    (successor : rename (before.next + 1) = rename before.next + 1)
    (entry : Cell (Expr Primitive) (Env Primitive) (Value Primitive)) :
    MemoryRel rename (Suspensions.allocate before entry).1
      (Suspensions.allocate after (cell rename entry)).1 where
  frontier := by simp [related.frontier, successor]
  exceptionNames := related.exceptionNames
  lookup address := by
    change (Durability.put after.memory after.next (cell rename entry)) (rename address) =
      ((Durability.put before.memory before.next entry) address).map (cell rename)
    rw [related.frontier]
    by_cases same : address = before.next
    · subst address
      simp [Durability.put]
    · have separate : rename address ≠ rename before.next := fun eq => same (injective eq)
      simp [Durability.put, same, separate, related.lookup]

theorem MemoryRel.delay {rename : Nat → Nat} (injective : Function.Injective rename)
    {before after : Memory Primitive} (related : MemoryRel rename before after)
    (successor : rename (before.next + 1) = rename before.next + 1)
    (body : Expr Primitive) (captured : Env Primitive) :
    MemoryRel rename (Suspensions.delay before body captured).1
      (Suspensions.delay after body (environment rename captured)).1 :=
  related.allocate injective successor (.thunk body captured)

@[simp] theorem cell_extend (rename : Nat → Nat) (additions : Env Primitive)
    (entry : Cell (Expr Primitive) (Env Primitive) (Value Primitive)) :
    cell rename (Cell.extendEnv (fun captured => Env.extend captured additions) entry) =
      Cell.extendEnv (fun captured => Env.extend captured (environment rename additions))
        (cell rename entry) := by
  cases entry <;> simp [cell, Cell.extendEnv]

theorem MemoryRel.srec {rename : Nat → Nat} (injective : Function.Injective rename)
    {before after : Memory Primitive} (related : MemoryRel rename before after)
    (targets : Finset Nat) (additions : Env Primitive) :
    MemoryRel rename
      (Suspensions.srec before targets (fun captured => Env.extend captured additions))
      (Suspensions.srec after (targets.image rename)
        (fun captured => Env.extend captured (environment rename additions))) where
  frontier := related.frontier
  exceptionNames := related.exceptionNames
  lookup address := by
    have membership : rename address ∈ targets.image rename ↔ address ∈ targets := by
      constructor
      · rintro member
        obtain ⟨other, belongs, same⟩ := Finset.mem_image.mp member
        have eq := injective same
        subst other
        exact belongs
      · intro belongs
        exact Finset.mem_image.mpr ⟨address, belongs, rfl⟩
    simp only [Suspensions.srec, membership, related.lookup]
    by_cases inside : address ∈ targets
    · cases found : before.memory address <;> simp [inside, cell_extend]
    · simp [inside]

@[simp] theorem addressRange_environment (rename : Nat → Nat) (bindings : Env Primitive) :
    addressRange (environment rename bindings) = (addressRange bindings).image rename := by
  ext address
  rw [mem_addressRange, Finset.mem_image]
  constructor
  · rintro ⟨name, found⟩
    rw [environment_lookup] at found
    cases original : Env.lookup bindings name with
    | none => simp [original] at found
    | some v =>
        rw [original, Option.map_some] at found
        cases v with
        | address old =>
            have same : rename old = address := by simpa [value] using found
            exact ⟨old, (mem_addressRange bindings old).mpr ⟨name, original⟩, same⟩
        | _ => simp [value] at found
  · rintro ⟨old, present, same⟩
    obtain ⟨name, found⟩ := (mem_addressRange bindings old).mp present
    exact ⟨name, by simp [found, value, same]⟩

theorem MemoryRel.exception {rename : Nat → Nat} {before after : Memory Primitive}
    (related : MemoryRel rename before after) (name : Nat) :
    MemoryRel rename { before with exceptionNames := insert name before.exceptionNames }
      { after with exceptionNames := insert name after.exceptionNames } where
  frontier := related.frontier
  exceptionNames := by rw [related.exceptionNames]
  lookup := related.lookup

/-- Reserve one extra private cell at the original frontier. -/
def shift (frontier address : Nat) : Nat := if address < frontier then address else address + 1

theorem shift_injective (frontier : Nat) : Function.Injective (shift frontier) := by
  intro first second same
  unfold shift at same
  split at same <;> split at same <;> omega

@[simp] theorem shift_old {frontier address : Nat} (old : address < frontier) :
    shift frontier address = address := if_pos old

@[simp] theorem shift_new {frontier address : Nat} (newer : frontier ≤ address) :
    shift frontier address = address + 1 := if_neg (by omega)

theorem shift_avoids (frontier address : Nat) : shift frontier address ≠ frontier := by
  unfold shift
  split <;> omega

theorem shift_successor {frontier address : Nat} (newer : frontier ≤ address) :
    shift frontier (address + 1) = shift frontier address + 1 := by
  rw [shift_new (by omega), shift_new newer]

/-- Updating the omitted private cell does not change the represented heap. -/
theorem MemoryRel.private_replace {frontier : Nat} {before after : Memory Primitive}
    (related : MemoryRel (shift frontier) before after)
    (entry : Cell (Expr Primitive) (Env Primitive) (Value Primitive)) :
    MemoryRel (shift frontier) before (Suspensions.replace after frontier entry) where
  frontier := related.frontier
  exceptionNames := related.exceptionNames
  lookup address := by
    rw [Suspensions.replace_other _ _ _ (shift_avoids frontier address)]
    exact related.lookup address

end Suspensions.Core.Renaming
