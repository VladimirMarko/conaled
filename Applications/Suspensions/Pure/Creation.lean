import Applications.Suspensions.Pure.Representation
import Applications.Suspensions.Recursive

/-!
# Creation and closing of represented recursive groups

The actual recursive-creation fold allocates delays without executing their
bodies. Its semantic world can already record the final group meanings, while
the new raw cells still contain the original capture. `PendingGroup` keeps
that intermediate condition separate from any closed-cell validity predicate.

Distinct source names ensure every allocated delay is selected by the
effective SRec target range. Closing then installs the represented expanded
body environments and retains every old occupied cell. No purity, body
termination, acyclicity or nonreentrancy premise is used here.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Creation
open Representation
variable {Primitive : Type}

/-- A world extension justified by actual creation, before SRec expands the
new captures. Existing world meanings are retained literally. -/
structure PendingGroup (beforeWorld afterWorld : World Primitive)
    (before preclose : Core.Machine.Memory Primitive) (rawOuter : Core.Env Primitive)
    (group : Suspensions.Pure.Group Primitive) (created : Core.Env Primitive) : Prop where
  extension : Durability.Extends beforeWorld afterWorld
  frontier : ∀ address meaning, afterWorld address = some meaning → address < preclose.next
  members : GroupRep afterWorld created group
  targets_fresh : ∀ address ∈ Core.Machine.addressRange (Core.Env.rec created),
    before.next ≤ address
  entries : ∀ address meaning, afterWorld address = some meaning →
    beforeWorld address = some meaning ∨
      ∃ body, meaning = ⟨body, group.outer, some group⟩ ∧
        preclose.memory address = some (.thunk body rawOuter) ∧
        address ∈ Core.Machine.addressRange (Core.Env.rec created)

private theorem world_fresh {world : World Primitive} {frontier : Nat}
    (bounded : ∀ address meaning, world address = some meaning → address < frontier) :
    world frontier = none := by
  cases found : world frontier with
  | none => rfl
  | some meaning => exact False.elim (Nat.lt_irrefl _ (bounded _ _ found))

/-- The private fold invariant retains the reversed processed source list.
Membership, rather than effective lookup, records delays until distinctness
is used after the complete creation fold. -/
private structure PendingEntries (initialWorld world : World Primitive)
    (lower : Nat) (memory : Core.Machine.Memory Primitive) (rawOuter : Core.Env Primitive)
    (group : Suspensions.Pure.Group Primitive) (processed : List (Nat × Rhs Primitive))
    (created : Core.Env Primitive) : Prop where
  extension : Durability.Extends initialWorld world
  frontier : ∀ address meaning, world address = some meaning → address < memory.next
  members : GroupMembersRep world group processed created
  addresses : ∀ name address, (name, Core.Value.address address) ∈ created → lower ≤ address
  entries : ∀ address meaning, world address = some meaning →
    initialWorld address = some meaning ∨
      ∃ name body, (name, Core.Value.address address) ∈ created ∧
        meaning = ⟨body, group.outer, some group⟩ ∧
        memory.memory address = some (.thunk body rawOuter)

private theorem PendingEntries.function
    {initialWorld world : World Primitive} {lower : Nat}
    {memory : Core.Machine.Memory Primitive} {rawOuter : Core.Env Primitive}
    {group : Suspensions.Pure.Group Primitive} {processed : List (Nat × Rhs Primitive)}
    {created : Core.Env Primitive}
    (pending : PendingEntries initialWorld world lower memory rawOuter group processed created)
    (captured : EnvRep world rawOuter group.outer) (name : Nat)
    (clauses : List (Core.Pattern × Core.Expr Primitive)) :
    PendingEntries initialWorld world lower memory rawOuter group
      ((name, .function clauses) :: processed)
      ((name, .closure clauses rawOuter []) :: created) where
  extension := pending.extension
  frontier := pending.frontier
  members := .function captured pending.members
  addresses key address inside := by
    rcases List.mem_cons.mp inside with same | earlier
    · cases same
    · exact pending.addresses key address earlier
  entries address meaning found := by
    rcases pending.entries address meaning found with old | ⟨key, body, member, same, cell⟩
    · exact Or.inl old
    · exact Or.inr ⟨key, body, List.mem_cons_of_mem _ member, same, cell⟩

private theorem PendingEntries.delay
    {initialWorld world : World Primitive} {lower : Nat}
    {memory : Core.Machine.Memory Primitive} {rawOuter : Core.Env Primitive}
    {group : Suspensions.Pure.Group Primitive} {processed : List (Nat × Rhs Primitive)}
    {created : Core.Env Primitive}
    (pending : PendingEntries initialWorld world lower memory rawOuter group processed created)
    (bounded : Suspensions.Bounded memory) (frontierLower : lower ≤ memory.next)
    (name : Nat) (body : Core.Expr Primitive) :
    PendingEntries initialWorld
      (Durability.put world memory.next ⟨body, group.outer, some group⟩)
      lower (Suspensions.delay memory body rawOuter).1 rawOuter group
      ((name, .delay body) :: processed)
      ((name, .address memory.next) :: created) := by
  let meaning : Meaning Primitive := ⟨body, group.outer, some group⟩
  have semanticExtension : Durability.Extends world (Durability.put world memory.next meaning) :=
    Durability.extends_put world memory.next meaning (world_fresh pending.frontier)
  have cellExtension := Suspensions.allocate_extends bounded (.thunk body rawOuter)
  refine ⟨pending.extension.trans semanticExtension, ?_,
    .delay (by simp [Durability.put]) (pending.members.mono semanticExtension), ?_, ?_⟩
  · intro address value found
    by_cases same : address = memory.next
    · subst address
      change memory.next < memory.next + 1
      omega
    · have previous : world address = some value := by
        simpa [Durability.put, same] using found
      have earlier := pending.frontier address value previous
      change address < memory.next + 1
      omega
  · intro key address inside
    rcases List.mem_cons.mp inside with same | earlier
    · cases same
      exact frontierLower
    · exact pending.addresses key address earlier
  · intro address value found
    by_cases same : address = memory.next
    · subst address
      have equal : meaning = value := by
        simpa [Durability.put, meaning] using found
      exact Or.inr ⟨name, body, List.mem_cons_self, equal.symm,
        Suspensions.delay_captures memory body rawOuter⟩
    · have previous : world address = some value := by
        simpa [Durability.put, same] using found
      rcases pending.entries address value previous with old | ⟨key, code, member, equal, cell⟩
      · exact Or.inl old
      · exact Or.inr ⟨key, code, List.mem_cons_of_mem _ member, equal,
          cellExtension address (.thunk code rawOuter) cell⟩

private theorem create_loop
    {initialWorld world : World Primitive} {lower : Nat}
    {memory : Core.Machine.Memory Primitive} {rawOuter : Core.Env Primitive}
    {group : Suspensions.Pure.Group Primitive} {processed : List (Nat × Rhs Primitive)}
    {created : Core.Env Primitive} (remaining : List (Nat × Rhs Primitive))
    {result : Core.Machine.Memory Primitive × Core.Env Primitive}
    (bounded : Suspensions.Bounded memory) (frontierLower : lower ≤ memory.next)
    (captured : EnvRep world rawOuter group.outer)
    (pending : PendingEntries initialWorld world lower memory rawOuter group processed created)
    (made : Core.Recursive.create memory rawOuter (Rhs.toBindings remaining) created = .ok result) :
    ∃ finalWorld, PendingEntries initialWorld finalWorld lower result.1 rawOuter group
      (remaining.reverse ++ processed) result.2 := by
  induction remaining generalizing memory world processed created result with
  | nil =>
      change Except.ok (memory, created) = Except.ok result at made
      have equal : (memory, created) = result := Except.ok.inj made
      subst result
      exact ⟨world, pending⟩
  | cons binding rest ih =>
      rcases binding with ⟨name, rhs⟩
      cases rhs with
      | function clauses =>
          change Core.Recursive.create memory rawOuter (Rhs.toBindings rest)
            ((name, .closure clauses rawOuter []) :: created) = .ok result at made
          obtain ⟨finalWorld, finalPending⟩ := ih bounded frontierLower captured
            (pending.function captured name clauses) made
          exact ⟨finalWorld, by
            simpa only [List.reverse_cons, List.append_assoc, List.singleton_append]
              using finalPending⟩
      | delay body =>
          let nextWorld := Durability.put world memory.next
            (⟨body, group.outer, some group⟩ : Meaning Primitive)
          have semanticExtension : Durability.Extends world nextWorld :=
            Durability.extends_put world memory.next _ (world_fresh pending.frontier)
          change Core.Recursive.create (Suspensions.delay memory body rawOuter).1 rawOuter
            (Rhs.toBindings rest) ((name, .address memory.next) :: created) = .ok result at made
          have nextLower : lower ≤ (Suspensions.delay memory body rawOuter).1.next := by
            change lower ≤ memory.next + 1
            omega
          obtain ⟨finalWorld, finalPending⟩ :=
            ih (Suspensions.delay_bounded bounded body rawOuter) nextLower
              (captured.mono semanticExtension)
              (pending.delay bounded frontierLower name body) made
          exact ⟨finalWorld, by
            simpa only [List.reverse_cons, List.append_assoc, List.singleton_append]
              using finalPending⟩

private theorem member_names {world : World Primitive} {group : Suspensions.Pure.Group Primitive}
    {definitions : List (Nat × Rhs Primitive)} {created : Core.Env Primitive}
    (represented : GroupMembersRep world group definitions created) :
    created.map Prod.fst = definitions.map Prod.fst := by
  induction definitions generalizing created with
  | nil => cases represented; rfl
  | cons binding rest ih =>
      rcases binding with ⟨name, rhs⟩
      cases represented with
      | function captured tail => simpa using congrArg (List.cons name) (ih tail)
      | delay found tail => simpa using congrArg (List.cons name) (ih tail)

private theorem lookup_of_mem {created : Core.Env Primitive} {name : Nat}
    {value : Core.Value Primitive} (distinct : (created.map Prod.fst).Nodup)
    (member : (name, value) ∈ created) : Core.Env.lookup created name = some value := by
  induction created with
  | nil => cases member
  | cons binding rest ih =>
      rcases binding with ⟨key, entry⟩
      have unique : key ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup :=
        List.nodup_cons.mp distinct
      rcases List.mem_cons.mp member with same | earlier
      · cases same
        exact Core.Env.lookup_cons_eq name value rest
      · have different : name ≠ key := by
          intro same
          subst name
          exact unique.1 (List.mem_map.mpr ⟨(key, value), earlier, rfl⟩)
        rw [Core.Env.lookup_cons_ne name key entry rest different]
        exact ih unique.2 earlier

/-- The actual permitted creation receipt determines a prospective world
extension. Distinct names ensure even the full template's delayed entries
are effective SRec targets; no body is evaluated by this construction. -/
theorem create_pending
    {beforeWorld : World Primitive} {before preclose : Core.Machine.Memory Primitive}
    {rawOuter created : Core.Env Primitive} {pureOuter : Env Primitive}
    {definitions : List (Nat × Rhs Primitive)}
    (bounded : Suspensions.Bounded before)
    (worldBelow : ∀ address meaning, beforeWorld address = some meaning → address < before.next)
    (captured : EnvRep beforeWorld rawOuter pureOuter)
    (distinct : (definitions.map Prod.fst).Nodup)
    (made : Core.Recursive.create before rawOuter (Rhs.toBindings definitions) [] =
      .ok (preclose, created)) :
    ∃ afterWorld, PendingGroup beforeWorld afterWorld before preclose rawOuter
      (.mk definitions pureOuter) created := by
  let group : Suspensions.Pure.Group Primitive := .mk definitions pureOuter
  have initial : PendingEntries beforeWorld beforeWorld before.next before rawOuter group [] [] :=
    { extension := Durability.Extends.refl _
      frontier := worldBelow
      members := .nil group
      addresses := by intro name address impossible; cases impossible
      entries := by intro address meaning found; exact Or.inl found }
  obtain ⟨afterWorld, pending⟩ := create_loop definitions bounded (Nat.le_refl _)
    captured initial made
  have names : created.map Prod.fst = (definitions.map Prod.fst).reverse := by
    simpa only [List.append_nil, List.map_reverse] using member_names pending.members
  have rawDistinct : (created.map Prod.fst).Nodup := by
    rw [names]
    exact List.nodup_reverse.mpr distinct
  refine ⟨afterWorld, pending.extension, pending.frontier, ?_, ?_, ?_⟩
  · change GroupMembersRep afterWorld group definitions.reverse created
    simpa only [List.append_nil] using pending.members
  · intro address inside
    rw [Core.Machine.addressRange_rec] at inside
    obtain ⟨name, found⟩ := (Core.Machine.mem_addressRange created address).mp inside
    exact pending.addresses name address (Core.Env.lookup_mem found)
  · intro address meaning found
    rcases pending.entries address meaning found with old | ⟨name, body, member, equal, cell⟩
    · exact Or.inl old
    · refine Or.inr ⟨body, equal, cell, ?_⟩
      rw [Core.Machine.addressRange_rec, Core.Machine.mem_addressRange]
      exact ⟨name, lookup_of_mem rawDistinct member⟩

variable {beforeWorld afterWorld : World Primitive}
  {before preclose : Core.Machine.Memory Primitive} {rawOuter created : Core.Env Primitive}
  {group : Suspensions.Pure.Group Primitive}

/-- SRec gives every new meaning its expanded represented capture. The body
may still diverge or force its own address; no evaluation witness is needed. -/
theorem PendingGroup.closed_new
    (pending : PendingGroup beforeWorld afterWorld before preclose rawOuter group created)
    (captured : EnvRep beforeWorld rawOuter group.outer) {address : Nat} {meaning : Meaning Primitive}
    (found : afterWorld address = some meaning) (fresh : beforeWorld address = none) :
    ∃ rawCapture,
      (Core.Recursive.closeMemory preclose created).memory address =
        some (.thunk meaning.body rawCapture) ∧
      EnvRep afterWorld rawCapture meaning.environment := by
  rcases pending.entries address meaning found with old | ⟨body, equal, cell, inside⟩
  · rw [fresh] at old
    cases old
  · subst meaning
    exact ⟨Core.Env.extend rawOuter (Core.Env.rec created),
      Suspensions.srec_thunk _ inside cell,
      pending.members.bodyEnvironment (captured.mono pending.extension)⟩

/-- Existing occupied cells survive both fresh creation and closing. This
includes cached values and unrelated thunks; SRec only selects fresh cells. -/
theorem PendingGroup.closed_old
    (pending : PendingGroup beforeWorld afterWorld before preclose rawOuter group created)
    (bounded : Suspensions.Bounded before)
    (made : Core.Recursive.create before rawOuter (Rhs.toBindings group.bindings) [] =
      .ok (preclose, created)) {address : Nat}
    {cell : Cell (Core.Expr Primitive) (Core.Env Primitive) (Core.Value Primitive)}
    (found : before.memory address = some cell) :
    (Core.Recursive.closeMemory preclose created).memory address = some cell := by
  have extension := (Core.Recursive.create_preserves (Rhs.toBindings_permitted group.bindings)
    bounded (Core.Recursive.CreatedThunks.nil before) made).2.2
  have outside : address ∉ Core.Machine.addressRange (Core.Env.rec created) := by
    intro inside
    have lower := pending.targets_fresh address inside
    have earlier := bounded.occupied_lt found
    omega
  exact (Suspensions.srec_other preclose _ _ outside).trans (extension _ _ found)

/-- The actual environment used after closing realizes the descriptor's
body environment, with recursive members overriding the original capture. -/
theorem PendingGroup.closed_environment
    (pending : PendingGroup beforeWorld afterWorld before preclose rawOuter group created)
    (captured : EnvRep beforeWorld rawOuter group.outer) :
    EnvRep afterWorld (Core.Recursive.closeEnvironment rawOuter created)
      (bodyEnvironment group.outer (some group)) :=
  pending.members.bodyEnvironment (captured.mono pending.extension)

end Suspensions.Pure.Creation
