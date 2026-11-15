import Applications.Suspensions.Pure.Representation
import Applications.Suspensions.Pure.Machine
import Applications.Suspensions.Machine

/-!
# Heap cells justified by immutable pure meanings

An unforced cell needs only its code and represented capture. A cached cell
instead carries an actual finite evaluation of that same pure body. This
distinction admits recursive, nonterminating thunks without assuming a result
for them. It also makes cache reuse independent of later heap growth.

The invariant concerns represented addresses. Other occupied cells may exist,
but cannot be accessed through a represented suspension without a world entry.
Hereditary source-code restrictions and primitive preservation are separate
obligations of the eventual execution correspondence.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Memory
open Representation

variable {Primitive : Type}

inductive CellRep (parameters : Machine.Parameters Primitive) (world : World Primitive)
    (meaning : Meaning Primitive) :
    Cell (Core.Expr Primitive) (Core.Env Primitive) (Core.Value Primitive) → Prop
  | thunk {captured : Core.Env Primitive}
      (environment : EnvRep world captured meaning.environment) :
      CellRep parameters world meaning (.thunk meaning.body captured)
  | cached {raw : Core.Value Primitive} {view : Value Primitive} {steps : Nat}
      (represented : ValueRep world raw view)
      (evaluation : Progress.Evaluates (Machine.step parameters)
        (Machine.start meaning.environment meaning.body) (.value view) steps) :
      CellRep parameters world meaning (.value raw)

/-- Finite raw memory and justified occupied cells suffice to derive a fresh
semantic frontier; a separate, redundant world-bound field is unnecessary. -/
structure StateRep (parameters : Machine.Parameters Primitive) (world : World Primitive)
    (memory : Core.Machine.Memory Primitive) : Prop where
  bounded : Suspensions.Bounded memory
  meanings : ∀ address meaning, world address = some meaning →
    ∃ cell, memory.memory address = some cell ∧ CellRep parameters world meaning cell

variable {parameters : Machine.Parameters Primitive} {world : World Primitive}

theorem CellRep.mono {before after : World Primitive} {meaning : Meaning Primitive}
    {cell : Cell (Core.Expr Primitive) (Core.Env Primitive) (Core.Value Primitive)}
    (extension : Durability.Extends before after)
    (represented : CellRep parameters before meaning cell) :
    CellRep parameters after meaning cell := by
  cases represented with
  | thunk environment => exact .thunk (environment.mono extension)
  | cached value evaluation => exact .cached (value.mono extension) evaluation

/-- Two justified cached values for one immutable meaning have a common pure
value and count. Raw values need not be syntactically identical. -/
theorem CellRep.cached_unique {meaning : Meaning Primitive}
    {first second : Core.Value Primitive}
    (earlier : CellRep parameters world meaning (.value first))
    (later : CellRep parameters world meaning (.value second)) :
    ∃ view steps, ValueRep world first view ∧ ValueRep world second view ∧
      Progress.Evaluates (Machine.step parameters)
        (Machine.start meaning.environment meaning.body) (.value view) steps := by
  cases earlier with
  | cached firstRep firstEvaluation =>
      cases later with
      | cached secondRep secondEvaluation =>
          have same := firstEvaluation.unique secondEvaluation
          cases same.1
          exact ⟨_, _, firstRep, secondRep, firstEvaluation⟩

/-- A known nonterminating pure body cannot justify a cached value. The
corresponding unforced thunk remains a valid possibility. -/
theorem CellRep.no_cache_of_not_terminates {meaning : Meaning Primitive}
    (unfinished : ¬Progress.Terminates (Machine.step parameters)
      (Machine.start meaning.environment meaning.body)) (value : Core.Value Primitive) :
    ¬CellRep parameters world meaning (.value value) := by
  intro represented
  cases represented with
  | cached value evaluation => exact unfinished ⟨_, _, evaluation⟩

theorem StateRep.empty (parameters : Machine.Parameters Primitive) :
    StateRep parameters (fun _ => none) Suspensions.empty where
  bounded := Suspensions.bounded_empty
  meanings address meaning impossible := by cases impossible

theorem StateRep.world_below {memory : Core.Machine.Memory Primitive}
    (valid : StateRep parameters world memory) (address : Nat) (meaning : Meaning Primitive)
    (found : world address = some meaning) : address < memory.next := by
  obtain ⟨cell, occupied, _⟩ := valid.meanings address meaning found
  exact valid.bounded.occupied_lt occupied

theorem StateRep.world_fresh {memory : Core.Machine.Memory Primitive}
    (valid : StateRep parameters world memory) : world memory.next = none := by
  cases found : world memory.next with
  | none => rfl
  | some meaning => exact False.elim (Nat.lt_irrefl _ (valid.world_below _ _ found))

theorem StateRep.lookup {memory : Core.Machine.Memory Primitive}
    (valid : StateRep parameters world memory) {address : Nat} {meaning : Meaning Primitive}
    {cell : Cell (Core.Expr Primitive) (Core.Env Primitive) (Core.Value Primitive)}
    (found : world address = some meaning) (occupied : memory.memory address = some cell) :
    CellRep parameters world meaning cell := by
  obtain ⟨actual, lookup, represented⟩ := valid.meanings address meaning found
  have same := Option.some.inj (lookup.symm.trans occupied)
  subst actual
  exact represented

/-- Fresh delay allocation installs a meaning without evaluating its body.
All earlier cache certificates and represented captures survive the extension. -/
theorem StateRep.delay {memory : Core.Machine.Memory Primitive}
    {rawCapture : Core.Env Primitive} {capture : Env Primitive}
    (valid : StateRep parameters world memory) (captured : EnvRep world rawCapture capture)
    (body : Core.Expr Primitive) :
    let meaning : Meaning Primitive := ⟨body, capture, none⟩
    let afterWorld := Durability.put world memory.next meaning
    Durability.Extends world afterWorld ∧
      StateRep parameters afterWorld (Suspensions.delay memory body rawCapture).1 ∧
      ValueRep afterWorld (.address memory.next) (.suspension body capture none) := by
  let meaning : Meaning Primitive := ⟨body, capture, none⟩
  let afterWorld := Durability.put world memory.next meaning
  have extension : Durability.Extends world afterWorld :=
    Durability.extends_put world memory.next meaning valid.world_fresh
  refine ⟨extension, ⟨Suspensions.delay_bounded valid.bounded body rawCapture, ?_⟩,
    .address (meaning := meaning) (by simp [Durability.put, meaning])⟩
  intro address entry found
  by_cases same : address = memory.next
  · subst address
    have equal : meaning = entry := by simpa [afterWorld, Durability.put] using found
    subst entry
    exact ⟨_, Suspensions.delay_captures memory body rawCapture,
      .thunk (captured.mono extension)⟩
  · have old : world address = some entry := by
      simpa [afterWorld, Durability.put, same] using found
    obtain ⟨cell, occupied, represented⟩ := valid.meanings address entry old
    exact ⟨cell, Suspensions.allocate_retains valid.bounded occupied (.thunk body rawCapture),
      represented.mono extension⟩

/-- A completed pure body justifies the actual replacement operation. The
written cell may already be cached; neither first-write nor nonreentry is a
premise. Those execution properties must be derived separately. -/
theorem StateRep.memoize {memory : Core.Machine.Memory Primitive}
    {address : Nat} {meaning : Meaning Primitive} {raw : Core.Value Primitive}
    {view : Value Primitive} {steps : Nat}
    (valid : StateRep parameters world memory) (found : world address = some meaning)
    (represented : ValueRep world raw view)
    (evaluation : Progress.Evaluates (Machine.step parameters)
      (Machine.start meaning.environment meaning.body) (.value view) steps) :
    StateRep parameters world (Suspensions.memoize memory address raw) := by
  obtain ⟨old, occupied, _⟩ := valid.meanings address meaning found
  refine ⟨Suspensions.memoize_bounded valid.bounded occupied raw, ?_⟩
  intro other entry lookup
  by_cases same : other = address
  · subst other
    have equal := Option.some.inj (found.symm.trans lookup)
    subst entry
    exact ⟨_, Suspensions.memoize_lookup memory address raw, .cached represented evaluation⟩
  · obtain ⟨cell, previous, cellRep⟩ := valid.meanings other entry lookup
    exact ⟨cell, (Suspensions.memoize_other memory address raw same).trans previous, cellRep⟩

end Suspensions.Pure.Memory
