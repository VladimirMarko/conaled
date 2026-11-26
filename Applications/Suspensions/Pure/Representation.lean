import Applications.Suspensions.Pure.Value
import Applications.Durability.Storage

/-!
# Stable meanings of raw suspension addresses and recursive templates

The semantic world uses the existing immutable `Durability.Heap`/`Extends`
interface. It is distinct from the mutable machine memory: a cache write must
not change an address's pure meaning. This module relates finite raw values
and original recursive-creation templates to the pure values. It does not yet
assert a memory invariant, primitive compatibility or execution adequacy.

A recursive closure's third component is related by a creation-template
witness, not by pointwise interpretation as already-closed member values.
The witness does not require the associated machine cells to remain unforced.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Representation

structure Meaning (Primitive : Type) where
  body : Core.Expr Primitive
  captured : Env Primitive
  recursive : Option (Suspensions.Pure.Group Primitive)

def Meaning.value {Primitive : Type} (meaning : Meaning Primitive) : Value Primitive :=
  .suspension meaning.body meaning.captured meaning.recursive

def Meaning.environment {Primitive : Type} (meaning : Meaning Primitive) : Env Primitive :=
  bodyEnvironment meaning.captured meaning.recursive

abbrev World (Primitive : Type) := Durability.Heap (Meaning Primitive)

mutual
  inductive ValueRep {Primitive : Type} (world : World Primitive) :
      Core.Value Primitive → Value Primitive → Prop
    | atom (atom : Core.Atom) : ValueRep world (.atom atom) (.atom atom)
    | constructor {tag : Nat} {raw : Option (Core.Value Primitive)}
        {view : Option (Value Primitive)} (argument : OptionalRep world raw view) :
        ValueRep world (.constructor tag raw) (.constructor tag view)
    | record {raw : Core.Env Primitive} {view : Env Primitive}
        (fields : EnvRep world raw view) : ValueRep world (.record raw) (.record view)
    | primitive (operation : Primitive) :
        ValueRep world (.primitive operation) (.primitive operation)
    | exception {name : Nat} {raw : Option (Core.Value Primitive)}
        {view : Option (Value Primitive)} (argument : OptionalRep world raw view) :
        ValueRep world (.exception name raw) (.exception name view)
    | address {address : Nat} {meaning : Meaning Primitive}
        (found : world address = some meaning) :
        ValueRep world (.address address) meaning.value
    | closure {clauses : List (Core.Pattern × Core.Expr Primitive)}
        {raw : Core.Env Primitive} {view : Env Primitive}
        (captured : EnvRep world raw view) :
        ValueRep world (.closure clauses raw []) (.closure clauses view none)
    | recursive_closure {clauses : List (Core.Pattern × Core.Expr Primitive)}
        {raw : Core.Env Primitive} {view : Env Primitive}
        {created : Core.Env Primitive} {group : Suspensions.Pure.Group Primitive}
        (captured : EnvRep world raw view)
        (members : GroupMembersRep world group group.bindings.reverse created) :
        ValueRep world (.closure clauses raw created) (.closure clauses view (some group))

  inductive EnvRep {Primitive : Type} (world : World Primitive) :
      Core.Env Primitive → Env Primitive → Prop
    | nil : EnvRep world [] []
    | cons {name : Nat} {raw : Core.Value Primitive} {view : Value Primitive}
        {rawRest : Core.Env Primitive} {viewRest : Env Primitive}
        (head : ValueRep world raw view) (tail : EnvRep world rawRest viewRest) :
        EnvRep world ((name, raw) :: rawRest) ((name, view) :: viewRest)

  inductive OptionalRep {Primitive : Type} (world : World Primitive) :
      Option (Core.Value Primitive) → Option (Value Primitive) → Prop
    | none : OptionalRep world none none
    | some {raw : Core.Value Primitive} {view : Value Primitive}
        (value : ValueRep world raw view) : OptionalRep world (some raw) (some view)

  /-- `definitions` and `created` are in the same reversed creation order.
  Function members are the original bare closures; delayed members retain
  their immutable address meanings. This is not a current-cell predicate. -/
  inductive GroupMembersRep {Primitive : Type} (world : World Primitive) :
      Suspensions.Pure.Group Primitive → List (Nat × Rhs Primitive) → Core.Env Primitive → Prop
    | nil (group : Suspensions.Pure.Group Primitive) : GroupMembersRep world group [] []
    | function {group : Suspensions.Pure.Group Primitive} {name : Nat}
        {clauses : List (Core.Pattern × Core.Expr Primitive)} {rawCapture : Core.Env Primitive}
        {definitions : List (Nat × Rhs Primitive)} {created : Core.Env Primitive}
        (captured : EnvRep world rawCapture group.outer)
        (rest : GroupMembersRep world group definitions created) :
        GroupMembersRep world group ((name, .function clauses) :: definitions)
          ((name, .closure clauses rawCapture []) :: created)
    | delay {group : Suspensions.Pure.Group Primitive} {name address : Nat} {body : Core.Expr Primitive}
        {definitions : List (Nat × Rhs Primitive)} {created : Core.Env Primitive}
        (found : world address = some ⟨body, group.outer, some group⟩)
        (rest : GroupMembersRep world group definitions created) :
        GroupMembersRep world group ((name, .delay body) :: definitions)
          ((name, .address address) :: created)
end

def GroupRep {Primitive : Type} (world : World Primitive)
    (created : Core.Env Primitive) (group : Suspensions.Pure.Group Primitive) : Prop :=
  GroupMembersRep world group group.bindings.reverse created

theorem ValueRep.mono {Primitive : Type} {before after : World Primitive}
    (extension : Durability.Extends before after)
    {raw : Core.Value Primitive} {view : Value Primitive} (represented : ValueRep before raw view) :
    ValueRep after raw view := by
  exact ValueRep.rec
    (motive_1 := fun raw view _ => ValueRep after raw view)
    (motive_2 := fun raw view _ => EnvRep after raw view)
    (motive_3 := fun raw view _ => OptionalRep after raw view)
    (motive_4 := fun group definitions created _ => GroupMembersRep after group definitions created)
    (fun atom => .atom atom)
    (fun _ argument => .constructor argument)
    (fun _ fields => .record fields)
    (fun operation => .primitive operation)
    (fun _ argument => .exception argument)
    (fun found => .address (extension _ _ found))
    (fun _ captured => .closure captured)
    (fun _ _ captured members => .recursive_closure captured members)
    .nil
    (fun _ _ head tail => .cons head tail)
    .none
    (fun _ value => .some value)
    (fun group => .nil group)
    (fun _ _ captured rest => .function captured rest)
    (fun found _ rest => .delay (extension _ _ found) rest)
    represented

theorem EnvRep.mono {Primitive : Type} {before after : World Primitive}
    (extension : Durability.Extends before after)
    {raw : Core.Env Primitive} {view : Env Primitive} (represented : EnvRep before raw view) :
    EnvRep after raw view := by
  induction raw generalizing view with
  | nil => cases represented; exact .nil
  | cons binding rest ih =>
      cases represented with
      | cons head tail => exact .cons (head.mono extension) (ih tail)

theorem OptionalRep.mono {Primitive : Type} {before after : World Primitive}
    (extension : Durability.Extends before after)
    {raw : Option (Core.Value Primitive)} {view : Option (Value Primitive)}
    (represented : OptionalRep before raw view) : OptionalRep after raw view := by
  cases represented with
  | none => exact .none
  | some value => exact .some (value.mono extension)

theorem GroupMembersRep.mono {Primitive : Type} {before after : World Primitive}
    (extension : Durability.Extends before after)
    {group : Suspensions.Pure.Group Primitive} {definitions : List (Nat × Rhs Primitive)}
    {created : Core.Env Primitive} (represented : GroupMembersRep before group definitions created) :
    GroupMembersRep after group definitions created := by
  induction definitions generalizing created with
  | nil => cases represented; exact .nil group
  | cons binding rest ih =>
      cases represented with
      | function captured tail => exact .function (captured.mono extension) (ih tail)
      | delay found tail => exact .delay (extension _ _ found) (ih tail)

variable {Primitive : Type} {world : World Primitive}

theorem GroupRep.mono {before after : World Primitive}
    (extension : Durability.Extends before after) {created : Core.Env Primitive} {group : Suspensions.Pure.Group Primitive}
    (represented : GroupRep before created group) : GroupRep after created group :=
  GroupMembersRep.mono extension represented

theorem EnvRep.append {rawFirst rawSecond : Core.Env Primitive} {viewFirst viewSecond : Env Primitive}
    (first : EnvRep world rawFirst viewFirst) (second : EnvRep world rawSecond viewSecond) :
    EnvRep world (rawFirst ++ rawSecond) (viewFirst ++ viewSecond) := by
  induction rawFirst generalizing viewFirst with
  | nil => cases first; exact second
  | cons binding rest ih =>
      cases first with
      | cons head tail => exact .cons head (ih tail)

theorem EnvRep.extend {rawBase rawAdded : Core.Env Primitive} {viewBase viewAdded : Env Primitive}
    (base : EnvRep world rawBase viewBase) (added : EnvRep world rawAdded viewAdded) :
    EnvRep world (Core.Env.extend rawBase rawAdded) (Env.extend viewBase viewAdded) :=
  added.append base

theorem EnvRep.lookup {raw : Core.Env Primitive} {view : Env Primitive}
    (represented : EnvRep world raw view) (name : Nat) :
    OptionalRep world (Core.Env.lookup raw name) (Env.lookup view name) := by
  induction raw generalizing view with
  | nil => cases represented; exact .none
  | cons binding rest ih =>
      rcases binding with ⟨key, rawValue⟩
      cases represented with
      | cons head tail =>
          by_cases same : name = key
          · simpa [Core.Env.lookup, Env.lookup, same] using OptionalRep.some head
          · simpa [Core.Env.lookup, Env.lookup, same] using ih tail

theorem EnvRep.names {raw : Core.Env Primitive} {view : Env Primitive}
    (represented : EnvRep world raw view) : raw.map Prod.fst = view.map Prod.fst := by
  induction raw generalizing view with
  | nil => cases represented; rfl
  | cons binding rest ih =>
      rcases binding with ⟨name, rawValue⟩
      cases represented with
      | cons head tail => simpa using congrArg (List.cons name) (ih tail)

private theorem GroupMembersRep.unroll_each {group : Suspensions.Pure.Group Primitive}
    {definitions : List (Nat × Rhs Primitive)} {created : Core.Env Primitive}
    (represented : GroupMembersRep world group definitions created)
    {complete : Core.Env Primitive} (whole : GroupRep world complete group) :
    EnvRep world
      (created.map fun (name, value) => (name, Core.Env.unrollValue complete value))
      (definitions.map fun (name, rhs) => (name, rhs.instantiate group)) := by
  induction definitions generalizing created with
  | nil => cases represented; exact .nil
  | cons binding rest ih =>
      cases represented with
      | function captured tail => exact .cons (.recursive_closure captured whole) (ih tail)
      | delay found tail => exact .cons (.address found) (ih tail)

/-- One actual `Rec` unrolling uses the same finite descriptor for every
function/suspension member. No cyclic semantic value or current-thunk premise
is used to construct this representation. -/
theorem GroupRep.unroll {created : Core.Env Primitive} {group : Suspensions.Pure.Group Primitive}
    (represented : GroupRep world created group) :
    EnvRep world (Core.Env.rec created) group.members :=
  GroupMembersRep.unroll_each represented represented

theorem GroupRep.bodyEnvironment {rawCapture created : Core.Env Primitive}
    {capture : Env Primitive} {group : Suspensions.Pure.Group Primitive}
    (represented : GroupRep world created group) (captured : EnvRep world rawCapture capture) :
    EnvRep world (Core.Env.extend rawCapture (Core.Env.rec created))
      (bodyEnvironment capture (some group)) :=
  captured.extend represented.unroll

end Suspensions.Pure.Representation
