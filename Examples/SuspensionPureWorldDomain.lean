import Applications.Suspensions.Pure.WorldDomain
import Examples.SuspensionPureDomain

/-!
# World admissibility follows actual delay and recursive creation

The literal case composes actual delay/cache transitions with the independent
state and code-domain laws. The cache's pure value and count are recovered from
its existing evaluation witness. The mutual recursive group is created and
closed without evaluating its cyclic body; its immutable world is allowed
through the public pending-template theorem.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureWorldDomain
open Suspensions Suspensions.Pure Suspensions.Pure.Representation
open Suspensions.Pure.Domain Suspensions.Pure.WorldDomain

namespace Literal
open Compatibility

private def selected : BasicOperation → Prop := fun _ => True
private def parameters : Machine.Parameters BasicOperation := basicPureParameters 10 11
private def rawParameters : Core.Machine.Parameters BasicOperation := basicRawParameters 10 11

def body : Core.Expr BasicOperation := .atom (.integer 41)
def meaning : Meaning BasicOperation := ⟨body, [], none⟩
def world : World BasicOperation := Durability.put (fun _ => none) 0 meaning
def delayed : Core.Machine.Memory BasicOperation :=
  (Suspensions.delay Suspensions.empty body []).1
def cached : Core.Machine.Memory BasicOperation :=
  Suspensions.memoize delayed 0 (.atom (.integer 41))

private theorem code : CodeAllowed selected body := CodeAllowed.atom (.integer 41)

private theorem delay_properties :
    Memory.StateRep parameters world delayed ∧ WorldAllowed selected world := by
  have allocated := (WorldAllowed.empty (operations := selected)).delay
    (Memory.StateRep.empty parameters) EnvRep.nil EnvAllowed.nil code
  exact ⟨allocated.2.1, allocated.2.2.1⟩

/-- Actual delay enters the expected address and allocates precisely the
unforced source body; its world/state obligations come from the composed law. -/
theorem actual_delay_allowed :
    Core.Machine.transition rawParameters
        (Core.Machine.start Suspensions.empty [] (.delay body)) =
      Core.Machine.proceed delayed (.value (.address 0)) [] (.allocate 0) ∧
    delayed.next = 1 ∧ delayed.memory 0 = some (.thunk body []) ∧
    Memory.StateRep parameters world delayed ∧ WorldAllowed selected world :=
  ⟨rfl, rfl, rfl, delay_properties⟩

private theorem body_evaluation :
    Progress.Evaluates (Machine.step parameters)
      (Machine.start meaning.environment meaning.body) (.value (.atom (.integer 41))) 2 :=
  .next rfl (.done rfl)

private theorem cached_state : Memory.StateRep parameters world cached :=
  delay_properties.1.memoize (address := 0) (meaning := meaning) rfl
    (.atom (.integer 41)) body_evaluation

/-- The actual cache transition and represented cached cell retain their pure
witness. Domain preservation derives its admissible result; uniqueness checks
the independently expected integer 41 and two-transition body count. -/
theorem actual_cache_allowed :
    Core.Machine.transition rawParameters
        ⟨delayed, .value (.atom (.integer 41)), [.memoize 0 [] .wildcard]⟩ =
      Core.Machine.proceed cached (.pattern [] .wildcard (.atom (.integer 41))) [] (.cacheWrite 0) ∧
    Memory.StateRep parameters world cached ∧ WorldAllowed selected world ∧
    (∃ view steps, ValueRep world (.atom (.integer 41)) view ∧
      Progress.Evaluates (Machine.step parameters)
        (Machine.start meaning.environment meaning.body) (.value view) steps ∧
      ValueAllowed selected view ∧ view = .atom (.integer 41) ∧ steps = 2) := by
  obtain ⟨view, steps, represented, evaluation, allowed⟩ :=
    cached_lookup_allowed (basic_parameters_preserve selected 10 11)
      delay_properties.2 cached_state (address := 0) (meaning := meaning) rfl rfl
  have same := evaluation.unique body_evaluation
  exact ⟨rfl, cached_state, delay_properties.2, view, steps, represented, evaluation, allowed,
    Machine.Result.value.inj same.1, same.2⟩

end Literal

namespace Mutual
open Examples.SuspensionPureValues

private def noOperations : Unit → Prop := fun _ => False
private def emptyWorld : World Unit := fun _ => none
def rawOuter : Core.Env Unit := [(1, .atom (.integer 99)), (9, .atom (.boolean true))]
def preclose : Core.Machine.Memory Unit :=
  (Suspensions.delay Suspensions.empty mutualSuspensionBody rawOuter).1
def created : Core.Env Unit :=
  [(2, .address 0), (1, .closure mutualClauses rawOuter [])]
def closed : Core.Machine.Memory Unit := Core.Recursive.closeMemory preclose created
def closedEnvironment : Core.Env Unit := Core.Recursive.closeEnvironment rawOuter created
def meaning : Meaning Unit := ⟨mutualSuspensionBody, mutualOuter, some mutualGroup⟩

private theorem outer_represented : EnvRep emptyWorld rawOuter mutualOuter :=
  .cons (.atom (.integer 99)) (.cons (.atom (.boolean true)) .nil)

private theorem group_allowed : GroupAllowed noOperations mutualGroup :=
  Examples.SuspensionPureDomain.mutual_group_allowed

private theorem receipt :
    Core.Recursive.create Suspensions.empty rawOuter (Rhs.toBindings mutualBindings) [] =
      .ok (preclose, created) := rfl

/-- The actual cyclic group receives allowed immutable meanings before any
body evaluation. Closing preserves state validity and the eight-transition
prefix ends just before forcing the newly created suspension. -/
theorem actual_recursive_world_allowed (parameters : Machine.Parameters Unit)
    (raw : Core.Machine.Parameters Unit) :
    ∃ world,
      Creation.PendingGroup emptyWorld world Suspensions.empty preclose rawOuter mutualGroup created ∧
      WorldAllowed noOperations world ∧ Memory.StateRep parameters world closed ∧
      world 0 = some meaning ∧ CodeAllowed noOperations meaning.body ∧
      EnvAllowed noOperations meaning.environment ∧
      Core.Prefix.observe raw 8
        (Core.Machine.start Suspensions.empty rawOuter
          (.recursive (Rhs.toBindings mutualBindings) (Core.force (.variable 2)))) =
        .inr (Core.Machine.start closed closedEnvironment (Core.force (.variable 2))) := by
  have initial := Memory.StateRep.empty parameters
  obtain ⟨world, pending⟩ := Creation.create_pending initial.bounded initial.world_below
    outer_represented group_allowed.distinct receipt
  have allowed := pending_allowed pending (WorldAllowed.empty (operations := noOperations)) group_allowed
  have found : world 0 = some meaning := by
    have members := pending.members
    cases members with
    | delay address rest => exact address
  have meaningAllowed := allowed 0 meaning found
  exact ⟨world, pending, allowed, pending.closed_state initial outer_represented receipt,
    found, meaning_code meaningAllowed, meaning_environment meaningAllowed,
    Core.Recursive.enter_body_prefix (Rhs.toBindings_permitted mutualBindings)
      receipt (Core.force (.variable 2))⟩

end Mutual

namespace Overwrite

private def noOperations : Unit → Prop := fun _ => False
private def first : Meaning Unit := ⟨.atom (.integer 7), [], none⟩
private def second : Meaning Unit := ⟨.atom (.integer 8), [], none⟩
private def before : World Unit := Durability.put (fun _ => none) 0 first
private def after : World Unit := Durability.put before 0 second

/-- Code admissibility survives this overwrite, while immutable extension
does not. Freshness must still be supplied by the separate storage theorem. -/
theorem allowed_put_is_not_extension :
    WorldAllowed noOperations before ∧ WorldAllowed noOperations after ∧
      ¬Durability.Extends before after := by
  have old : WorldAllowed noOperations before :=
    (WorldAllowed.empty (operations := noOperations)).put 0 first
      (.suspension (CodeAllowed.atom (.integer 7)) .nil .none)
  have new : WorldAllowed noOperations after :=
    old.put 0 second (.suspension (CodeAllowed.atom (.integer 8)) .nil .none)
  refine ⟨old, new, ?_⟩
  intro extension
  have occupied := extension 0 first rfl
  have equal : second = first := Option.some.inj occupied
  have impossible := congrArg Meaning.body equal
  cases impossible

end Overwrite
end Examples.SuspensionPureWorldDomain
