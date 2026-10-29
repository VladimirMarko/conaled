import Applications.Durability.Executions
import Applications.Resources.Measured

namespace Durability

/-- Primitive storage observations. They are not wall-clock times or byte sizes.
Volatile planning, admission searches and codec work require additional models. -/
inductive StorageEvent where
  | write | persist | installRoot | readRecord | followLink | readRoot | readDescriptor
  | reclaimCell | query | crash
  deriving DecidableEq

/-- This interface instruments selected storage transitions, preserving their
preconditions. A complete algorithm cost model must also charge planning and
client work; these annotations alone make no total-cost claim. -/
inductive StorageStep {P : Type} : List StorageEvent → Machine P → Machine P → Prop
  | write {s p i c} : s.pending = some p → p.writes i = some c →
      StorageStep [.write] s (writeState s i c)
  | persist {s p i c} : s.pending = some p → p.writes i = some c →
      s.buffered i = some c → (s.disk i = none ∨ s.disk i = some c) →
      StorageStep [.persist] s (persistState s i c)
  | publish {s p} : s.pending = some p → Extends p.writes s.disk →
      StorageStep [.installRoot] s (publishState s p)
  | readFlat {s a as seen tip e} : s.cache = none →
      s.cursor = some (.prefixCells (a :: as) seen tip) → s.disk a = some (.flat e) →
      StorageStep [.readRecord] s { s with cursor := some (.prefixCells as (seen ++ [e]) tip) }
  | readNode {s a prev e pre suffix} : s.cache = none →
      s.cursor = some (.tailCells (some a) pre suffix) → s.disk a = some (.node prev e) →
      StorageStep [.readRecord, .followLink] s { s with cursor := some (.tailCells prev pre (e :: suffix)) }
  | readLogRoot {s} : s.cache = none → s.cursor = none → s.root.checkpoint = none →
      StorageStep [.readRoot] s { s with cursor := some (.tailCells s.root.tail [] []) }
  | readCheckpointRoot {s a as} : s.cache = none → s.cursor = none →
      s.root.checkpoint = some a → s.disk a = some (.index as) →
      StorageStep [.readRoot, .readDescriptor] s { s with cursor := some (.prefixCells as [] s.root.tail) }
  | reclaim {s h i} : s.cache = some h → s.active = none → s.pending = none →
      (∃ c, s.disk i = some c) → ¬ RootNeeds s.disk s.root i →
      StorageStep [.reclaimCell] s { s with disk := fun a => if a = i then none else s.disk a }
  | query {s h} : s.cache = some h → s.active = none → s.pending = none →
      StorageStep [.query] s s
  | crash {s} : StorageStep [.crash] s (crashState s)

theorem StorageStep.sound {P : Type} {events s t} (step : @StorageStep P events s t) :
    ∃ ev, Step ev s t := by
  cases step with
  | write hp hw => exact ⟨_, .write hp hw⟩
  | persist hp hw hb compatible => exact ⟨_, .persist hp hw hb compatible⟩
  | publish hp persisted => exact ⟨_, .publish hp persisted⟩
  | readFlat hc cur lookup => exact ⟨_, .read hc cur (.flat lookup)⟩
  | readNode hc cur lookup => exact ⟨_, .read hc cur (.node lookup)⟩
  | readLogRoot hc cur empty => exact ⟨_, .startRead hc cur (.log empty)⟩
  | readCheckpointRoot hc cur ptr lookup => exact ⟨_, .startRead hc cur (.checkpoint ptr lookup)⟩
  | @reclaim s h i hc ha hp allocated unreachable =>
    refine ⟨_, Step.reclaim hc ha hp ?_ ?_⟩
    · intro a c needed found
      have ne : a ≠ i := by intro eq; subst a; exact unreachable needed
      simp [ne, found]
    · intro a c found
      split at found
      · cases found
      · exact found
  | query hc ha hp => exact ⟨_, .query hc ha hp⟩
  | crash => exact ⟨_, .crash⟩

/-- Counts retain every primitive weight until the caller chooses a target. -/
def weighted (weight : StorageEvent → Nat) (events : List StorageEvent) : Nat :=
  (events.map weight).sum

theorem weighted_append (weight : StorageEvent → Nat) (xs ys : List StorageEvent) :
    weighted weight (xs ++ ys) = weighted weight xs + weighted weight ys := by
  simp [weighted]

/-- Existing measured reweighting changes the observation only. -/
theorem reweight_storage (weight : StorageEvent → Nat) (events : List StorageEvent) :
    (Resources.reweight (weighted weight) (((), events) : Resources.Measured Unit (List StorageEvent))).1 = () :=
  Resources.reweight_value _ _

end Durability
