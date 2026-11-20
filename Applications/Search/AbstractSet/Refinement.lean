import Applications.Search.AbstractSet.Deletion

/-!
# Set contracts from operational refinement and an auxiliary invariant

The source validity is the conjunction of an independent auxiliary invariant
and target validity after observation. Only the auxiliary part is separately
preserved by the primitive assumptions. Target closure and the actual
commuting equations derive the rest; no final source set law is assumed.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.AbstractSet
universe u v w
variable {α : Type u} {S : Type v} {T : Type w}

structure Refinement (source : DeleteOps α S) (target : DeleteOps α T)
    (view : S → T) (Aux : S → Prop) (TargetValid : T → Prop) : Prop where
  empty : view source.empty = target.empty
  auxiliary_empty : Aux source.empty
  insert : ∀ x s, Aux s → TargetValid (view s) →
    view (source.insert x s) = target.insert x (view s)
  auxiliary_insert : ∀ x s, Aux s → TargetValid (view s) → Aux (source.insert x s)
  delete : ∀ x s, Aux s → TargetValid (view s) →
    view (source.delete x s) = target.delete x (view s)
  auxiliary_delete : ∀ x s, Aux s → TargetValid (view s) → Aux (source.delete x s)
  member : ∀ x s, Aux s → TargetValid (view s) →
    source.member x s = target.member x (view s)

def Refinement.Valid (view : S → T) (Aux : S → Prop) (TargetValid : T → Prop) :
    S → Prop := fun s => Aux s ∧ TargetValid (view s)

theorem Refinement.laws {source : DeleteOps α S} {target : DeleteOps α T}
    {view : S → T} {Aux : S → Prop} {TargetValid : T → Prop}
    {observe : T → α → Prop}
    (refinement : Refinement source target view Aux TargetValid)
    (targetLaws : DeleteLaws target observe TargetValid) :
    DeleteLaws source (fun s => observe (view s))
      (Refinement.Valid view Aux TargetValid) where
  empty_valid := by
    refine ⟨refinement.auxiliary_empty, ?_⟩
    rw [refinement.empty]
    exact targetLaws.empty_valid
  empty x := by
    rw [refinement.empty]
    exact targetLaws.empty x
  insert_valid x s hs := by
    refine ⟨refinement.auxiliary_insert x s hs.1 hs.2, ?_⟩
    rw [refinement.insert x s hs.1 hs.2]
    exact targetLaws.insert_valid x (view s) hs.2
  insert x s hs y := by
    rw [refinement.insert x s hs.1 hs.2]
    exact targetLaws.insert x (view s) hs.2 y
  member x s hs := by
    rw [refinement.member x s hs.1 hs.2]
    exact targetLaws.member x (view s) hs.2
  delete_valid x s hs := by
    refine ⟨refinement.auxiliary_delete x s hs.1 hs.2, ?_⟩
    rw [refinement.delete x s hs.1 hs.2]
    exact targetLaws.delete_valid x (view s) hs.2
  delete x s hs y := by
    rw [refinement.delete x s hs.1 hs.2]
    exact targetLaws.delete x (view s) hs.2 y

/-- Actual observed states commute for every mixed word. This is stronger
than merely obtaining the same final set, and does not require view injective. -/
theorem Refinement.execute {source : DeleteOps α S} {target : DeleteOps α T}
    {view : S → T} {Aux : S → Prop} {TargetValid : T → Prop}
    {observe : T → α → Prop}
    (refinement : Refinement source target view Aux TargetValid)
    (targetLaws : DeleteLaws target observe TargetValid)
    (updates : List (Update α)) {s : S}
    (hs : Refinement.Valid view Aux TargetValid s) :
    view (execute source updates s) = execute target updates (view s) := by
  apply SquareKit.ListFusion.foldl_reachable (step source) (step target) view
    (Refinement.Valid view Aux TargetValid) s hs
  · exact fun q update hq => (refinement.laws targetLaws).step_valid q update hq
  · intro q update hq
    cases update with
    | insert x => exact refinement.insert x q hq.1 hq.2
    | delete x => exact refinement.delete x q hq.1 hq.2

theorem Refinement.member_execute {source : DeleteOps α S} {target : DeleteOps α T}
    {view : S → T} {Aux : S → Prop} {TargetValid : T → Prop}
    {observe : T → α → Prop}
    (refinement : Refinement source target view Aux TargetValid)
    (targetLaws : DeleteLaws target observe TargetValid)
    (updates : List (Update α)) {s : S}
    (hs : Refinement.Valid view Aux TargetValid s) (x : α) :
    source.member x (Search.AbstractSet.execute source updates s) =
      target.member x (Search.AbstractSet.execute target updates (view s)) := by
  have valid := (refinement.laws targetLaws).execute_valid updates hs
  rw [refinement.member x _ valid.1 valid.2,
    refinement.execute targetLaws updates hs]

theorem Refinement.execute_from_empty {source : DeleteOps α S} {target : DeleteOps α T}
    {view : S → T} {Aux : S → Prop} {TargetValid : T → Prop}
    {observe : T → α → Prop}
    (refinement : Refinement source target view Aux TargetValid)
    (targetLaws : DeleteLaws target observe TargetValid) (updates : List (Update α)) :
    view (Search.AbstractSet.execute source updates source.empty) =
      Search.AbstractSet.execute target updates target.empty := by
  rw [refinement.execute targetLaws updates (refinement.laws targetLaws).empty_valid,
    refinement.empty]

end Search.AbstractSet
