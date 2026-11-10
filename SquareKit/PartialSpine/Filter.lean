import SquareKit.PartialSpine.Limits

/-!
# Partial-predicate filtering of observations

Undefined, rejected and accepted tests have different meanings. Filtering uses
the existing semantic fold and strict fusion. Predicate fusion evaluates the
inner test first; finite completed and open prefixes retain their distinct ends.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace SquareKit.PartialSpine.Observations

open Order

universe u v
variable {α : Type u} {β : Type v}

/-- Undefined tests yield bottom; rejection keeps the tail; acceptance keeps the cons. -/
def filterStep (p : α → Option Bool) (a : α) (I : Observations α) : Observations α :=
  match p a with
  | none => ⊥
  | some false => I
  | some true => cons a I

theorem filterStep_continuous (p : α → Option Bool) (a : α) : ScottContinuous (filterStep p a) := by
  unfold filterStep
  cases p a with
  | none => exact ScottContinuous.const ⊥
  | some b => cases b with
    | false => exact ScottContinuous.id
    | true => exact cons_continuous a

def filter (p : α → Option Bool) (I : Observations α) : Observations α :=
  foldr (filterStep p) (Ideal.principal .nil) I

theorem filter_continuous (p : α → Option Bool) : ScottContinuous (filter p) :=
  foldr_continuous (filterStep p) (Ideal.principal .nil)
    (fun a => (filterStep_continuous p a).monotone)

@[simp] theorem filter_bottom (p : α → Option Bool) : filter p ⊥ = ⊥ :=
  foldr_bottom (filterStep p) (Ideal.principal .nil)
    (fun a => (filterStep_continuous p a).monotone)

@[simp] theorem filter_nil (p : α → Option Bool) :
    filter p (Ideal.principal .nil) = Ideal.principal .nil :=
  foldr_nil (filterStep p) (Ideal.principal .nil)
    (fun a => (filterStep_continuous p a).monotone)

theorem filter_cons (p : α → Option Bool) (a : α) (I : Observations α) :
    filter p (cons a I) = filterStep p a (filter p I) :=
  foldr_cons (filterStep p) (Ideal.principal .nil)
    (fun a => (filterStep_continuous p a).monotone) a (filterStep_continuous p a) I

theorem filter_ofList (p : α → Bool) (xs : List α) :
    filter (fun a => some (p a)) (Ideal.principal (ofList xs)) =
      Ideal.principal (ofList (xs.filter p)) := by
  induction xs with
  | nil => exact filter_nil _
  | cons a xs ih =>
    rw [ofList_cons, ← cons_principal, filter_cons, ih]
    cases hp : p a <;> simp [filterStep, hp]

/-- Total finite tests retain an unknown end when the input supplies only a prefix. -/
theorem filter_openPrefix (p : α → Bool) (xs : List α) :
    filter (fun a => some (p a)) (Ideal.principal (openPrefix xs)) =
      Ideal.principal (openPrefix (xs.filter p)) := by
  induction xs with
  | nil => exact filter_bottom _
  | cons a xs ih =>
    rw [openPrefix_cons, ← cons_principal, filter_cons, ih]
    cases hp : p a <;> simp [filterStep, hp]

/-- The standard directed stream-prefix limit specializes to filtered open prefixes. -/
theorem filter_stream_prefixes_isLUB (p : α → Bool) (σ : Stream' α) :
    IsLUB (Set.range fun n => Ideal.principal (openPrefix ((σ.take n).filter p)))
      (filter (fun a => some (p a)) (stream σ)) := by
  have prefixes : filter (fun a => some (p a)) ''
      (Set.range fun n => Ideal.principal (openPrefix (σ.take n))) =
      Set.range (fun n => Ideal.principal (openPrefix ((σ.take n).filter p))) := by
    rw [← Set.range_comp']
    simp only [filter_openPrefix]
  have lub := filter_continuous (fun a => some (p a)) (Set.range_nonempty _)
    (stream_prefixes_directed σ) (stream_prefixes_isLUB σ)
  rw [prefixes] at lub
  exact lub

/-- Inner undefined/rejection does not inspect the outer predicate. -/
def fusedPredicate (outer inner : α → Option Bool) (a : α) : Option Bool :=
  match inner a with
  | none => none
  | some false => some false
  | some true => outer a

theorem filter_step_commute (p q : α → Option Bool) (a : α) (I : Observations α) :
    filter p (filterStep q a I) = filterStep (fusedPredicate p q) a (filter p I) := by
  cases hq : q a with
  | none => simp only [filterStep, hq, fusedPredicate, filter_bottom]
  | some b => cases b <;> simp only [filterStep, hq, fusedPredicate, filter_cons]

theorem filter_fusion (p q : α → Option Bool) (I : Observations α) :
    filter p (filter q I) = filter (fusedPredicate p q) I := by
  have fused := foldr_fusion (filterStep q) (filterStep (fusedPredicate p q))
    (Ideal.principal .nil) (fun a => (filterStep_continuous q a).monotone)
    (fun a => (filterStep_continuous (fusedPredicate p q) a).monotone)
    (filter p) (filter_continuous p) (filter_bottom p) (filter_step_commute p q) I
  change filter p (filter q I) =
    foldr (filterStep (fusedPredicate p q)) (filter p (Ideal.principal .nil)) I at fused
  rw [filter_nil] at fused
  exact fused

theorem fusedPredicate_total (p q : α → Bool) (a : α) :
    fusedPredicate (fun x => some (p x)) (fun x => some (q x)) a =
      some (q a && p a) := by
  cases hq : q a <;> simp only [fusedPredicate, hq, Bool.false_and, Bool.true_and]

theorem filter_fusion_total (p q : α → Bool) (I : Observations α) :
    filter (fun a => some (p a)) (filter (fun a => some (q a)) I) =
      filter (fun a => some (q a && p a)) I := by
  rw [filter_fusion]
  apply congrArg (fun r => filter r I)
  funext a
  exact fusedPredicate_total p q a

theorem filter_true (I : Observations α) : filter (fun _ => some true) I = I :=
  foldr_cons_identity I

section Fold

variable [CompletePartialOrder β]

/-- The arbitrary fold algebra retains undefined, rejected and accepted tests. -/
def filteredStep (f : α → β → β) (p : α → Option Bool) (a : α) (b : β) : β :=
  match p a with
  | none => ⊥
  | some false => b
  | some true => f a b

theorem filteredStep_continuous (f : α → β → β)
    (continuous : ∀ a, ScottContinuous (f a)) (p : α → Option Bool) (a : α) :
    ScottContinuous (filteredStep f p a) := by
  unfold filteredStep
  cases p a with
  | none => exact ScottContinuous.const ⊥
  | some b => cases b with
    | false => exact ScottContinuous.id
    | true => exact continuous a

theorem foldr_filter_step_commute (f : α → β → β) (e : β)
    (continuous : ∀ a, ScottContinuous (f a)) (p : α → Option Bool) (a : α)
    (I : Observations α) :
    foldr f e (filterStep p a I) = filteredStep f p a (foldr f e I) := by
  cases hp : p a with
  | none =>
    simp only [filterStep, filteredStep, hp]
    exact foldr_bottom f e (fun a => (continuous a).monotone)
  | some b => cases b with
    | false => simp only [filterStep, filteredStep, hp]
    | true =>
      simp only [filterStep, filteredStep, hp]
      exact foldr_cons f e (fun a => (continuous a).monotone) a (continuous a) I

/-- Strict continuous fold fusion preserves the arbitrary seed after nil evaluation. -/
theorem foldr_filter (f : α → β → β) (e : β) (continuous : ∀ a, ScottContinuous (f a))
    (p : α → Option Bool) (I : Observations α) :
    foldr f e (filter p I) = foldr (filteredStep f p) e I := by
  have fused := foldr_fusion (filterStep p) (filteredStep f p) (Ideal.principal .nil)
    (fun a => (filterStep_continuous p a).monotone)
    (fun a => (filteredStep_continuous f continuous p a).monotone)
    (foldr f e) (foldr_continuous f e (fun a => (continuous a).monotone))
    (foldr_bottom f e (fun a => (continuous a).monotone))
    (foldr_filter_step_commute f e continuous p) I
  change foldr f e (filter p I) =
    foldr (filteredStep f p) (foldr f e (Ideal.principal .nil)) I at fused
  rw [foldr_nil f e (fun a => (continuous a).monotone)] at fused
  exact fused

end Fold

/-- All rejected infinite observations have bottom denotation, without a runtime claim. -/
theorem filter_stream_all_false (p : α → Option Bool) (σ : Stream' α)
    (rejected : ∀ n, p (σ n) = some false) : filter p (stream σ) = ⊥ := by
  have finite : ∀ (τ : Stream' α), (∀ n, p (τ n) = some false) → ∀ n,
      PartialSpine.foldr (⊥ : Observations α) (filterStep p) (Ideal.principal .nil)
        (openPrefix (τ.take n)) = ⊥ := by
    intro τ hτ n
    induction n generalizing τ with
    | zero => rfl
    | succ n ih =>
      change filterStep p (τ 0)
        (PartialSpine.foldr ⊥ (filterStep p) (Ideal.principal .nil)
          (openPrefix (Stream'.take n (fun k => τ (k + 1))))) = ⊥
      rw [filterStep, hτ 0]
      exact ih _ (fun k => hτ (k + 1))
  apply le_antisymm
  · apply foldr_le (filterStep p) (Ideal.principal .nil)
      (fun a => (filterStep_continuous p a).monotone)
    rintro s ⟨n, hn⟩
    have bound := finiteFold_monotone (filterStep p) (Ideal.principal .nil)
      (fun a => (filterStep_continuous p a).monotone) hn
    rw [finite σ rejected n] at bound
    exact bound
  · exact bot_le

end SquareKit.PartialSpine.Observations
