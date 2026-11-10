import Applications.Optimization.SelectionMap

/-! Finite admissible choice. Ranking establishes no semantic law: callers lift
membership through their own contract, including relational contracts. -/
namespace Optimization.Choice
universe u v w
variable {C : Type u} {D : Type v} {K : Type w} [LinearOrder K]

def select (catalog : List C) (admitted : C → Prop) [DecidablePred admitted]
    (score : C → K) : Option C :=
  Thinning.argmin score (catalog.filter fun c => decide (admitted c))

theorem selected {catalog : List C} {admitted : C → Prop} [DecidablePred admitted]
    {score : C → K} {c : C} (h : select catalog admitted score = some c) :
    c ∈ minimizers {x | x ∈ catalog ∧ admitted x} score := by
  simpa only [List.mem_filter, decide_eq_true_eq] using
    Thinning.argmin_correct score _ c h

/-- The contract can mention the request, execution, allowed outcomes, or bounds.
It need not identify all admitted candidates or their outputs. -/
theorem selected_contract {catalog : List C} {admitted : C → Prop} [DecidablePred admitted]
    {score : C → K} {c : C} (contract : C → Prop)
    (laws : ∀ x ∈ catalog, admitted x → contract x)
    (h : select catalog admitted score = some c) : contract c :=
  laws c (selected h).1.1 (selected h).1.2

theorem select_none_iff (catalog : List C) (admitted : C → Prop) [DecidablePred admitted]
    (score : C → K) : select catalog admitted score = none ↔
      ∀ c ∈ catalog, ¬ admitted c := by
  simp [select, Thinning.argmin_eq_none_iff, List.filter_eq_nil_iff]

/-- Pull admission and ranking back through a known enclosing context. This
preserves the exact selected witness, including the existing first-tie rule. -/
theorem select_map (embed : C → D) (catalog : List C)
    (admitted : D → Prop) [DecidablePred admitted] (score : D → K) :
    select (catalog.map embed) admitted score =
      (select catalog (fun c => admitted (embed c)) (score ∘ embed)).map embed := by
  have hf : (catalog.map embed).filter (fun d => decide (admitted d)) =
      (catalog.filter (fun c => decide (admitted (embed c)))).map embed := by
    induction catalog with
    | nil => rfl
    | cons c cs ih => by_cases h : admitted (embed c) <;> simp [h, ih]
  unfold select
  rw [hf, Thinning.argmin_map]

end Optimization.Choice
