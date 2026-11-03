import Applications.Connectivity.Observation

/-! Find and union operations carry no correctness assumptions. Requests use
both finds from their own representation, with explicit rejection outcomes. -/
set_option autoImplicit false
set_option warningAsError true

namespace Connectivity

structure Ops (σ α ρ : Type*) where
  find : σ → α → Option ρ
  union : ρ → ρ → σ → Option σ

inductive RequestResult (σ : Type*) where
  | missingVertex
  | alreadyConnected
  | unionFailed
  | merged (state : σ)
  deriving DecidableEq, Repr

variable {σ α ρ : Type*} [DecidableEq ρ]

def query (ops : Ops σ α ρ) (s : σ) (u v : α) : Option Bool :=
  match ops.find s u, ops.find s v with
  | some a, some b => some (decide (a = b))
  | _, _ => none

def request (ops : Ops σ α ρ) (s : σ) (u v : α) : RequestResult σ :=
  match ops.find s u, ops.find s v with
  | some a, some b =>
      if a = b then .alreadyConnected
      else match ops.union a b s with
        | none => .unionFailed
        | some out => .merged out
  | _, _ => .missingVertex

/-- An edge is retained exactly when both endpoints exist and are disconnected. -/
def retainEdge (ops : Ops σ α ρ) (s : σ) (edge : α × α) : Option Bool :=
  (query ops s edge.1 edge.2).map Bool.not

theorem query_true_iff (ops : Ops σ α ρ) (s : σ) (u v : α) :
    query ops s u v = some true ↔ ∃ r, ops.find s u = some r ∧ ops.find s v = some r := by
  cases hu : ops.find s u <;> cases hv : ops.find s v <;> simp [query, hu, hv]
  exact eq_comm

theorem query_none_iff (ops : Ops σ α ρ) (s : σ) (u v : α) :
    query ops s u v = none ↔ ops.find s u = none ∨ ops.find s v = none := by
  cases hu : ops.find s u <;> cases hv : ops.find s v <;> simp [query, hu, hv]

theorem request_merged_iff (ops : Ops σ α ρ) (s out : σ) (u v : α) :
    request ops s u v = .merged out ↔
      ∃ a b, ops.find s u = some a ∧ ops.find s v = some b ∧ a ≠ b ∧
        ops.union a b s = some out := by
  cases hu : ops.find s u <;> cases hv : ops.find s v <;> simp [request, hu, hv]
  rename_i a b
  by_cases h : a = b
  · simp [h]
  · cases ops.union a b s <;> simp [h]

theorem request_already_iff (ops : Ops σ α ρ) (s : σ) (u v : α) :
    request ops s u v = .alreadyConnected ↔ query ops s u v = some true := by
  cases hu : ops.find s u <;> cases hv : ops.find s v <;> simp [request, query, hu, hv]
  rename_i a b
  by_cases h : a = b
  · simp [h]
  · cases hm : ops.union a b s <;> simp [h]

theorem request_missing_iff (ops : Ops σ α ρ) (s : σ) (u v : α) :
    request ops s u v = .missingVertex ↔ query ops s u v = none := by
  cases hu : ops.find s u <;> cases hv : ops.find s v <;> simp [request, query, hu, hv]
  rename_i a b
  by_cases h : a = b
  · simp [h]
  · cases hm : ops.union a b s <;> simp [h]

/-- Laws of an implementation relative to an independent observation. -/
structure QueryLaws {σ α ρ : Type*} (ops : Ops σ α ρ) (state : σ)
    (vs : Finset α) (edges : List (α × α)) : Prop where
  domain : ∀ v, (∃ r, ops.find state v = some r) ↔ v ∈ vs
  connectivity : ∀ u v, (∃ r, ops.find state u = some r ∧ ops.find state v = some r) ↔
    Connected vs edges u v

theorem QueryLaws.query_eq {σ α ρ : Type*} [DecidableEq ρ]
    {ops : Ops σ α ρ} {s : σ} {vs : Finset α} {edges : List (α × α)}
    (h : QueryLaws ops s vs edges) (u v : α) : query ops s u v = observe vs edges u v := by
  have ht : query ops s u v = some true ↔ observe vs edges u v = some true :=
    (query_true_iff ops s u v).trans ((h.connectivity u v).trans (observe_true_iff ..).symm)
  have missing (w : α) : ops.find s w = none ↔ w ∉ vs := by
    rw [← h.domain w]
    cases ops.find s w <;> simp
  have hn : query ops s u v = none ↔ observe vs edges u v = none := by
    rw [query_none_iff, missing, missing, observe_none_iff]
    tauto
  cases hq : query ops s u v with
  | none => exact ((hn.mp hq).symm)
  | some b =>
    cases ho : observe vs edges u v with
    | none => have := hn.mpr ho; simp [hq] at this
    | some c => cases b <;> cases c <;> simp_all

theorem QueryLaws.request_already {σ α ρ : Type*} [DecidableEq ρ]
    {ops : Ops σ α ρ} {s : σ} {vs : Finset α} {edges : List (α × α)}
    (h : QueryLaws ops s vs edges) (u v : α) :
    request ops s u v = .alreadyConnected ↔ Connected vs edges u v := by
  rw [request_already_iff, h.query_eq, observe_true_iff]

theorem QueryLaws.request_missing {σ α ρ : Type*} [DecidableEq ρ]
    {ops : Ops σ α ρ} {s : σ} {vs : Finset α} {edges : List (α × α)}
    (h : QueryLaws ops s vs edges) (u v : α) :
    request ops s u v = .missingVertex ↔ ¬ (u ∈ vs ∧ v ∈ vs) := by
  rw [request_missing_iff, h.query_eq, observe_none_iff]

theorem QueryLaws.retain_iff {σ α ρ : Type*} [DecidableEq ρ]
    {ops : Ops σ α ρ} {s : σ} {vs : Finset α} {edges : List (α × α)}
    (h : QueryLaws ops s vs edges) (u v : α) :
    retainEdge ops s (u, v) = some true ↔
      u ∈ vs ∧ v ∈ vs ∧ ¬ Connected vs edges u v := by
  unfold retainEdge
  rw [h.query_eq, observe_retain_iff]

end Connectivity
