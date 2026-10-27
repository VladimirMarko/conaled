import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic

/-!
# Conditional safety and observation contracts

Experimental contracts for #194. Relations and behavior sets are mathematical
specifications: no executable choice, finite state space or termination is
required. Boundary interference is explicit; the sequential rule does not
model interruption inside a component unless its relation includes it.
-/
namespace Interaction
universe u v w

/-- Partial correctness of every related endpoint; no result existence claim. -/
def Safe {S : Type u} (P : S → Prop) (C : S → S → Prop) (Q : S → Prop) : Prop :=
  ∀ ⦃s t⦄, P s → C s t → Q t

/-- An assertion survives one permitted environment step. -/
def Stable {S : Type u} (R : S → S → Prop) (Q : S → Prop) : Prop :=
  ∀ ⦃s t⦄, Q s → R s t → Q t

theorem Stable.closure {S : Type u} {R : S → S → Prop} {Q : S → Prop}
    (h : Stable R Q) : Stable (Relation.ReflTransGen R) Q := by
  intro s t hs hst
  induction hst with
  | refl => exact hs
  | tail _ step ih => exact h ih step

/-- Run C, permit finitely many R steps, then run D. Stability is the
obligation that ordinary endpoint composition would otherwise omit. -/
theorem safe_interference_seq {S : Type u} {P Q U : S → Prop}
    {C D R : S → S → Prop} (hc : Safe P C Q) (hr : Stable R Q)
    (hd : Safe Q D U) :
    Safe P (Relation.Comp C (Relation.Comp (Relation.ReflTransGen R) D)) U := by
  rintro s t hs ⟨a, hca, b, hab, hdb⟩
  exact hd (hr.closure (hc hs hca) hab) hdb

/-- Every target behavior has a related permitted source behavior.
The carriers may include finite, infinite or otherwise represented behaviors. -/
def Refines {S : Type u} {T : Type v} (obs : S → T → Prop)
    (source : Set S) (target : Set T) : Prop :=
  ∀ ⦃t⦄, t ∈ target → ∃ s ∈ source, obs s t

theorem Refines.trans {S : Type u} {T : Type v} {U : Type w}
    {a : Set S} {b : Set T} {c : Set U} {r : S → T → Prop} {q : T → U → Prop}
    (h : Refines r a b) (j : Refines q b c) : Refines (Relation.Comp r q) a c := by
  intro t ht
  obtain ⟨m, hm, hmt⟩ := j ht
  obtain ⟨s, hs, hsm⟩ := h hm
  exact ⟨s, hs, m, hsm, hmt⟩

/-- Target properties transfer only when the observation relation respects them. -/
theorem Refines.property {S : Type u} {T : Type v} {obs : S → T → Prop}
    {source : Set S} {target : Set T} (h : Refines obs source target)
    {P : S → Prop} {Q : T → Prop} (hp : ∀ s ∈ source, P s)
    (respects : ∀ s t, obs s t → P s → Q t) : ∀ t ∈ target, Q t := by
  intro t ht
  obtain ⟨s, hs, hst⟩ := h ht
  exact respects s t hst (hp s hs)

/-- An infinite sequence of permitted steps; no fairness condition is implicit. -/
def Run {S : Type u} (step : S → S → Prop) (states : Nat → S) : Prop :=
  ∀ n, step (states n) (states (n + 1))

theorem Run.invariant {S : Type u} {step : S → S → Prop} {states : Nat → S}
    (run : Run step states) {P : S → Prop} (initial : P (states 0))
    (stable : Stable step P) : ∀ n, P (states n) := by
  intro n
  induction n with
  | zero => exact initial
  | succ n ih => exact stable ih (run n)
end Interaction
