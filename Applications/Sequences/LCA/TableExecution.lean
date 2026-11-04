import Applications.Dijkstra.Store
import Applications.Resources.Measured
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

/-! Bounded initStored table construction from indexed primitive operations.
The vectors describe mutable target slots mathematically; native Lean allocation
and array-copy behavior are not the target execution model. -/
namespace Sequences.LCA.TableExecution
open Resources Dijkstra.Store
variable {α : Type}

def read {n : Nat} (mem : Store n α) (i : Fin n) : Measured α Nat := (lookup mem i, 1)
def store {n : Nat} (mem : Store n α) (i : Fin n) (x : α) : Measured (Store n α) Nat :=
  (write mem i x, 1)

def initStore (seed : α) : (n : Nat) → Measured (Store n α) Nat
  | 0 => pure #v[]
  | n+1 => bind (initStore seed n) fun cells => (cells.push seed, 3)

theorem initStore_exact (seed : α) (n : Nat) :
    initStore seed n = (Vector.replicate n seed, 3*n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [initStore, ih, Resources.bind, Vector.replicate_succ]; omega

/-- A bounded loop counter visit performs its comparison and increment. The
list passed to `fill` denotes the control schedule, not a target heap list. -/
def visitIndex {n : Nat} (i : Fin n) : Measured (Fin n) Nat := (i, 2)

def fill {n : Nat} (f : Fin n → Measured α Nat) : List (Fin n) → Store n α → Measured (Store n α) Nat
  | [], mem => pure mem
  | i :: rest, mem => bind (visitIndex i) fun j =>
      bind (f j) fun a => bind (store mem j a) fun mem' => fill f rest mem'

theorem fill_value {n : Nat} (f : Fin n → Measured α Nat) (indices : List (Fin n))
    (mem : Store n α) :
    (fill f indices mem).1 = accum (fun _ x => x) mem (indices.map (fun i => (i, (f i).1))) := by
  induction indices generalizing mem with
  | nil => rfl
  | cons i rest ih => simpa [fill, visitIndex, Resources.bind, store, accum, accumStep] using ih (write mem i (f i).1)

theorem fill_cost {n : Nat} (f : Fin n → Measured α Nat) (indices : List (Fin n))
    (mem : Store n α) (c : Nat) (hc : ∀ i, (f i).2 ≤ c) :
    (fill f indices mem).2 ≤ indices.length * (c+3) := by
  induction indices generalizing mem with
  | nil => simp [fill, Resources.pure]
  | cons i rest ih =>
    simp only [fill, visitIndex, Resources.bind, store, List.length_cons]
    have hh := ih (write mem i (f i).1)
    have hi := hc i
    nlinarith

def tabulate {n : Nat} (seed : α) (f : Fin n → Measured α Nat) : Measured (Store n α) Nat :=
  bind (initStore seed n) fun mem => fill f (List.finRange n) mem

theorem tabulate_lookup {n : Nat} (seed : α) (f : Fin n → Measured α Nat) (i : Fin n) :
    lookup (tabulate seed f).1 i = (f i).1 := by
  simp only [tabulate, Resources.bind, fill_value]
  rw [accum_lookup, valuesAt_map_unique _ _ (List.nodup_finRange n)]
  simp

theorem tabulate_value {n : Nat} (seed : α) (f : Fin n → Measured α Nat) :
    (tabulate seed f).1 = Vector.ofFn (fun i => (f i).1) := by
  apply Vector.ext
  intro i hi
  have hh := tabulate_lookup seed f ⟨i, hi⟩
  simpa [lookup] using hh

theorem tabulate_cost {n : Nat} (seed : α) (f : Fin n → Measured α Nat)
    (c : Nat) (hc : ∀ i, (f i).2 ≤ c) :
    (tabulate seed f).2 ≤ n * (c+6) := by
  simp only [tabulate, Resources.bind, initStore_exact]
  have hh := fill_cost f (List.finRange n) (Vector.replicate n seed) c hc
  simp only [List.length_finRange] at hh
  nlinarith

end Sequences.LCA.TableExecution
