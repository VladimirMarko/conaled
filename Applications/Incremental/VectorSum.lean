import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Applications.Incremental.Stateful
import Applications.Incremental.Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Fin
import Mathlib.Tactic.Abel

/-! Exact sums with ordered assignment patches. Indexed functions specify the
values; they do not assert constant-time lookup in Lean's runtime. -/
namespace Incremental.VectorSum
open scoped BigOperators
variable {G : Type} [AddCommGroup G] {n : Nat}

abbrev Values (G : Type) (n : Nat) := Fin n → G
abbrev Assignment (G : Type) (n : Nat) := Fin n × G
abbrev Patch (G : Type) (n : Nat) := List (Assignment G n)

def assign (v : Values G n) (a : Assignment G n) : Values G n := Function.update v a.1 a.2

def applyPatch (v : Values G n) (p : Patch G n) : Values G n := p.foldl assign v

def total (v : Values G n) : G := ∑ i, v i

@[reducible] def object (G : Type) (n : Nat) : ChangeObj := ⟨Values G n, Patch G n, applyPatch⟩

theorem total_assign (v : Values G n) (a : Assignment G n) :
    total (assign v a) = total v + (a.2 - v a.1) := by
  classical
  simp only [total, assign, Finset.sum_update_of_mem (Finset.mem_univ a.1)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a.1)]
  simp only [Finset.sdiff_singleton_eq_erase]
  abel

structure State (G : Type) (n : Nat) where
  values : Values G n
  sum : G

def Valid (v : Values G n) (s : State G n) : Prop := s.values = v ∧ s.sum = total v

def init (v : Values G n) : State G n := ⟨v, total v⟩

def step (s : State G n) (a : Assignment G n) : State G n :=
  ⟨assign s.values a, s.sum + (a.2 - s.values a.1)⟩

def patch (s : State G n) (p : Patch G n) : State G n := p.foldl step s

theorem step_valid (v : Values G n) (s : State G n) (a : Assignment G n)
    (h : Valid v s) : Valid (assign v a) (step s a) := by
  rcases h with ⟨hv, hs⟩
  exact ⟨congrArg (fun v => assign v a) hv, by simp only [step, hv, hs, total_assign]⟩

theorem patch_valid (v : Values G n) (s : State G n) (p : Patch G n)
    (h : Valid v s) : Valid (applyPatch v p) (patch s p) := by
  induction p generalizing v s with
  | nil => exact h
  | cons a p ih => exact ih _ _ (step_valid v s a h)

@[reducible] def realization (G : Type) [AddCommGroup G] (n : Nat) :
    Stateful.Ops (object G n) (additive G) where
  State := State G n
  init := init
  repair s p := let t := patch s p; (t, t.sum - s.sum)
  observe := State.sum

theorem realization_laws :
    Stateful.Laws (@total G _ n) (realization G n) Valid where
  init _ := ⟨rfl, rfl⟩
  repair v s p h := patch_valid v s p h
  observe _ _ h := h.2
  boundary _ s p _ := by dsimp [realization, additive]; abel

/-- The stateless map specifies the same finite-update semantics. It is not
used by the retained implementation to compute its changes. -/
def sumMap (G : Type) [AddCommGroup G] (n : Nat) : Map (object G n) (additive G) where
  run := total
  change v p := total (applyPatch v p) - total v
  correct _ _ := by dsimp [additive, object]; abel

theorem compatibility (v : Values G n) (s : State G n) (h : Valid v s) (p : Patch G n) :
    (realization G n).observe ((realization G n).repair s p).1 =
      ((Stateful.project realization_laws v s h : Cache (sumMap G n)).advance p).output :=
  Stateful.project_repair (f := sumMap G n) realization_laws v s h p

/-- A downstream component retaining its own output; repair uses the upstream
change and cached output, without recomputing the vector sum. -/
@[reducible] def doubleRealization (G : Type) [AddCommGroup G] : Stateful.Ops (additive G) (additive G) where
  State := G
  init x := x + x
  repair s d := (s + (d + d), d + d)
  observe := id

theorem double_laws : Stateful.Laws (fun x : G => x + x) (doubleRealization G)
    (fun x s => s = x + x) where
  init _ := rfl
  repair x s d h := by dsimp [doubleRealization, additive]; rw [h]; abel
  observe _ _ h := h
  boundary _ _ _ _ := rfl

@[reducible] def doubled (G : Type) [AddCommGroup G] (n : Nat) :=
  Stateful.comp (doubleRealization G) (realization G n)

theorem doubled_laws : Stateful.Laws (fun v : Values G n => total v + total v)
    (doubled G n) (Stateful.CompValid (realization G n) (doubleRealization G)
      Valid (fun x s => s = x + x)) := realization_laws.comp double_laws

theorem doubled_after_patch (v : Values G n) (p : Patch G n) :
    (doubled G n).observe ((doubled G n).repair ((doubled G n).init v) p).1 =
      total (applyPatch v p) + total (applyPatch v p) :=
  doubled_laws.observe _ _ (doubled_laws.repair _ _ _ (doubled_laws.init v))

end Incremental.VectorSum
