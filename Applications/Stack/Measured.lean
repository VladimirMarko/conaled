import Applications.Stack.Machine
import Applications.Resources.Measured
import Mathlib.Algebra.Group.Nat.Defs

/-! Unit-per-instruction accounting for the existing typed interpreter.
Primitive costs are an abstract tariff, not implementation time or bit cost. -/
namespace StackMachine
open FirstOrderCompiler
variable {Prim : Ty → Ty → Type} {B : Type}

def runInstrMeasured
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (i : Instr Prim a s b t) (x : Val B a × Stack B s) :
    Resources.Measured (Val B b × Stack B t) Nat := (runInstr meaning i x, 1)

def runMeasured
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) :
    Program Prim a s b t → Val B a × Stack B s →
      Resources.Measured (Val B b × Stack B t) Nat
  | .nil, x => Resources.pure x
  | .cons i p, x => Resources.bind (runInstrMeasured meaning i x) (runMeasured meaning p)

@[simp] theorem runMeasured_value
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (p : Program Prim a s b t) (x) : (runMeasured meaning p x).1 = run meaning p x := by
  induction p with
  | nil => rfl
  | cons i p ih => exact ih (runInstr meaning i x)

theorem runMeasured_append
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (p : Program Prim a s b t) (q : Program Prim b t c u) (x) :
    runMeasured meaning (p.append q) x =
      Resources.bind (runMeasured meaning p x) (runMeasured meaning q) := by
  induction p with
  | nil => exact (Resources.pure_bind (C := Nat) x (runMeasured meaning q)).symm
  | cons i p ih =>
    simp only [Program.append, runMeasured, Resources.bind, runInstrMeasured] at *
    rw [ih q (runInstr meaning i x)]
    simp [Nat.add_assoc]

/-- Static count is a consequence of the instrumented execution. -/
def Program.instructions : Program Prim a s b t → Nat
  | .nil => 0
  | .cons _ p => 1 + p.instructions

theorem runMeasured_cost
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (p : Program Prim a s b t) (x) : (runMeasured meaning p x).2 = p.instructions := by
  induction p with
  | nil => rfl
  | cons i p ih => exact congrArg (1 + ·) (ih (runInstr meaning i x))

def padding : Program Prim a s a s :=
  .cons .dup (.cons .swap (.cons .swap (.cons .fst .nil)))

theorem runMeasured_padding
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (x : Val B a × Stack B s) : runMeasured meaning padding x = (x, 4) := rfl

theorem append_padding
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (p : Program Prim a s b t) (x) :
    runMeasured meaning (p.append padding) x =
      ((runMeasured meaning p x).1, (runMeasured meaning p x).2 + 4) := by
  rw [runMeasured_append]
  simp only [Resources.bind, runMeasured_padding]

theorem padding_changes_cost
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (p : Program Prim a s b t) (x) :
    (runMeasured meaning (p.append padding) x).1 = (runMeasured meaning p x).1 ∧
    (runMeasured meaning (p.append padding) x).2 ≠ (runMeasured meaning p x).2 := by
  rw [append_padding]
  exact ⟨rfl, by omega⟩

namespace Certified
variable {meaning : {a b : Ty} → Prim a b → Val B a → Val B b}

theorem measured_correct (f : Certified Prim meaning a b) (s) (x) (z : Stack B s) :
    (runMeasured meaning (f.code s) (x,z)).1 = (f.spec x,z) := by
  rw [runMeasured_value, f.correct]

/-- Optional predicate on an unchanged Certified arrow, not a new target. -/
def Budget (f : Certified Prim meaning a b) (n : Nat) : Prop :=
  ∀ s x (z : Stack B s), (runMeasured meaning (f.code s) (x,z)).2 ≤ n

theorem Budget.comp {f : Certified Prim meaning a b} {g : Certified Prim meaning b c}
    (hf : f.Budget m) (hg : g.Budget n) : (g.comp f).Budget (m+n) := by
  intro s x z
  change (runMeasured meaning ((f.code s).append (g.code s)) (x,z)).2 ≤ m+n
  rw [runMeasured_append]
  simp only [Resources.bind, f.measured_correct]
  exact Nat.add_le_add (hf s x z) (hg s (f.spec x) z)

theorem Budget.primitive (p : Prim a b) :
    (Certified.primitive (meaning := meaning) p).Budget 1 := by
  intro s x z
  exact Nat.le_refl 1

end Certified
end StackMachine
