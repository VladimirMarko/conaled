import SquareKit.Internal.ArrowPresheafPushout
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! A local proposition changes from false to true along a restriction.
The induced restriction computes the input arrow, rather than retaining the
old domain witness or replacing it by a proof of mere inhabitation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Examples.SierpinskiLocal
open CategoryTheory CategoryTheory.Limits SquareKit.Internal
open WalkingParallelPair

def P : WalkingParallelPair ⥤ Type :=
  parallelPair (TypeCat.ofHom (PEmpty.elim : PEmpty → PUnit)) (TypeCat.ofHom PEmpty.elim)

instance (X : WalkingParallelPair) : Subsingleton (P.obj X) := by
  cases X <;> dsimp [P, parallelPair] <;> infer_instance

def increment : Arrow (WalkingParallelPair ⥤ Type) := Arrow.mk
  (show (Functor.const WalkingParallelPair).obj Nat ⟶ (Functor.const WalkingParallelPair).obj Nat from
    { app _ := TypeCat.ofHom (fun (n : Nat) => n + 1) })

theorem at_zero : ¬ ArrowPresheafPushout.inhabited P zero := fun ⟨x⟩ => PEmpty.elim x

theorem at_one : ArrowPresheafPushout.inhabited P one := ⟨PUnit.unit⟩

/-- Crossing the local boundary sends the domain witness 3 to codomain witness 4. -/
example : ((ArrowPresheafPushout.interpretation P).obj increment).map
    WalkingParallelPairHom.left (.inr ⟨(3 : Nat), at_zero⟩) = .inl ⟨(4 : Nat), at_one⟩ := by
  simp [ArrowPresheafPushout.interpretation, ArrowPresheaf.interpretation,
    ArrowPresheaf.object, ArrowPresheaf.restrict, at_one, increment]

/-- The false stage keeps the domain value through the canonical pushout comparison. -/
example : (ArrowPresheafPushout.inl P increment).app zero (3 : Nat) = .inr ⟨(3 : Nat), at_zero⟩ := by
  simp [ArrowPresheafPushout.inl, at_zero]

/-- The true stage computes the original function, retaining its output value. -/
example : (ArrowPresheafPushout.inl P increment).app one (3 : Nat) = .inl ⟨(4 : Nat), at_one⟩ := by
  simp [ArrowPresheafPushout.inl, at_one, increment]

/-- These local computations concern the actual categorical pushout. -/
example : pushout.inl (CategoryTheory.CartesianMonoidalCategory.snd P increment.left)
      (CategoryTheory.MonoidalCategory.whiskerLeft P increment.hom) ≫
    (ArrowPresheafPushout.comparison P increment).hom = ArrowPresheafPushout.inl P increment :=
  ArrowPresheafPushout.comparison_inl P increment

end Examples.SierpinskiLocal
