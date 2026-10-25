import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! Countable powers as final stream coalgebras. A coalgebra comparison must be
invertible to transport this finality; finite-product preservation alone does not suffice. -/
noncomputable section
namespace SquareKit.ProductStreams
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor
universe u v
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev step (A : C) : C ⥤ C := prod.functor.obj A

variable (A : C) [HasProduct (fun _ : Nat => A)]
abbrev streams := ∏ᶜ (fun _ : Nat => A)
def head : streams A ⟶ A := Pi.π _ 0
def tail : streams A ⟶ streams A := Pi.lift fun n => Pi.π _ (n + 1)

def coalgebra : Coalgebra (step A) := ⟨streams A, prod.lift (head A) (tail A)⟩

def observation (S : Coalgebra (step A)) : Nat → (S.V ⟶ A)
  | 0 => S.str ≫ prod.fst
  | n + 1 => S.str ≫ prod.snd ≫ observation S n

def unfold (S : Coalgebra (step A)) : S ⟶ coalgebra A where
  f := Pi.lift (observation A S)
  h := by
    apply prod.hom_ext
    · simp [step, prod.functor, coalgebra, head, observation]
    · simp only [step, prod.functor, prod.map_snd, Category.assoc, coalgebra, prod.lift_snd]
      apply Pi.hom_ext
      intro n
      simp [tail, Category.assoc, observation]

theorem morphism_observation (S : Coalgebra (step A)) (f : S ⟶ coalgebra A) (n : Nat) :
    f.f ≫ Pi.π (fun _ : Nat => A) n = observation A S n := by
  have hh := congrArg (fun k => k ≫ prod.fst) f.h
  have ht := congrArg (fun k => k ≫ prod.snd) f.h
  simp only [step, prod.functor, Category.assoc, prod.map_fst, Category.comp_id, coalgebra, prod.lift_fst] at hh
  simp only [step, prod.functor, Category.assoc, prod.map_snd, coalgebra, prod.lift_snd] at ht
  induction n with
  | zero => exact hh.symm
  | succ n ih =>
    have ht' := congrArg (fun k => k ≫ Pi.π (fun _ : Nat => A) n) ht
    simpa only [tail, Category.assoc, Pi.lift_comp_π, ih, observation] using ht'.symm

def final : IsTerminal (coalgebra A) := IsTerminal.ofUniqueHom (unfold A) (by
  intro S f
  apply Coalgebra.Hom.ext
  apply Pi.hom_ext
  intro n
  rw [morphism_observation]
  exact (Pi.lift_comp_π (observation A S) n).symm)

/-- An invertible structure-preserving comparison suffices, without claiming
that an arbitrary functor preserves final coalgebras. -/
def final_of_comparison {S : Coalgebra (step A)} (f : S ⟶ coalgebra A) [IsIso f.f] :
    IsTerminal S :=
  (final A).ofIso (Coalgebra.isoMk (asIso f.f) f.h).symm

/-- Conversely any comparison from a final coalgebra to this final one is invertible. -/
theorem comparison_iso_of_final {S : Coalgebra (step A)} (f : S ⟶ coalgebra A)
    (hS : IsTerminal S) : IsIso f.f := by
  have hf : f = (hS.uniqueUpToIso (final A)).hom := (final A).hom_ext _ _
  rw [hf]
  change IsIso ((Coalgebra.forget (step A)).map (hS.uniqueUpToIso (final A)).hom)
  infer_instance

section Types
variable (B : Type)

def functionCoalgebra : Coalgebra (step B) where
  V := Nat → B
  str := prod.lift (↾fun s => s 0) (↾fun s n => s (n + 1))

def functionComparison : functionCoalgebra B ⟶ coalgebra B where
  f := (Types.productIso (fun _ : Nat => B)).inv
  h := by
    apply prod.hom_ext
    · simp only [step, prod.functor, Category.assoc, prod.map_fst, Category.comp_id, coalgebra,
        prod.lift_fst, head, Types.productIso_inv_comp_π, functionCoalgebra]
    · simp only [step, prod.functor, Category.assoc, prod.map_snd, coalgebra, prod.lift_snd,
        functionCoalgebra, prod.lift_snd_assoc]
      apply Pi.hom_ext
      intro n
      simp only [Category.assoc, Types.productIso_inv_comp_π, tail, Pi.lift_comp_π]
      rfl

def functionFinal : IsTerminal (functionCoalgebra B) := by
  letI : IsIso (functionComparison B).f :=
    inferInstanceAs (IsIso (Types.productIso (fun _ : Nat => B)).inv)
  exact final_of_comparison B (functionComparison B)
end Types

/-- Preserving the one countable power, together with the checked coalgebra
comparison law, suffices for this route. No preservation of arbitrary limits
or arbitrary final coalgebras is asserted. -/
def final_of_preservesPower (F : Type ⥤ C) (B : Type)
    [HasProduct (fun _ : Nat => F.obj B)]
    [PreservesLimit (Discrete.functor (fun _ : Nat => B)) F]
    (str : F.obj (Nat → B) ⟶ (step (F.obj B)).obj (F.obj (Nat → B)))
    (law : str ≫ (step (F.obj B)).map
        (F.map (Types.productIso (fun _ : Nat => B)).inv ≫ piComparison F (fun _ : Nat => B)) =
      (F.map (Types.productIso (fun _ : Nat => B)).inv ≫ piComparison F (fun _ : Nat => B)) ≫
        (coalgebra (F.obj B)).str) :
    IsTerminal (show Coalgebra (step (F.obj B)) from ⟨F.obj (Nat → B), str⟩) :=
  final_of_comparison (F.obj B)
    ⟨F.map (Types.productIso (fun _ : Nat => B)).inv ≫ piComparison F (fun _ : Nat => B), law⟩

end SquareKit.ProductStreams
