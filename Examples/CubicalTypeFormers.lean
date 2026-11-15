import SquareKit.Internal.Cubical.Naturals
import SquareKit.Internal.Cubical.Substitution
import Examples.CubicalPresheaf

/-! Dependent function, pair and recursion cases with varying finite fibers. -/
namespace Examples.CubicalTypeFormers
open CategoryTheory SquareKit.Cubical.Presheaf

abbrev base : Context := terminal
abbrev numbers : Family base := natFamily base

abbrev finiteMotive : Family (total numbers) where
  obj e := Fin (Nat.succ e.val.2.down)
  map {_x y} f := TypeCat.ofHom (Fin.cast (congrArg
    (fun z : (total numbers).obj y.obj => Nat.succ z.2.down) f.map_val))
  map_id _ := rfl
  map_comp _ _ := rfl

def last : Term finiteMotive where
  val e := Fin.last e.val.2.down
  property f := Fin.ext (congrArg (fun z => z.2.down) f.map_val)

/-- Abstraction retains the argument-dependent Fin(n+1) result type. -/
def dependentLast : Term (pi numbers finiteMotive) := lam last

theorem dependentLast_beta : app dependentLast = last := app_lam last

theorem dependentLast_eta : lam (app dependentLast) = dependentLast := lam_app dependentLast

theorem dependentLast_at_three :
    (app dependentLast).val ((total numbers).elementsMk (Opposite.op ⟨0⟩)
      ⟨PUnit.unit, ⟨3⟩⟩) = (3 : Fin 4) := by
  rw [dependentLast_beta]
  rfl

def zeroCase : Term (reindex finiteMotive (pair (𝟙 base) (natZero base))) where
  val _ := (0 : Fin 1)
  property _ := rfl

def stepCase : NatStep finiteMotive where
  val _ _ b := b.succ
  naturality _ _ _ := rfl

/-- The dependent recursor inhabits Fin(n+1), without replacing it by Nat. -/
def countedLast : Term finiteMotive := natElim zeroCase stepCase

theorem countedLast_zero :
    Term.reindex countedLast (pair (𝟙 base) (natZero base)) = zeroCase :=
  natElim_zero zeroCase stepCase

theorem countedLast_succ (x : base.Elements) (n : ℕ) :
    countedLast.val (extendObj numbers x ⟨n+1⟩) =
      (countedLast.val (extendObj numbers x ⟨n⟩)).succ :=
  natElim_succ zeroCase stepCase x n

theorem countedLast_is_last : countedLast = last := by
  apply Term.ext
  intro e
  rcases e with @⟨I, x, ⟨n⟩⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show countedLast.val ((total numbers).elementsMk I ⟨x, ⟨n+1⟩⟩) =
      (countedLast.val ((total numbers).elementsMk I ⟨x, ⟨n⟩⟩)).succ from
        countedLast_succ (base.elementsMk I x) n]
    rw [ih]
    rfl

theorem pair_second_recovers_dependent_zero :
    sigmaSnd (sigmaIntro (natZero base) zeroCase) = zeroCase :=
  sigmaSnd_intro (natZero base) zeroCase

/-- Neither direction of substitution comparison loses the dependent function. -/
theorem dependentLast_substitution_roundtrip (Δ : Context) (σ : Δ ⟶ base) :
    Term.map (piReindexIso numbers finiteMotive σ).inv
      (Term.map (piReindexIso numbers finiteMotive σ).hom
        (Term.reindex dependentLast σ)) = Term.reindex dependentLast σ :=
  Term.map_iso_roundtrip (piReindexIso numbers finiteMotive σ) (Term.reindex dependentLast σ)

end Examples.CubicalTypeFormers
