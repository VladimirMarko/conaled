import SquareKit.AssemblyLift

/-! Tracked comparison with the diagonal-input lifting presentation (#385). -/

universe u
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

def runDiagonal (n : Nat) : Part Nat := (ofNat Code n).eval n

/-- The source's diagonal-input presentation, specified independently of
zero-input lifting. -/
def diagonalLift (A : Assembly.{u}) : Assembly.{u} where
  Carrier := Option A.Carrier
  realizes n x := match x with
    | none => ¬ (runDiagonal n).Dom
    | some x => ∃ m, m ∈ runDiagonal n ∧ A.realizes m x
  inhabited x := by
    cases x with
    | none =>
      obtain ⟨c, hc⟩ := Code.exists_code.mp Nat.Partrec.none
      exact ⟨encode c, by simp [runDiagonal, hc]⟩
    | some x =>
      obtain ⟨n, hn⟩ := A.inhabited x
      exact ⟨encode (Code.const n), n, by simp [runDiagonal, Code.eval_const], hn⟩

/-- Fix the argument before changing the program's index. No fixed-point
construction or halting test is needed. -/
def zeroToDiagonal (A : Assembly.{u}) : Hom (programLift A) (diagonalLift A) where
  toFun := id
  tracked := by
    let t := fun n => encode (Code.comp (ofNat Code n) (Code.const 0))
    have ht : Computable t := (Primrec.encode.comp (Code.primrec₂_comp.comp
      (Primrec.ofNat Code) (Primrec.const (Code.const 0)))).to_comp
    refine ⟨fun n => Part.some (t n), Partrec.nat_iff.mp ht, ?_⟩
    intro x n hn
    refine ⟨t n, by simp, ?_⟩
    have he : runDiagonal (t n) = run n := by
      simp [t, runDiagonal, run, Code.eval, Code.eval_const]
      exact Part.bind_some _ _
    cases x with
    | none => simpa only [diagonalLift, programLift, id_eq, he] using hn
    | some x => simpa only [diagonalLift, programLift, id_eq, he] using hn

def diagonalToZero (A : Assembly.{u}) : Hom (diagonalLift A) (programLift A) where
  toFun := id
  tracked := by
    let t := fun n => encode (Code.comp (ofNat Code n) (Code.const n))
    have ht : Computable t := (Primrec.encode.comp (Code.primrec₂_comp.comp
      (Primrec.ofNat Code) Code.primrec_const)).to_comp
    refine ⟨fun n => Part.some (t n), Partrec.nat_iff.mp ht, ?_⟩
    intro x n hn
    refine ⟨t n, by simp, ?_⟩
    have he : run (t n) = runDiagonal n := by
      simp [t, runDiagonal, Code.eval, Code.eval_const]
      exact Part.bind_some _ _
    cases x with
    | none => simpa only [diagonalLift, programLift, id_eq, he] using hn
    | some x => simpa only [diagonalLift, programLift, id_eq, he] using hn

@[simp] theorem zero_diagonal_inverse (A : Assembly.{u}) :
    (zeroToDiagonal A).comp (diagonalToZero A) = Hom.id (programLift A) := Hom.ext fun _ => rfl

@[simp] theorem diagonal_zero_inverse (A : Assembly.{u}) :
    (diagonalToZero A).comp (zeroToDiagonal A) = Hom.id (diagonalLift A) := Hom.ext fun _ => rfl

/-- Transport of the lifted arrow through the proved presentation equivalence. -/
def diagonalLiftMap {A B : Assembly.{u}} (f : Hom A B) : Hom (diagonalLift A) (diagonalLift B) :=
  ((diagonalToZero A).comp (programLiftMap f)).comp (zeroToDiagonal B)

def diagonalLiftUnit (A : Assembly.{u}) : Hom A (diagonalLift A) :=
  (programLiftUnit A).comp (zeroToDiagonal A)

theorem zeroToDiagonal_natural {A B : Assembly.{u}} (f : Hom A B) :
    (programLiftMap f).comp (zeroToDiagonal B) = (zeroToDiagonal A).comp (diagonalLiftMap f) :=
  Hom.ext fun _ => rfl

theorem diagonalToZero_natural {A B : Assembly.{u}} (f : Hom A B) :
    (diagonalLiftMap f).comp (diagonalToZero B) = (diagonalToZero A).comp (programLiftMap f) :=
  Hom.ext fun _ => rfl

theorem diagonalToZero_unit (A : Assembly.{u}) :
    (diagonalLiftUnit A).comp (diagonalToZero A) = programLiftUnit A := Hom.ext fun _ => rfl

end Realizability.Assembly
