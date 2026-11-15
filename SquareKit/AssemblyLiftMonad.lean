import SquareKit.AssemblyLiftClassifier
import Mathlib.CategoryTheory.Monad.Basic

/-! The tracked program-index lifting monad (#386). -/

universe u
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

/-- Emit a program that runs the outer program and then its returned inner
program. Generating this code does not decide either termination problem. -/
def programLiftMul (A : Assembly.{u}) : Hom (programLift (programLift A)) (programLift A) where
  toFun := Option.join
  tracked := by
    obtain ⟨c, hc⟩ := Code.exists_code.mp run_partrec
    let t := fun n => encode (Code.comp c (ofNat Code n))
    have ht : Computable t := (Primrec.encode.comp (Code.primrec₂_comp.comp
      (Primrec.const c) (Primrec.ofNat Code))).to_comp
    refine ⟨fun n => Part.some (t n), Partrec.nat_iff.mp ht, ?_⟩
    intro x n hn
    refine ⟨t n, by simp, ?_⟩
    have he : run (t n) = (run n).bind run := by
      simp only [t, run_encode, Code.eval, hc]
      rfl
    cases x with
    | none =>
      change ¬ (run (t n)).Dom
      rw [he]
      exact fun hd => hn hd.1
    | some x =>
      obtain ⟨m, hm, hx⟩ := hn
      cases x with
      | none =>
        change ¬ (run (t n)).Dom
        rw [he]
        intro hd
        obtain ⟨r, hr⟩ := Part.dom_iff_mem.mp hd
        obtain ⟨k, hk, hk'⟩ := Part.mem_bind_iff.mp hr
        have hkm : k = m := Part.mem_unique hk hm
        exact hx (hkm ▸ Part.dom_iff_mem.mpr ⟨r, hk'⟩)
      | some x =>
        obtain ⟨r, hr, hy⟩ := hx
        exact ⟨r, he ▸ Part.mem_bind_iff.mpr ⟨m, hm, hr⟩, hy⟩

theorem programLiftMul_left_unit (A : Assembly.{u}) :
    (programLiftUnit (programLift A)).comp (programLiftMul A) = Hom.id (programLift A) :=
  Hom.ext fun _ => rfl

theorem programLiftMul_right_unit (A : Assembly.{u}) :
    (programLiftMap (programLiftUnit A)).comp (programLiftMul A) = Hom.id (programLift A) := by
  apply Hom.ext
  intro x
  cases x <;> rfl

theorem programLiftMul_assoc (A : Assembly.{u}) :
    (programLiftMap (programLiftMul A)).comp (programLiftMul A) =
      (programLiftMul (programLift A)).comp (programLiftMul A) := by
  apply Hom.ext
  intro x
  cases x with
  | none => rfl
  | some x => cases x <;> rfl

theorem programLiftMul_natural {A B : Assembly.{u}} (f : Hom A B) :
    (programLiftMap (programLiftMap f)).comp (programLiftMul B) =
      (programLiftMul A).comp (programLiftMap f) := by
  apply Hom.ext
  intro x
  cases x with
  | none => rfl
  | some x => cases x <;> rfl

open CategoryTheory

def programLiftFunctor : Assembly.{u} ⥤ Assembly.{u} where
  obj := programLift
  map := programLiftMap
  map_id := programLiftMap_id
  map_comp := programLiftMap_comp

def programLiftMonad : Monad Assembly.{u} where
  toFunctor := programLiftFunctor
  η := ⟨programLiftUnit, fun _ _ f => (programLiftUnit_natural f).symm⟩
  μ := ⟨programLiftMul, fun _ _ f => programLiftMul_natural f⟩
  assoc := programLiftMul_assoc
  left_unit := programLiftMul_left_unit
  right_unit := programLiftMul_right_unit

end Realizability.Assembly
