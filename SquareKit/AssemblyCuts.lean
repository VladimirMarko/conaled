import SquareKit.AssemblyLiftMonad

/-! Finite and full cut assemblies, using every index with the stated domain. -/

universe u
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

/-- A program observes a cut through termination only; returned values are unrestricted. -/
def Cut (e n : Nat) : Prop := ∀ k, ((ofNat Code e).eval k).Dom ↔ k < n

def FullCut (e : Nat) : Prop := ∀ k, ((ofNat Code e).eval k).Dom

private theorem cut_template_recursive :
    Nat.Partrec (fun z => Part.ofOption (if z.unpair.2 < z.unpair.1 then some 0 else none)) := by
  apply Partrec.nat_iff.mp
  exact Computable.ofOption
    ((Primrec.ite (Primrec.nat_lt.comp (Primrec.snd.comp Primrec.unpair) (Primrec.fst.comp Primrec.unpair))
      (Primrec.const (some 0)) (Primrec.const none)).to_comp)

private noncomputable def cutTemplate : Code := Code.exists_code.mp cut_template_recursive |>.choose

private theorem cutTemplate_eval (z : Nat) :
    cutTemplate.eval z = Part.ofOption (if z.unpair.2 < z.unpair.1 then some 0 else none) :=
  congrFun (Code.exists_code.mp cut_template_recursive).choose_spec z

/-- The template is fixed once; compilation of the length is computable. -/
noncomputable def cutCode (n : Nat) : Code := cutTemplate.curry n

theorem cutCode_computable : Computable cutCode :=
  (Code.primrec₂_curry.comp (Primrec.const cutTemplate) Primrec.id).to_comp

@[simp] theorem cutCode_eval (n k : Nat) :
    (cutCode n).eval k = Part.ofOption (if k < n then some 0 else none) := by
  simp [cutCode, Code.eval_curry, cutTemplate_eval]

theorem cutCode_realizes (n : Nat) : Cut (encode (cutCode n)) n := by
  intro k
  simp only [Denumerable.ofNat_encode, cutCode_eval]
  split <;> simp_all

/-- Removing the first observation is a computable transformation of indices. -/
def shiftCode (e : Nat) : Code := Code.comp (ofNat Code e) Code.succ

theorem shiftCode_computable : Computable shiftCode :=
  (Code.primrec₂_comp.comp (Primrec.ofNat Code) (Primrec.const Code.succ)).to_comp

@[simp] theorem shiftCode_eval (e k : Nat) :
    (shiftCode e).eval k = (ofNat Code e).eval (k + 1) := by
  simp only [shiftCode, Code.eval]
  exact Part.bind_some _ _

theorem Cut.shift {e n : Nat} (h : Cut e (n + 1)) : Cut (encode (shiftCode e)) n := by
  intro k
  simpa using h (k + 1)

theorem FullCut.shift {e : Nat} (h : FullCut e) : FullCut (encode (shiftCode e)) := by
  intro k
  simpa using h (k + 1)

/-- Finite cuts carry no bound in their realizers. -/
noncomputable def iterationCuts : Assembly.{u} where
  Carrier := ULift.{u} Nat
  realizes e n := Cut e n.down
  inhabited n := ⟨encode (cutCode n.down), cutCode_realizes n.down⟩

/-- `none` denotes the infinite cut, whereas `some n` denotes a finite cut. -/
noncomputable def finalCuts : Assembly.{u} where
  Carrier := ULift.{u} (Option Nat)
  realizes e n := match n.down with
    | some n => Cut e n
    | none => FullCut e
  inhabited n := by
    rcases n with ⟨n⟩
    cases n with
    | some n => exact ⟨encode (cutCode n), cutCode_realizes n⟩
    | none => exact ⟨encode (Code.const 0), by intro k; simp [Code.eval_const]⟩

noncomputable def cutInclusion : Hom iterationCuts.{u} finalCuts.{u} where
  toFun n := ⟨some n.down⟩
  tracked := ⟨Part.some, Nat.Partrec.some, fun n e h => ⟨e, by simp, h⟩⟩

/-- Infinity has a total constant program as its realizer. -/
noncomputable def cutInfinity (A : Assembly.{u}) : Hom A finalCuts.{u} where
  toFun _ := ⟨none⟩
  tracked := by
    refine ⟨fun _ => Part.some (encode (Code.const 0)), Nat.Partrec.of_primrec (Nat.Primrec.const _), ?_⟩
    intro x e h
    exact ⟨encode (Code.const 0), by simp, by intro k; simp [Code.eval_const]⟩

/-- The empty cut is a tracked constant in every context. -/
noncomputable def cutZero (A : Assembly.{u}) : Hom A iterationCuts.{u} where
  toFun _ := ⟨0⟩
  tracked := by
    refine ⟨fun _ => Part.some (encode (cutCode 0)),
      Nat.Partrec.of_primrec (Nat.Primrec.const _), ?_⟩
    intro x e h
    exact ⟨encode (cutCode 0), by simp, cutCode_realizes 0⟩

end Realizability.Assembly
