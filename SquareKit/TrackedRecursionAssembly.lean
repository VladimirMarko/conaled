import SquareKit.TrackedRecursion
import SquareKit.AssemblyPartialMap

/-! Uniform families are precisely tracked maps into the computation assembly.
Evaluation produces program realizers in the existing assembly lifting. -/
set_option backward.isDefEq.respectTransparency false

namespace Realizability.TrackedRecursion
open Encodable Denumerable
open Nat.Partrec (Code)
open Assembly

/-- A realizer is a code for the entire partial computation. -/
def computationAssembly : Assembly where
  Carrier := Computation
  realizes n p := (ofNat Code n).eval = p.val
  inhabited p := by
    obtain ⟨c, hc⟩ := represented_surjective p
    exact ⟨encode c, by simpa [represented] using congrArg Subtype.val hc⟩

theorem uniform_tracked {a : Nat → Computation} (ha : Uniform a) :
    ∃ h : Hom (encoded Nat) computationAssembly, h.toFun = a := by
  obtain ⟨k, hk⟩ := uniform_coverage ha
  refine ⟨⟨a, ?_⟩, rfl⟩
  refine ⟨fun n => Part.some (encode ((ofNat Code k).curry n)), ?_, ?_⟩
  · exact Partrec.nat_iff.mp ((Computable.encode.comp
      (Code.primrec₂_curry.comp (Primrec.const (ofNat Code k)) Primrec.id).to_comp))
  · intro x n hn
    change n = x at hn
    subst n
    refine ⟨encode ((ofNat Code k).curry x), by simp, ?_⟩
    simpa [computationAssembly, row, represented] using
      congrArg Subtype.val (congrFun hk x)

theorem tracked_uniform (h : Hom (encoded Nat) computationAssembly) : Uniform h.toFun := by
  obtain ⟨c, hc⟩ := h.has_code
  have hp : Partrec (fun z : Nat => (c.eval z.unpair.1).bind
      (fun e => (ofNat Code e).eval z.unpair.2)) := by
    apply Partrec.bind (Code.eval_part.comp (Computable.const c)
      (Computable.fst.comp Primrec.unpair.to_comp))
    exact (Code.eval_part.comp ((Computable.ofNat Code).comp Computable.snd)
      (Computable.snd.comp (Primrec.unpair.to_comp.comp Computable.fst))).to₂
  apply (Partrec.nat_iff.mp hp).of_eq
  intro z
  obtain ⟨e, he, hr⟩ := hc z.unpair.1 z.unpair.1 rfl
  rw [Part.bind_of_mem he]
  exact congrFun hr z.unpair.2

theorem uniform_iff_tracked (a : Nat → Computation) :
    Uniform a ↔ ∃ h : Hom (encoded Nat) computationAssembly, h.toFun = a := by
  constructor
  · exact uniform_tracked
  · rintro ⟨h, rfl⟩
    exact tracked_uniform h

/-- Semantic observation only: deciding termination is not an executable operation. -/
noncomputable def observation (p : Computation) (n : Nat) : Option Nat := by
  classical
  exact (p.val n).toOption

/-- Evaluation returns a program for a lifted natural, not a decision of its domain. -/
noncomputable def computationEvaluation :
    Hom (prod computationAssembly (encoded Nat)) (programLift (encoded Nat)) where
  toFun x := observation x.1 x.2
  tracked := by
    let generate := fun z : Nat => encode (Code.comp (ofNat Code z.unpair.1)
      (Code.const z.unpair.2))
    have hg : Computable generate :=
      Computable.encode.comp (Code.primrec₂_comp.to_comp.comp
        ((Computable.ofNat Code).comp (Computable.fst.comp Primrec.unpair.to_comp))
        (Code.primrec_const.to_comp.comp (Computable.snd.comp Primrec.unpair.to_comp)))
    refine ⟨fun z => Part.some (generate z), Partrec.nat_iff.mp hg, ?_⟩
    rintro ⟨p, n⟩ z ⟨hp, hn⟩
    change z.unpair.2 = n at hn
    have he : run (generate z) = p.val n := by
      simp only [generate, run_encode]
      change ((Code.const z.unpair.2).eval 0).bind (ofNat Code z.unpair.1).eval = _
      rw [Code.eval_const, Part.bind_some, hn]
      exact congrFun hp n
    refine ⟨generate z, by simp, ?_⟩
    classical
    simp only [programLift, encoded, he]
    cases ho : observation p n with
    | none => exact (Part.toOption_eq_none _).mp ho
    | some x => exact ⟨x, Part.toOption_eq_some_iff.mp ho, rfl⟩

/-- Existing exponential evaluation recovers the same tracked observation. -/
noncomputable def computationFunction :
    Hom computationAssembly (function (encoded Nat) (programLift (encoded Nat))) :=
  Assembly.curry computationEvaluation

theorem computationFunction_apply (p : Computation) (n : Nat) :
    ((computationFunction.toFun p).toFun n) = observation p n :=
  Assembly.curry_apply computationEvaluation p n

/-- Evaluation has saturated recursively enumerable support on every realizer. -/
theorem evaluation_admissible : Admissible
    (prod computationAssembly (encoded Nat)) (fun x => (x.1.val x.2).Dom) := by
  refine ⟨fun z => (ofNat Code z.unpair.1).eval z.unpair.2, ?_, ?_⟩
  · exact Partrec.nat_iff.mp (Code.eval_part.comp
      ((Computable.ofNat Code).comp (Computable.fst.comp Primrec.unpair.to_comp))
      (Computable.snd.comp Primrec.unpair.to_comp))
  · rintro ⟨p, n⟩ z ⟨hp, hn⟩
    change z.unpair.2 = n at hn
    change (ofNat Code z.unpair.1).eval = p.val at hp
    change ((ofNat Code z.unpair.1).eval z.unpair.2).Dom ↔ (p.val n).Dom
    have he : (ofNat Code z.unpair.1).eval z.unpair.2 = p.val n :=
      (congrFun hp _).trans (congrArg p.val hn)
    rw [he]

/-- The partial map retains its domain witness rather than deciding termination. -/
def computationPartialMap : PartialMap
    (prod computationAssembly (encoded Nat)) (encoded Nat) where
  domain x := (x.1.val x.2).Dom
  admissible := evaluation_admissible
  map := ⟨fun x => (x.val.1.val x.val.2).get x.property, by
    refine ⟨fun z => (ofNat Code z.unpair.1).eval z.unpair.2, ?_, ?_⟩
    · exact Partrec.nat_iff.mp (Code.eval_part.comp
        ((Computable.ofNat Code).comp (Computable.fst.comp Primrec.unpair.to_comp))
        (Computable.snd.comp Primrec.unpair.to_comp))
    · rintro ⟨⟨p, n⟩, hd⟩ z ⟨hp, hn⟩
      change z.unpair.2 = n at hn
      change (ofNat Code z.unpair.1).eval = p.val at hp
      refine ⟨(p.val n).get hd, ?_, rfl⟩
      change (p.val n).get hd ∈ (ofNat Code z.unpair.1).eval z.unpair.2
      have he : (ofNat Code z.unpair.1).eval z.unpair.2 = p.val n :=
        (congrFun hp _).trans (congrArg p.val hn)
      rw [he]
      exact Part.get_mem hd⟩

theorem computationEvaluation_classifies :
    computationEvaluation = computationPartialMap.classify := by
  apply PartialMap.classify_unique
  rintro ⟨p, n⟩ y
  classical
  change (p.val n).toOption = some y ↔ ∃ h : (p.val n).Dom, (p.val n).get h = y
  rw [Part.toOption_eq_some_iff]
  rfl

end Realizability.TrackedRecursion
