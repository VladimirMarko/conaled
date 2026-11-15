import SquareKit.AssemblyCountdownIteration
import SquareKit.AssemblyCutWait

/-! A tracked full-cut extension identifies the internally selected countdown. -/
namespace Realizability.Assembly

private def natAddition : Hom (prod (encoded Nat) (encoded Nat)) (encoded Nat) where
  toFun := fun (x : Nat × Nat) => x.1+x.2
  tracked := by
    have hc := (Primrec.nat_add.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)).to_comp
    refine ⟨_, Partrec.nat_iff.mp hc, ?_⟩
    rintro ⟨a,b⟩ z ⟨ha,hb⟩
    refine ⟨z.unpair.1+z.unpair.2, by simp, ?_⟩
    change Nat at a b
    change z.unpair.1 = a at ha
    change z.unpair.2 = b at hb
    change z.unpair.1+z.unpair.2 = a+b
    rw [ha,hb]

private def liftBottom (Γ : Assembly) : Hom Γ (programLift (encoded Nat)) where
  toFun _ := none
  tracked := by
    obtain ⟨e,he⟩ := (programLift (encoded Nat)).inhabited none
    refine ⟨fun _ => Part.some e, Nat.Partrec.of_primrec (Nat.Primrec.const e), ?_⟩
    intro γ r hr
    exact ⟨e, by simp, he⟩

noncomputable def countdownExtension {Γ : Assembly} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) : Hom (prod Γ finalCuts) partialSequences := by
  let E := prod (prod Γ finalCuts) (encoded Nat)
  let ctx : Hom E Γ := (fst _ _).comp (fst _ _)
  let cut : Hom E finalCuts := (fst _ _).comp (snd _ _)
  let wait := (pair cut (snd _ _)).comp cutWait
  let value := ((pair (ctx.comp seed) wait).comp (liftStrength _ _)).comp
    (programLiftMap natAddition)
  exact curry ((pair (ctx.comp enabled) (pair value (liftBottom E))).comp (booleanChoice _))

def countdownLimit (enabled : Bool) (seed : Nat) (t : Option Nat) (k : Nat) : Option Nat :=
  if enabled then (cutWaitValue t k).map (fun v => seed+v) else none

theorem countdownExtension_apply {Γ : Assembly} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (γ : Γ.Carrier) (t : Option Nat) (k : Nat) :
    ((countdownExtension enabled seed).toFun (γ,⟨t⟩)).toFun k =
      countdownLimit (enabled.toFun γ) (seed.toFun γ) t k := by
  unfold countdownExtension
  change cond (enabled.toFun γ)
    (((cutWaitValue t k).map (fun v : Nat => (seed.toFun γ,v))).map
      (fun p : Nat × Nat => p.1+p.2)) none = _
  unfold countdownLimit
  cases enabled.toFun γ <;> cases cutWaitValue t k <;> rfl

theorem countdownExtension_finite {Γ : Assembly} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (γ : Γ.Carrier) (fuel k : Nat) :
    ((countdownExtension enabled seed).toFun (γ,⟨some fuel⟩)).toFun k =
      countdownFinite (enabled.toFun γ) (seed.toFun γ) fuel k := by
  rw [countdownExtension_apply]
  cases enabled.toFun γ <;> by_cases h : k < fuel <;>
    simp [countdownLimit, countdownFinite, cutWaitValue, h] <;> rfl

theorem countdownExtension_is_extension {Γ : Assembly} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) :
    cutExtend partialSequences_complete (strictIteration sequenceAlgebra (countdown enabled seed)) =
      countdownExtension enabled seed := by
  symm
  apply cutExtend_unique
  apply Hom.ext
  rintro ⟨γ,⟨fuel⟩⟩
  apply Hom.ext
  intro k
  exact (countdownExtension_finite enabled seed γ fuel k).trans
    (countdown_iteration enabled seed γ fuel k).symm

theorem countdown_selected {Γ : Assembly} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (γ : Γ.Carrier) (k : Nat) :
    ((cutSelected sequenceAlgebra partialSequences_complete (countdown enabled seed)).toFun γ).toFun k =
      countdownLimit (enabled.toFun γ) (seed.toFun γ) none k := by
  change ((cutExtend partialSequences_complete (strictIteration sequenceAlgebra
    (countdown enabled seed))).toFun (γ,⟨none⟩)).toFun k = _
  rw [countdownExtension_is_extension]
  exact countdownExtension_apply _ _ _ _ _

end Realizability.Assembly
