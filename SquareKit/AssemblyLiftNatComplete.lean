import SquareKit.AssemblyCutSearchGraph
import SquareKit.AssemblyNatComplete

/-! Concrete, uniformly tracked extension of lifted-natural cut arrows. -/
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

noncomputable def liftNatExtensionValue {Γ : Assembly}
    (h : Hom (prod Γ iterationCuts) (programLift (encoded Nat)))
    (γ : Γ.Carrier) (t : Option Nat) : Option Nat := match t with
  | some n => h.toFun (γ, ⟨n⟩)
  | none => cutLimitValue (fun n => h.toFun (γ, ⟨n⟩))

theorem liftNatExtension_graph {Γ : Assembly}
    {h : Hom (prod Γ iterationCuts) (programLift (encoded Nat))}
    {p : Code} (hp : Tracks (prod Γ iterationCuts) (programLift (encoded Nat)) p.eval h.toFun)
    {γ : Γ.Carrier} {r : Nat} (hr : Γ.realizes r γ)
    {e : Nat} {t : Option Nat} (he : finalCuts.{0}.realizes e ⟨t⟩) (v : Nat) :
    v ∈ run (encode (searchCode (encode (observerCode p r)) e)) ↔
      liftNatExtensionValue h γ t = some v := by
  rw [cutSearch_mem hp hr]
  cases t with
  | some m =>
    change (∃ n, CutAccessible e n ∧ h.toFun (γ, ⟨n⟩) = some v) ↔
      h.toFun (γ, ⟨m⟩) = some v
    constructor
    · rintro ⟨n, hn, hv⟩
      exact cutArrow_mono h γ ((accessible_final he).mp hn) hv
    · intro hv
      exact ⟨m, (accessible_final he).mpr (Nat.le_refl m), hv⟩
  | none =>
    change (∃ n, CutAccessible e n ∧ h.toFun (γ, ⟨n⟩) = some v) ↔
      cutLimitValue (fun n => h.toFun (γ, ⟨n⟩)) = some v
    rw [cutLimitValue_eq_some _ (fun _ _ _ _ => cutArrow_values_agree h γ)]
    exact exists_congr fun n => and_iff_right ((accessible_final he).mpr trivial)

noncomputable def liftNatExtensionProgram (p : Code) (z : Nat) : Code :=
  searchCode (encode (observerCode p z.unpair.1)) z.unpair.2

theorem liftNatExtensionProgram_computable : Computable₂ liftNatExtensionProgram :=
  searchCode_computable.comp
    (Computable.encode.comp (observerCode_computable.comp Computable.fst
      (Computable.fst.comp (Primrec.unpair.to_comp.comp Computable.snd))))
    (Computable.snd.comp (Primrec.unpair.to_comp.comp Computable.snd))

/-- An ordinary total tracker emits the search program without waiting for its
partial result, so bottom receives a realizer as well. -/
noncomputable def liftNatExtension {Γ : Assembly}
    (h : Hom (prod Γ iterationCuts) (programLift (encoded Nat))) :
    Hom (prod Γ finalCuts) (programLift (encoded Nat)) where
  toFun x := liftNatExtensionValue h x.1 x.2.down
  tracked := by
    obtain ⟨p, hp⟩ := h.has_code
    refine ⟨fun z => Part.some (encode (liftNatExtensionProgram p z)), ?_, ?_⟩
    · exact Partrec.nat_iff.mp (Computable.encode.comp
        (liftNatExtensionProgram_computable.comp (Computable.const p) Computable.id))
    · rintro ⟨γ, ⟨t⟩⟩ z ⟨hr, he⟩
      refine ⟨encode (liftNatExtensionProgram p z), by simp, ?_⟩
      apply liftNat_realizes_iff.mpr
      exact liftNatExtension_graph hp hr he

/-- Concrete completeness includes extension tracking and uniqueness in every context. -/
theorem liftNat_cutComplete : CutComplete (programLift (encoded Nat)) := by
  intro Γ
  constructor
  · intro h k hk
    apply Hom.ext
    rintro ⟨γ, ⟨t⟩⟩
    cases t with
    | some n => exact congrArg (fun f => f.toFun (γ, ⟨n⟩)) hk
    | none =>
      apply Option.ext
      intro v
      change (h.toFun (γ, ⟨none⟩) = some v) ↔ (k.toFun (γ, ⟨none⟩) = some v)
      exact (cutArrow_infinity_iff h γ v).trans
        ((exists_congr fun n => Iff.of_eq
          (congrArg (fun x => x = some v) (congrArg (fun f => f.toFun (γ, ⟨n⟩)) hk))).trans
          (cutArrow_infinity_iff k γ v).symm)
  · intro h
    exact ⟨liftNatExtension h, Hom.ext fun _ => rfl⟩

end Realizability.Assembly
