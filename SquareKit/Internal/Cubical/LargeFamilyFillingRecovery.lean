import SquareKit.Internal.Cubical.LargeFamilySubstitution
import SquareKit.Internal.Cubical.UniverseRaisingNaturality

/-! Recovery of the full selected filling operation through small chart classification. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse
open CategoryTheory
universe u

namespace SmallPresentation.Data
variable {Ξ : Context.{u+1}} {C : Family Ξ} (P : SmallPresentation.Data C)
  (F : Filling C) (hF : F.Lawful)

/-- Restricting the large classifier records the entire supplied chart family. -/
theorem localFamily_code {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) :
    (P.localFamily F hF σ).code = σ ≫ P.code F hF := by
  ext I x
  change (P.localFamily F hF σ).reindex (represented (Γ.elementsMk I x.down)) =
    P.localFamily F hF (chart (Ξ.elementsMk I (σ.app I x)))
  rw [P.local_reindex]
  apply congrArg (P.localFamily F hF)
  ext J y
  exact σ.naturality_apply y.down.down.op x

/-- Small decoding recovers the chart's family, filler and lawfulness record. -/
theorem decoded_localFamily {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) :
    decodedLocalFamily (σ ≫ P.code F hF) = P.localFamily F hF σ := by
  rw [← P.localFamily_code F hF σ]
  exact LocalFamily.decoded_code _

def localDecodeIso {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) :
    Presheaf.decode (σ ≫ P.code F hF) ≅ P.chartFamily σ :=
  eqToIso (congrArg LocalFamily.family (P.decoded_localFamily F hF σ))

private theorem record_filling {Γ : Context.{u}} (A B : LocalFamily Γ) (h : A = B) :
    A.toNative.filling.transport (eqToIso (congrArg LocalFamily.family h)) = B.toNative.filling := by
  cases h
  rfl

theorem localDecodeIso_filling {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) :
    (decodedLocalFamily (σ ≫ P.code F hF)).toNative.filling.transport
        (P.localDecodeIso F hF σ) =
      LowerFilling.operation ((F.reindex σ).transport (P.chartIso σ).symm) := by
  refine (record_filling _ _ (P.decoded_localFamily F hF σ)).trans ?_
  exact Filling.toLocal_toFilling _ (LowerFilling.lawful _
    ((F.reindex σ).transport_lawful _ (hF.reindex σ)))

private theorem small_map_eqToHom_heq (S : Ξ.Elements ⥤ Type u) {x y : Ξ.Elements}
    (h : x = y) (a : S.obj x) : HEq (S.map (eqToHom h) a) a := by
  cases h
  exact heq_of_eq (ConcreteCategory.congr_hom (S.map_id x) a)

/-- The local comparison uses the same fiber maps as the global decoder. -/
theorem localDecodeIso_native {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) :
    Raising.iso (P.localDecodeIso F hF σ) ≪≫ P.chartIso σ =
      Functor.isoWhiskerLeft σ.mapElements (P.nativeIso F hF) := by
  apply Iso.ext
  ext x a
  change P.equiv (σ.mapElements.obj x)
    ((P.localDecodeIso F hF σ).hom.app ((Raising.lowerElements Γ).obj x) a.down) =
    P.equiv (σ.mapElements.obj x) ((P.decodeIso F hF).hom.app (σ.mapElements.obj x) a.down)
  apply congrArg (P.equiv (σ.mapElements.obj x))
  apply eq_of_heq
  exact (family_eqToIso_hom_heq _ _ _).trans
    (small_map_eqToHom_heq P.family (generic_source (σ.mapElements.obj x)) a.down).symm

/-- Complete selected chart sections are recovered before raising back to the large context. -/
theorem chartFilled_recovery {Δ : Context.{u+1}} {Γ : Context.{u}}
    (p : total (Presheaf.interval Δ) ⟶ Ξ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (liftedDecode (P.code F hF)) p) φ)
    (σ : raisedContext Γ ⟶ Δ) :
    Term.map (P.localDecodeIso F hF (chartInterval σ ≫ p)).hom
        (NativeDecode.chartFilled (p ≫ P.code F hF) b σ) =
      (LowerFilling.operation ((F.reindex (chartInterval σ ≫ p)).transport
        (P.chartIso (chartInterval σ ≫ p)).symm)).fill (𝟙 _) (chartFace φ σ)
        ((NativeDecode.chartBox (p ≫ P.code F hF) b σ).map
          (P.localDecodeIso F hF (chartInterval σ ≫ p)).hom) := by
  rw [← P.localDecodeIso_filling F hF (chartInterval σ ≫ p)]
  change _ = Term.map _ ((decodedLocalFamily (chartInterval σ ≫ p ≫ P.code F hF)).toNative.filling.fill (𝟙 _) _ _)
  apply congrArg (Term.map (P.localDecodeIso F hF (chartInterval σ ≫ p)).hom)
  apply congrArg (fun b => (decodedLocalFamily (chartInterval σ ≫ p ≫ P.code F hF)).toNative.filling.fill
    (𝟙 _) (chartFace φ σ) b)
  exact (OpenBox.map_iso_roundtrip (P.localDecodeIso F hF (chartInterval σ ≫ p)).symm _).symm

theorem chartBox_recovery {Δ : Context.{u+1}} {Γ : Context.{u}}
    (p : total (Presheaf.interval Δ) ⟶ Ξ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (liftedDecode (P.code F hF)) p) φ)
    (σ : raisedContext Γ ⟶ Δ) :
    (LowerFilling.box (𝟙 _) ((NativeDecode.chartBox (p ≫ P.code F hF) b σ).map
      (P.localDecodeIso F hF (chartInterval σ ≫ p)).hom)).map
        (Functor.whiskerLeft (LowerFilling.intervalSub (𝟙 _)).mapElements
          (P.chartIso (chartInterval σ ≫ p)).hom) =
      (b.map (Functor.whiskerLeft p.mapElements (P.nativeIso F hF).hom)).reindex σ := by
  apply OpenBox.ext
  · apply PartialSection.ext
    intro x hx
    exact congrArg (fun e => e.hom.app
      ((LowerFilling.intervalSub (𝟙 _)).mapElements.obj x)
      ⟨(b.tube.val ((liftSub (Presheaf.interval Δ) σ).mapElements.obj x) hx).down⟩)
      (P.localDecodeIso_native F hF (chartInterval σ ≫ p))
  · apply Term.ext
    intro x
    exact congrArg (fun e => e.hom.app
      ((raisedSub (endpointSub Γ false)).mapElements.obj x)
      ⟨(b.base.val (σ.mapElements.obj x)).down⟩)
      (P.localDecodeIso_native F hF (chartInterval σ ≫ p))

/-- Raising the recovered selected chart section agrees with the original full filler. -/
theorem chartFilled_native {Δ : Context.{u+1}} {Γ : Context.{u}}
    (p : total (Presheaf.interval Δ) ⟶ Ξ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (liftedDecode (P.code F hF)) p) φ)
    (σ : raisedContext Γ ⟶ Δ) :
    Term.map (Functor.whiskerLeft (chartInterval σ ≫ p).mapElements (P.nativeIso F hF).hom)
        (Raising.raiseTerm (NativeDecode.chartFilled (p ≫ P.code F hF) b σ)) =
      (F.fill p φ (b.map (Functor.whiskerLeft p.mapElements (P.nativeIso F hF).hom))).reindex
        (chartInterval σ) := by
  refine (congrArg (fun e => Term.map e.hom
    (Raising.raiseTerm (NativeDecode.chartFilled (p ≫ P.code F hF) b σ)))
    (P.localDecodeIso_native F hF (chartInterval σ ≫ p))).symm.trans ?_
  change Term.map (P.chartIso (chartInterval σ ≫ p)).hom
    (Raising.raiseTerm (Term.map (P.localDecodeIso F hF (chartInterval σ ≫ p)).hom
      (NativeDecode.chartFilled (p ≫ P.code F hF) b σ))) = _
  rw [P.chartFilled_recovery F hF]
  let c := (LowerFilling.box (𝟙 _) ((NativeDecode.chartBox (p ≫ P.code F hF) b σ).map
    (P.localDecodeIso F hF (chartInterval σ ≫ p)).hom)).map
      (Functor.whiskerLeft (LowerFilling.intervalSub (𝟙 _)).mapElements
        (P.chartIso (chartInterval σ ≫ p)).hom)
  let t := F.fill (liftSub (Presheaf.interval Δ) σ ≫ p) (φ.reindex σ) c
  have hb : c = (b.map (Functor.whiskerLeft p.mapElements (P.nativeIso F hF).hom)).reindex σ :=
    P.chartBox_recovery F hF p φ b σ
  have hu : t = (F.fill p φ
      (b.map (Functor.whiskerLeft p.mapElements (P.nativeIso F hF).hom))).reindex
        (liftSub (Presheaf.interval Δ) σ) := by
    dsimp only [t]
    rw [hb]
    exact hF.uniform p φ _ σ
  apply Term.ext
  intro x
  change (P.chartIso (chartInterval σ ≫ p)).hom.app x
    ((P.chartIso (chartInterval σ ≫ p)).inv.app x
      (t.val ((raisedIntervalIso Γ).hom.mapElements.obj x))) = _
  exact (congrArg (fun η => η.app x (t.val ((raisedIntervalIso Γ).hom.mapElements.obj x)))
      (P.chartIso (chartInterval σ ≫ p)).inv_hom_id).trans
    (congrArg (fun t => t.val ((raisedIntervalIso Γ).hom.mapElements.obj x)) hu)

/-- The reconstructed represented filler returns the complete supplied section. -/
theorem fillRepresented_recovery {I : Cube}
    (p : total (Presheaf.interval (representable.{u+1} I)) ⟶ Ξ)
    (φ : Cofibration (representable.{u+1} I))
    (b : OpenBox (reindex (liftedDecode (P.code F hF)) p) φ) :
    Term.map (Functor.whiskerLeft p.mapElements (P.nativeIso F hF).hom)
        (NativeDecode.fillRepresented (p ≫ P.code F hF) b) =
      F.fill p φ (b.map (Functor.whiskerLeft p.mapElements (P.nativeIso F hF).hom)) := by
  apply Term.ext
  intro x
  exact congrArg (fun t => t.val ((raisedElements _).obj
    ((NativeDecode.lowerIntervalElements I).obj x)))
    (P.chartFilled_native F hF p φ b (NativeDecode.representedRaise I))

/-- Classification and canonical decoding preserve the entire supplied lawful filling operation. -/
theorem native_filling_recovery :
    (NativeDecode.filling (P.code F hF)).transport (P.nativeIso F hF) = F := by
  let G := (NativeDecode.filling (P.code F hF)).transport (P.nativeIso F hF)
  have hG : G.Lawful := (NativeDecode.filling (P.code F hF)).transport_lawful
    (P.nativeIso F hF) (NativeDecode.filling_lawful (P.code F hF))
  have hrep {I : Cube} (p : total (Presheaf.interval (representable.{u+1} I)) ⟶ Ξ)
      (φ : Cofibration (representable.{u+1} I)) (b : OpenBox (reindex C p) φ) :
      G.fill p φ b = F.fill p φ b := by
    let d := b.map (Functor.whiskerLeft p.mapElements (P.nativeIso F hF).inv)
    have hn := congrArg (fun L : LocalFilling (liftedDecode (P.code F hF)) => L.fill p φ d)
      (LocalFilling.toFilling_toLocal (NativeDecode.localFilling (P.code F hF))
        (NativeDecode.localFilling_lawful (P.code F hF)))
    exact (congrArg (Term.map (Functor.whiskerLeft p.mapElements (P.nativeIso F hF).hom)) hn).trans
      ((P.fillRepresented_recovery F hF p φ d).trans
        (congrArg (F.fill p φ)
          (OpenBox.map_iso_roundtrip (Functor.isoWhiskerLeft p.mapElements (P.nativeIso F hF)) b)))
  apply Filling.ext
  intro Δ p φ b
  apply Term.ext
  intro x
  exact (G.toLocal_value hG p φ b x).symm.trans
    ((congrArg (fun t => (reindex C p).map (intervalEvaluation x) (t.val (intervalGeneric x)))
      (hrep (liftSub (Presheaf.interval Δ) (represented (intervalBase x)) ≫ p)
        (φ.reindex (represented (intervalBase x))) (b.reindex (represented (intervalBase x))))).trans
      (F.toLocal_value hF p φ b x))

end SmallPresentation.Data
namespace LargeConstructors
variable {Ξ : Context.{u+1}}

/-- The canonical decoder operation equals the operation returned by fixed construction. -/
theorem construct_native_filling {C : Family Ξ} (P : SmallPresentation.Data C)
    (F : Filling C) (hF : F.Lawful) :
    NativeDecode.filling (construct P F hF).code = (construct P F hF).filling := by
  have h := congrArg (fun G => G.transport (P.nativeIso F hF).symm)
    (P.native_filling_recovery F hF)
  rw [Filling.transport_trans, Iso.self_symm_id] at h
  exact h

theorem sigma_native_filling (a : Ξ ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) :
    NativeDecode.filling (sigma a b).code = (sigma a b).filling :=
  construct_native_filling _ _ _

theorem pi_native_filling (a : Ξ ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) :
    NativeDecode.filling (pi a b).code = (pi a b).filling :=
  construct_native_filling _ _ _

theorem path_native_filling (b : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (a₀ : Term (reindex (liftedDecode b) (endpointSub Ξ false)))
    (a₁ : Term (reindex (liftedDecode b) (endpointSub Ξ true))) :
    NativeDecode.filling (path b a₀ a₁).code = (path b a₀ a₁).filling :=
  construct_native_filling _ _ _

variable {Ω : Context.{u+1}}

/-- Canonical Sigma filling commutes with the fixed independently rebuilt decoder adapter. -/
theorem sigmaSubstitution_native_filling (a : Ξ ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) (σ : Ω ⟶ Ξ) :
    (NativeDecode.filling (σ ≫ (sigma a b).code)).transport (sigmaSubstitution a b σ) =
      NativeDecode.filling (sigma (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b)).code :=
  (congrArg (fun G => (G.reindex σ).transport (sigmaSubstitution a b σ))
    (sigma_native_filling a b)).trans ((sigmaSubstitution_filling a b σ).trans
      (sigma_native_filling (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b)).symm)

/-- Canonical Pi filling commutes with the fixed independently rebuilt decoder adapter. -/
theorem piSubstitution_native_filling (a : Ξ ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) (σ : Ω ⟶ Ξ) :
    (NativeDecode.filling (σ ≫ (pi a b).code)).transport (piSubstitution a b σ) =
      NativeDecode.filling (pi (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b)).code :=
  (congrArg (fun G => (G.reindex σ).transport (piSubstitution a b σ))
    (pi_native_filling a b)).trans ((piSubstitution_filling a b σ).trans
      (pi_native_filling (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b)).symm)

/-- Canonical Path filling commutes with the fixed independently rebuilt decoder adapter. -/
theorem pathSubstitution_native_filling (b : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (a₀ : Term (reindex (liftedDecode b) (endpointSub Ξ false)))
    (a₁ : Term (reindex (liftedDecode b) (endpointSub Ξ true))) (σ : Ω ⟶ Ξ) :
    (NativeDecode.filling (σ ≫ (path b a₀ a₁).code)).transport (pathSubstitution b a₀ a₁ σ) =
      NativeDecode.filling (path (liftSub (interval Ξ) σ ≫ b)
        (Term.reindex a₀ σ) (Term.reindex a₁ σ)).code :=
  (congrArg (fun G => (G.reindex σ).transport (pathSubstitution b a₀ a₁ σ))
    (path_native_filling b a₀ a₁)).trans ((pathSubstitution_filling b a₀ a₁ σ).trans
      (path_native_filling (liftSub (interval Ξ) σ ≫ b) (Term.reindex a₀ σ) (Term.reindex a₁ σ)).symm)

end LargeConstructors
end SquareKit.Cubical.Presheaf.SmallUniverse
