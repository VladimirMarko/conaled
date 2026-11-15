import SquareKit.Internal.Cubical.LargeFamilyConstructors
import SquareKit.Internal.Cubical.FillingTransportLaws

/-! Substitution comparisons are isomorphisms of decoded families. Each compares
restriction with a constructor independently rebuilt from substituted inputs. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.LargeConstructors
open CategoryTheory
universe u
variable {Ξ Ω : Context.{u+1}}

private theorem transport_cancel {C D E : Family Ξ} (F : Filling D)
    (e : C ≅ D) (d : E ≅ D) :
    (F.transport e.symm).transport (e ≪≫ d.symm) = F.transport d.symm := by
  rw [Filling.transport_trans]
  congr 1
  simp

private theorem transport_middle {C D E H : Family Ξ} (F : Filling D) (G : Filling H)
    (e : C ≅ D) (k : D ≅ H) (d : E ≅ H) (h : F.transport k = G) :
    (F.transport e.symm).transport (e ≪≫ k ≪≫ d.symm) = G.transport d.symm := by
  rw [Filling.transport_trans, ← h, Filling.transport_trans]
  congr 1
  simp

theorem construct_filling {C : Family Ξ} (P : SmallPresentation.Data C)
    (F : Filling C) (hF : F.Lawful) :
    (construct P F hF).filling.transport (construct P F hF).decoding = F := by
  change (F.transport (P.nativeIso F hF).symm).transport (P.nativeIso F hF) = F
  rw [Filling.transport_trans]
  simp only [Iso.symm_self_id]
  rfl

def Result.reindex {C : Family Ξ} (R : Result C) (σ : Ω ⟶ Ξ) : Result (Presheaf.reindex C σ) where
  code := σ ≫ R.code
  decoding := Functor.isoWhiskerLeft σ.mapElements R.decoding
  filling := R.filling.reindex σ
  lawful := R.lawful.reindex σ

noncomputable def sigmaSubstitution (a : Ξ ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) (σ : Ω ⟶ Ξ) :
    liftedDecode (σ ≫ (sigma a b).code) ≅
      liftedDecode (sigma (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b)).code :=
  Functor.isoWhiskerLeft σ.mapElements (sigma a b).decoding ≪≫
    (sigma (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b)).decoding.symm

noncomputable def piSubstitution (a : Ξ ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) (σ : Ω ⟶ Ξ) :
    liftedDecode (σ ≫ (pi a b).code) ≅
      liftedDecode (pi (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b)).code :=
  Functor.isoWhiskerLeft σ.mapElements (pi a b).decoding ≪≫
    piReindexIso (liftedDecode a) (liftedDecode b) σ ≪≫
    (pi (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b)).decoding.symm

noncomputable def pathSubstitution (b : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (a₀ : Term (reindex (liftedDecode b) (endpointSub Ξ false)))
    (a₁ : Term (reindex (liftedDecode b) (endpointSub Ξ true))) (σ : Ω ⟶ Ξ) :
    liftedDecode (σ ≫ (path b a₀ a₁).code) ≅
      liftedDecode (path (liftSub (interval Ξ) σ ≫ b) (a₀.reindex σ) (a₁.reindex σ)).code :=
  Functor.isoWhiskerLeft σ.mapElements (path b a₀ a₁).decoding ≪≫
    pathReindexIso (liftedDecode b) a₀ a₁ σ ≪≫
    (path (liftSub (interval Ξ) σ ≫ b) (a₀.reindex σ) (a₁.reindex σ)).decoding.symm

theorem sigmaSubstitution_filling (a : Ξ ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) (σ : Ω ⟶ Ξ) :
    ((sigma a b).filling.reindex σ).transport (sigmaSubstitution a b σ) =
      (sigma (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b)).filling := by
  let e := Functor.isoWhiskerLeft σ.mapElements (sigma a b).decoding
  let d := (sigma (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b)).decoding
  let F := (sigmaFilling (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling b)).reindex σ
  change (F.transport e.symm).transport (e ≪≫ d.symm) = F.transport d.symm
  exact transport_cancel F e d

theorem piSubstitution_filling (a : Ξ ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) (σ : Ω ⟶ Ξ) :
    ((pi a b).filling.reindex σ).transport (piSubstitution a b σ) =
      (pi (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b)).filling := by
  let e := Functor.isoWhiskerLeft σ.mapElements (pi a b).decoding
  let k := piReindexIso (liftedDecode a) (liftedDecode b) σ
  let d := (pi (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b)).decoding
  let F := (piFilling (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling b)).reindex σ
  let G := piFilling (NativeDecode.filling (σ ≫ a)) (NativeDecode.filling_lawful (σ ≫ a))
    (NativeDecode.filling (liftSub (liftedDecode a) σ ≫ b))
  change (F.transport e.symm).transport (e ≪≫ k ≪≫ d.symm) = G.transport d.symm
  exact transport_middle F G e k d (Filling.transport_eq _ _ _
    (piFilling_reindex (NativeDecode.filling a) (NativeDecode.filling_lawful a)
      (NativeDecode.filling b) σ))

theorem pathSubstitution_filling (b : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (a₀ : Term (reindex (liftedDecode b) (endpointSub Ξ false)))
    (a₁ : Term (reindex (liftedDecode b) (endpointSub Ξ true))) (σ : Ω ⟶ Ξ) :
    ((path b a₀ a₁).filling.reindex σ).transport (pathSubstitution b a₀ a₁ σ) =
      (path (liftSub (interval Ξ) σ ≫ b) (a₀.reindex σ) (a₁.reindex σ)).filling := by
  let e := Functor.isoWhiskerLeft σ.mapElements (path b a₀ a₁).decoding
  let k := pathReindexIso (liftedDecode b) a₀ a₁ σ
  let d := (path (liftSub (interval Ξ) σ ≫ b) (a₀.reindex σ) (a₁.reindex σ)).decoding
  let F := (pathFilling (NativeDecode.filling b) (NativeDecode.filling_lawful b) a₀ a₁).reindex σ
  let G := pathFilling (NativeDecode.filling (liftSub (interval Ξ) σ ≫ b))
    (NativeDecode.filling_lawful _) (a₀.reindex σ) (a₁.reindex σ)
  change (F.transport e.symm).transport (e ≪≫ k ≪≫ d.symm) = G.transport d.symm
  exact transport_middle F G e k d
    (pathFilling_reindex_iso (NativeDecode.filling b) (NativeDecode.filling_lawful b) a₀ a₁ σ)

theorem sigmaSubstitution_comp {Θ : Context.{u+1}}
    (a : Ξ ⟶ smallFamilyCodes.{u}) (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u})
    (σ : Ω ⟶ Ξ) (τ : Θ ⟶ Ω) :
    sigmaSubstitution a b (τ ≫ σ) =
      Functor.isoWhiskerLeft τ.mapElements (sigmaSubstitution a b σ) ≪≫
        sigmaSubstitution (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b) τ := by
  apply Iso.ext
  ext x z
  let d := (sigma (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b)).decoding
  exact congrArg ((sigma ((τ ≫ σ) ≫ a)
    (liftSub (liftedDecode a) (τ ≫ σ) ≫ b)).decoding.inv.app x)
    (congrArg (fun k => k.app (τ.mapElements.obj x)
      ((sigma a b).decoding.hom.app ((τ ≫ σ).mapElements.obj x) z)) d.inv_hom_id).symm

end SquareKit.Cubical.Presheaf.SmallUniverse.LargeConstructors
