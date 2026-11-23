import SquareKit.Internal.Cubical.CartesianLargeFamilyConstructors
import SquareKit.Internal.Cubical.CartesianEquivalenceExtension

/-! Substitution comparisons are isomorphisms of decoded families. Each compares
restriction with a constructor independently rebuilt from substituted inputs. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.SmallUniverse.LargeConstructors
open CategoryTheory
universe u
variable {Ξ Ω : Context.{u+1}}

private theorem pi_reindex_family {Γ Δ E : Context.{u+1}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B)
    (σ : E ⟶ Γ) (p : total (interval Δ) ⟶ E) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (Cartesian.pi A B) (p ≫ σ)) φ r) :
    (piFilling (F.reindex σ) (hF.reindex σ) (G.reindex (liftSub A σ))).fill p φ r
      (b.map (Functor.whiskerLeft p.mapElements (piReindex A B σ))) =
      Term.map (Functor.whiskerLeft p.mapElements (piReindex A B σ))
        ((piFilling F hF G).fill (p ≫ σ) φ r b) := by
  apply Term.map_injective_of_iso (piReindexIso (reindex A σ) (reindex B (liftSub A σ)) p)
  exact (FunctionFilling.fill_normalize _ _ _ _ _ _ _).trans
    (FunctionFilling.fill_normalize F hF G (p ≫ σ) φ r b).symm

private theorem pi_reindex {Γ E : Context.{u+1}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (σ : E ⟶ Γ) :
    ((piFilling F hF G).reindex σ).transport (piReindexIso A B σ) =
      piFilling (F.reindex σ) (hF.reindex σ) (G.reindex (liftSub A σ)) := by
  apply Filling.ext
  intro Δ p φ r b
  let e := Functor.isoWhiskerLeft p.mapElements (piReindexIso A B σ)
  exact (pi_reindex_family F hF G σ p φ r (b.map e.inv)).symm.trans
    (congrArg (fun z => (piFilling (F.reindex σ) (hF.reindex σ)
      (G.reindex (liftSub A σ))).fill p φ r z) (OpenBox.map_iso_roundtrip e b))

private theorem transport_trans {C D E : Family Ξ} (F : Filling C)
    (e : C ≅ D) (d : D ≅ E) :
    (F.transport e).transport d = F.transport (e.trans d) := rfl

private theorem transport_cancel {C D E : Family Ξ} (F : Filling D)
    (e : C ≅ D) (d : E ≅ D) :
    (F.transport e.symm).transport (e ≪≫ d.symm) = F.transport d.symm := by
  rw [transport_trans]
  congr 1
  simp

private theorem transport_middle {C D E H : Family Ξ} (F : Filling D) (G : Filling H)
    (e : C ≅ D) (k : D ≅ H) (d : E ≅ H) (h : F.transport k = G) :
    (F.transport e.symm).transport (e ≪≫ k ≪≫ d.symm) = G.transport d.symm := by
  rw [transport_trans, ← h, transport_trans]
  congr 1
  simp

theorem construct_filling {C : Family Ξ} (P : SmallPresentation.Data C)
    (F : Filling C) (hF : F.Lawful) :
    (construct P F hF).filling.transport (construct P F hF).decoding = F := by
  change (F.transport (P.nativeIso F hF).symm).transport (P.nativeIso F hF) = F
  rw [transport_trans]
  simp only [Iso.symm_self_id]
  rfl

def Result.reindex {C : Family Ξ} (R : Result C) (σ : Ω ⟶ Ξ) : Result (Cartesian.reindex C σ) where
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
      liftedDecode (path (liftSub (interval Ξ) σ ≫ b) (Term.reindex a₀ σ) (Term.reindex a₁ σ)).code :=
  Functor.isoWhiskerLeft σ.mapElements (path b a₀ a₁).decoding ≪≫
    pathReindexIso (liftedDecode b) a₀ a₁ σ ≪≫
    (path (liftSub (interval Ξ) σ ≫ b) (Term.reindex a₀ σ) (Term.reindex a₁ σ)).decoding.symm

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
  exact transport_middle F G e k d (pi_reindex (NativeDecode.filling a) (NativeDecode.filling_lawful a)
      (NativeDecode.filling b) σ)

theorem pathSubstitution_filling (b : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (a₀ : Term (reindex (liftedDecode b) (endpointSub Ξ false)))
    (a₁ : Term (reindex (liftedDecode b) (endpointSub Ξ true))) (σ : Ω ⟶ Ξ) :
    ((path b a₀ a₁).filling.reindex σ).transport (pathSubstitution b a₀ a₁ σ) =
      (path (liftSub (interval Ξ) σ ≫ b) (Term.reindex a₀ σ) (Term.reindex a₁ σ)).filling := by
  let e := Functor.isoWhiskerLeft σ.mapElements (path b a₀ a₁).decoding
  let k := pathReindexIso (liftedDecode b) a₀ a₁ σ
  let d := (path (liftSub (interval Ξ) σ ≫ b) (Term.reindex a₀ σ) (Term.reindex a₁ σ)).decoding
  let F := (pathFilling (NativeDecode.filling b) (NativeDecode.filling_lawful b) a₀ a₁).reindex σ
  let G := pathFilling (NativeDecode.filling (liftSub (interval Ξ) σ ≫ b))
    (NativeDecode.filling_lawful _) (Term.reindex a₀ σ) (Term.reindex a₁ σ)
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

@[simp] theorem piSubstitution_id (a : Ξ ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) :
    piSubstitution a b (𝟙 Ξ) = Iso.refl _ := by
  apply Iso.ext
  change (pi a b).decoding.hom ≫ 𝟙 _ ≫ (pi a b).decoding.inv = 𝟙 _
  simp

@[simp] theorem pathSubstitution_id (b : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (a₀ : Term (reindex (liftedDecode b) (endpointSub Ξ false)))
    (a₁ : Term (reindex (liftedDecode b) (endpointSub Ξ true))) :
    pathSubstitution b a₀ a₁ (𝟙 Ξ) = Iso.refl _ := by
  apply Iso.ext
  change (path b a₀ a₁).decoding.hom ≫ 𝟙 _ ≫ (path b a₀ a₁).decoding.inv = 𝟙 _
  simp

set_option backward.isDefEq.respectTransparency false in
theorem piSubstitution_comp {Θ : Context.{u+1}}
    (a : Ξ ⟶ smallFamilyCodes.{u}) (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u})
    (σ : Ω ⟶ Ξ) (τ : Θ ⟶ Ω) :
    piSubstitution a b (τ ≫ σ) =
      Functor.isoWhiskerLeft τ.mapElements (piSubstitution a b σ) ≪≫
        piSubstitution (σ ≫ a) (liftSub (liftedDecode a) σ ≫ b) τ := by
  apply Iso.ext
  simp only [piSubstitution, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_comp, piReindexIso]
  rw [piReindex_comp]
  simp only [Category.assoc, ← Functor.isoWhiskerLeft_inv,
    ← Functor.isoWhiskerLeft_hom, Iso.inv_hom_id_assoc]
  rfl
set_option backward.isDefEq.respectTransparency false in
theorem pathSubstitution_comp {Θ : Context.{u+1}}
    (b : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (a₀ : Term (reindex (liftedDecode b) (endpointSub Ξ false)))
    (a₁ : Term (reindex (liftedDecode b) (endpointSub Ξ true)))
    (σ : Ω ⟶ Ξ) (τ : Θ ⟶ Ω) :
    pathSubstitution b a₀ a₁ (τ ≫ σ) =
      Functor.isoWhiskerLeft τ.mapElements (pathSubstitution b a₀ a₁ σ) ≪≫
        pathSubstitution (liftSub (interval Ξ) σ ≫ b)
          (Term.reindex a₀ σ) (Term.reindex a₁ σ) τ := by
  apply Iso.ext
  simp only [pathSubstitution, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_comp, pathReindexIso]
  rw [pathReindex_comp]
  simp only [Category.assoc, ← Functor.isoWhiskerLeft_inv,
    ← Functor.isoWhiskerLeft_hom, Iso.inv_hom_id_assoc]
  rfl

end SquareKit.Cubical.Cartesian.SmallUniverse.LargeConstructors
