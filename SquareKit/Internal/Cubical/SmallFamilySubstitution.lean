import SquareKit.Internal.Cubical.SmallFamilyConstructors

/-! Decoded constructor codes commute with dependent substitution through the
native comparison isomorphisms. These are not source conversion judgments. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def sigmaCode_reindex {Γ Δ : Context.{u}}
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (b : raisedContext (total (decode a)) ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) :
    decode (raisedSub σ ≫ sigmaCode a b) ≅
      decode (sigmaCode (raisedSub σ ≫ a) (raisedSub (liftSub (decode a) σ) ≫ b)) :=
  eqToIso (decode_reindex (sigmaCode a b) σ) ≪≫
    Functor.isoWhiskerLeft σ.mapElements (sigmaCode_decode a b) ≪≫
    (sigmaCode_decode (raisedSub σ ≫ a) (raisedSub (liftSub (decode a) σ) ≫ b)).symm

noncomputable def piCode_reindex {Γ Δ : Context.{u}}
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (b : raisedContext (total (decode a)) ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) :
    decode (raisedSub σ ≫ piCode a b) ≅
      decode (piCode (raisedSub σ ≫ a) (raisedSub (liftSub (decode a) σ) ≫ b)) :=
  eqToIso (decode_reindex (piCode a b) σ) ≪≫
    Functor.isoWhiskerLeft σ.mapElements (piCode_decode a b) ≪≫
    piReindexIso (decode a) (decode b) σ ≪≫
    (piCode_decode (raisedSub σ ≫ a) (raisedSub (liftSub (decode a) σ) ≫ b)).symm

noncomputable def pathCode_reindex {Γ Δ : Context.{u}}
    (b : raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u})
    (a₀ : Term (Presheaf.reindex (decode b) (endpointSub Γ false)))
    (a₁ : Term (Presheaf.reindex (decode b) (endpointSub Γ true))) (σ : Δ ⟶ Γ) :
    decode (raisedSub σ ≫ pathCode b a₀ a₁) ≅
      decode (pathCode (raisedSub (liftSub (interval Γ) σ) ≫ b) (a₀.reindex σ) (a₁.reindex σ)) :=
  eqToIso (decode_reindex (pathCode b a₀ a₁) σ) ≪≫
    Functor.isoWhiskerLeft σ.mapElements (pathCode_decode b a₀ a₁) ≪≫
    pathReindexIso (decode b) a₀ a₁ σ ≪≫
    (pathCode_decode (raisedSub (liftSub (interval Γ) σ) ≫ b) (a₀.reindex σ) (a₁.reindex σ)).symm

def discreteCode_reindex {Γ Δ : Context.{u}} {T : Type u}
    (q : Term (constantFamily Γ T)) (S : T → Type u) (σ : Δ ⟶ Γ) :
    decode (raisedSub σ ≫ discreteCode q S) ≅ decode (discreteCode (q.reindex σ) S) :=
  eqToIso (decode_reindex (discreteCode q S) σ) ≪≫
    Functor.isoWhiskerLeft σ.mapElements (discreteCode_decode q S) ≪≫
    (discreteCode_decode (q.reindex σ) S).symm


theorem LocalFamily.toNative_reindex {Γ Δ : Context.{u}} (A : LocalFamily Γ) (σ : Δ ⟶ Γ) :
    (A.reindex σ).toNative = A.toNative.reindex σ := rfl

theorem LocalFamily.sigma_reindex {Γ Δ : Context.{u}} (A : LocalFamily Γ)
    (B : LocalFamily (total A.family)) (σ : Δ ⟶ Γ) :
    (A.sigma B).reindex σ = (A.reindex σ).sigma (B.reindex (liftSub A.family σ)) := rfl

theorem LocalFamily.pi_reindex_filling {Γ Δ : Context.{u}} (A : LocalFamily Γ)
    (B : LocalFamily (total A.family)) (σ : Δ ⟶ Γ) {I : Cube}
    (p : total (interval (representable.{u} I)) ⟶ Δ)
    (φ : Cofibration (representable.{u} I))
    (b : OpenBox (Presheaf.reindex (Presheaf.pi A.family B.family) (p ≫ σ)) φ) :
    ((A.reindex σ).pi (B.reindex (liftSub A.family σ))).filling.fill p φ
      (b.map (Functor.whiskerLeft p.mapElements (piReindex A.family B.family σ))) =
      Term.map (Functor.whiskerLeft p.mapElements (piReindex A.family B.family σ))
        ((A.pi B).filling.fill (p ≫ σ) φ b) :=
  piFilling_reindex A.toNative.filling A.toNative.lawful B.toNative.filling σ p φ b

theorem LocalFamily.path_reindex_filling {Γ Δ : Context.{u}}
    (B : LocalFamily (total (interval Γ)))
    (a₀ : Term (Presheaf.reindex B.family (endpointSub Γ false)))
    (a₁ : Term (Presheaf.reindex B.family (endpointSub Γ true))) (σ : Δ ⟶ Γ) {I : Cube}
    (p : total (interval (representable.{u} I)) ⟶ Δ)
    (φ : Cofibration (representable.{u} I))
    (b : OpenBox (Presheaf.reindex (Presheaf.path B.family a₀ a₁) (p ≫ σ)) φ) :
    ((B.reindex (liftSub (interval Γ) σ)).path (a₀.reindex σ) (a₁.reindex σ)).filling.fill p φ
      (b.map (Functor.whiskerLeft p.mapElements (pathReindex B.family a₀ a₁ σ))) =
      Term.map (Functor.whiskerLeft p.mapElements (pathReindex B.family a₀ a₁ σ))
        ((B.path a₀ a₁).filling.fill (p ≫ σ) φ b) :=
  pathFilling_reindex_family B.toNative.filling B.toNative.lawful a₀ a₁ σ p φ b

theorem LocalFamily.discrete_reindex {Γ Δ : Context.{u}} {T : Type u}
    (q : Term (constantFamily Γ T)) (S : T → Type u) (σ : Δ ⟶ Γ) :
    (LocalFamily.discrete q S).reindex σ = LocalFamily.discrete (q.reindex σ) S := rfl

end SquareKit.Cubical.Presheaf
