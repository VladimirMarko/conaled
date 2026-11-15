import SquareKit.Internal.Cubical.EquivalenceFamilies
import SquareKit.Internal.Cubical.HomotopyEquivalenceSubstitution

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.EquivalenceFamilies
open CategoryTheory
universe u

private theorem contrReindexIso_comp {Γ Δ Θ : Context.{u}} (A : Family Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    Functor.isoWhiskerLeft τ.mapElements (contrReindexIso A σ) ≪≫
      contrReindexIso (reindex A σ) τ = contrReindexIso A (τ ≫ σ) := by
  apply Iso.ext
  rfl

private theorem reindexedDecode_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (s : Term (reindex (isEquiv f) σ)) :
    (reindexedIsEquivSections f (τ ≫ σ)).symm (s.reindex τ) =
      ((reindexedIsEquivSections f σ).symm s).reindex (liftSub (reindex B σ) τ) := by
  let C := homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)
  let p := piReindexIso B (contr C) σ
  let q := contrReindexIso C (liftSub B σ)
  let t := app (Term.map p.hom s)
  let ρ := liftSub (reindex B σ) τ
  have hp : app (Term.map (piReindexIso B (contr C) (τ ≫ σ)).hom (s.reindex τ)) =
      t.reindex ρ := rfl
  have hq := congrArg Iso.hom (contrReindexIso_comp C (liftSub B σ) ρ)
  have ht : Term.map (contrReindexIso C (liftSub B (τ ≫ σ))).hom (t.reindex ρ) =
      Term.map (contrReindexIso (reindex C (liftSub B σ)) ρ).hom
        ((Term.map q.hom t).reindex ρ) := by
    exact congrArg (fun m => Term.map m (t.reindex ρ)) hq.symm
  change decodeContr (Term.map (contrReindexIso C (liftSub B (τ ≫ σ))).hom
    (app (Term.map (piReindexIso B (contr C) (τ ≫ σ)).hom (s.reindex τ)))) = _
  exact (congrArg (fun z => decodeContr
      (Term.map (contrReindexIso C (liftSub B (τ ≫ σ))).hom z)) hp).trans
    ((congrArg decodeContr ht).trans
      (decodeContr_reindex (reindex C (liftSub B σ)) (Term.map q.hom t) ρ))

/-- Substitution retains the complete selected native fiber contraction. -/
theorem isEquivReindexSections_decode_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (s : Term (reindex (isEquiv f) σ)) :
    (isEquivReindexSections f (τ ≫ σ)).symm (s.reindex τ) =
      ((isEquivReindexSections f σ).symm s).reindex τ := by
  apply HomotopyEquivalence.ext
  let c := (reindexedIsEquivSections f σ).symm s
  let ρ := liftSub (reindex B σ) τ
  have h := (c.transport_reindex (genericFiberReindexIso f σ) ρ)
  have h' := HomotopyContractible.transport_trans (c.reindex ρ)
    (Functor.isoWhiskerLeft ρ.mapElements (genericFiberReindexIso f σ))
    (genericFiberReindexIso (Functor.whiskerLeft σ.mapElements f) τ)
  have h'' := congrArg (fun i => (c.reindex ρ).transport i)
    (genericFiberReindexIso_comp f σ τ)
  exact (congrArg (fun d => d.transport (genericFiberReindexIso f (τ ≫ σ)))
      (reindexedDecode_reindex f σ τ s)).trans
    (((congrArg (fun d => d.transport
      (genericFiberReindexIso (Functor.whiskerLeft σ.mapElements f) τ)) h).trans h').trans h'').symm

theorem isEquivReindexSections_comp {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (E : HomotopyEquivalence (Functor.whiskerLeft σ.mapElements f)) :
    isEquivReindexSections f (τ ≫ σ) (E.reindex τ) =
      (isEquivReindexSections f σ E).reindex τ := by
  apply (isEquivReindexSections f (τ ≫ σ)).symm.injective
  rw [Equiv.symm_apply_apply, isEquivReindexSections_decode_reindex, Equiv.symm_apply_apply]

end SquareKit.Cubical.Presheaf.EquivalenceFamilies
