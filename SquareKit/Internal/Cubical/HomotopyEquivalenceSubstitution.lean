import SquareKit.Internal.Cubical.EquivalenceExtension

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

@[ext] theorem HomotopyEquivalence.ext {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    {E F : HomotopyEquivalence f} (h : E.fibers = F.fibers) : E = F := by
  cases E
  cases F
  cases h
  rfl

theorem HomotopyContractible.ext_pathApp {Γ : Context.{u}} {A : Family Γ}
    {c d : HomotopyContractible A} (hc : c.center = d.center)
    (hp : pathApp c.contraction = pathApp d.contraction) : c = d :=
  HomotopyContractible.ext hc (pathTerm_hext c.contraction d.contraction hp)

theorem HomotopyContractible.reindex_comp {Γ Δ Θ : Context.{u}} {A : Family Γ}
    (c : HomotopyContractible A) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    (c.reindex σ).reindex τ = c.reindex (τ ≫ σ) := by
  apply HomotopyContractible.ext_pathApp
  · rfl
  · rfl

theorem HomotopyContractible.transport_trans {Γ : Context.{u}} {A B C : Family Γ}
    (c : HomotopyContractible A) (e : A ≅ B) (d : B ≅ C) :
    (c.transport e).transport d = c.transport (e ≪≫ d) := by
  apply HomotopyContractible.ext_pathApp
  · rfl
  · apply Term.ext
    intro x
    rfl

theorem HomotopyContractible.reindex_transport_comp {Γ Δ Θ : Context.{u}}
    {A : Family Γ} {B : Family Δ} {C : Family Θ}
    (c : HomotopyContractible A) (σ : Δ ⟶ Γ) (e : Presheaf.reindex A σ ≅ B)
    (τ : Θ ⟶ Δ) (d : Presheaf.reindex B τ ≅ C) :
    (((c.reindex σ).transport e).reindex τ).transport d =
      (c.reindex (τ ≫ σ)).transport (Functor.isoWhiskerLeft τ.mapElements e ≪≫ d) :=
  (congrArg (fun k => k.transport d) ((c.reindex σ).transport_reindex e τ)).trans
    ((HomotopyContractible.transport_trans ((c.reindex σ).reindex τ)
      (Functor.isoWhiskerLeft τ.mapElements e) d).trans
        (congrArg (fun k => k.transport (Functor.isoWhiskerLeft τ.mapElements e ≪≫ d))
          (c.reindex_comp σ τ)))

theorem genericFiberReindexIso_comp {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    Functor.isoWhiskerLeft (liftSub (Presheaf.reindex B σ) τ).mapElements
      (genericFiberReindexIso f σ) ≪≫
      genericFiberReindexIso (Functor.whiskerLeft σ.mapElements f) τ =
    genericFiberReindexIso f (τ ≫ σ) := by
  apply Iso.ext
  rfl

/-- Iterated substitution retains the entire chosen fiber contraction. -/
theorem HomotopyEquivalence.reindex_comp {Γ Δ Θ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    (E.reindex σ).reindex τ = E.reindex (τ ≫ σ) := by
  apply HomotopyEquivalence.ext
  change (((E.fibers.reindex (liftSub B σ)).transport (genericFiberReindexIso f σ)).reindex
    (liftSub (Presheaf.reindex B σ) τ)).transport
      (genericFiberReindexIso (Functor.whiskerLeft σ.mapElements f) τ) = _
  rw [HomotopyContractible.transport_reindex, HomotopyContractible.reindex_comp]
  exact (HomotopyContractible.transport_trans
    (E.fibers.reindex (liftSub B (τ ≫ σ)))
    (Functor.isoWhiskerLeft (liftSub (Presheaf.reindex B σ) τ).mapElements
      (genericFiberReindexIso f σ))
    (genericFiberReindexIso (Functor.whiskerLeft σ.mapElements f) τ)).trans
      (congrArg (fun e => (E.fibers.reindex (liftSub B (τ ≫ σ))).transport e)
        (genericFiberReindexIso_comp f σ τ))

end SquareKit.Cubical.Presheaf
