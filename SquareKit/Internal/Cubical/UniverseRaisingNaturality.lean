import SquareKit.Internal.Cubical.UniverseRaising
import SquareKit.Internal.Cubical.HomotopyEquivalenceSubstitution

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace Raising

def iso {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) : family A ≅ family B where
  hom := map e.hom
  inv := map e.inv
  hom_inv_id := by
    ext x a
    exact congrArg ULift.up (congrArg (fun k => k.app ((lowerElements Γ).obj x) a.down) e.hom_inv_id)
  inv_hom_id := by
    ext x b
    exact congrArg ULift.up (congrArg (fun k => k.app ((lowerElements Γ).obj x) b.down) e.inv_hom_id)

theorem lowerContractible_transport {Γ : Context.{u}} {A B : Family Γ}
    (c : HomotopyContractible (family A)) (e : A ≅ B) :
    lowerContractible (c.transport (iso e)) = (lowerContractible c).transport e := by
  apply HomotopyContractible.ext_pathApp
  · rfl
  · apply Term.ext
    intro x
    rfl

/-- The comparison of whole generic fibers packages both representation changes. -/
def lowerFiberIso {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) :
    reindex (homotopyFiber (Functor.whiskerLeft (projection (family B)).mapElements (map f))
      (generic (family B))) (totalIso B).hom ≅
    family (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)) :=
  fiberReindexIso (Functor.whiskerLeft (projection (family B)).mapElements (map f))
    (generic (family B)) (totalIso B).hom ≪≫
      (fiberIso (Functor.whiskerLeft (projection B).mapElements f) (generic B)).symm

theorem lowerEquivalence_fibers {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (E : HomotopyEquivalence (map f)) :
    (lowerEquivalence (f := f) E).fibers =
    lowerContractible ((E.fibers.reindex (totalIso B).hom).transport (lowerFiberIso f)) :=
  congrArg lowerContractible (HomotopyContractible.transport_trans
    (E.fibers.reindex (totalIso B).hom)
    (fiberReindexIso (Functor.whiskerLeft (projection (family B)).mapElements (map f))
      (generic (family B)) (totalIso B).hom)
    (fiberIso (Functor.whiskerLeft (projection B).mapElements f) (generic B)).symm)

theorem fiberReindexIso_comp {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (b : Term B) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    Functor.isoWhiskerLeft τ.mapElements (fiberReindexIso f b σ) ≪≫
      fiberReindexIso (Functor.whiskerLeft σ.mapElements f) (b.reindex σ) τ =
    fiberReindexIso f b (τ ≫ σ) := by
  apply Iso.ext
  rfl

theorem fiberIso_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (b : Term B) (σ : Δ ⟶ Γ) :
    Functor.isoWhiskerLeft (raisedSub σ).mapElements (fiberIso f b) ≪≫
      fiberReindexIso (map f) (raiseTerm b) (raisedSub σ) =
    iso (fiberReindexIso f b σ) ≪≫
      fiberIso (Functor.whiskerLeft σ.mapElements f) (b.reindex σ) := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro z
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    apply PiElement.ext
    intro y g i
    rfl

private theorem inverse_square {C : Type*} [Category C] {A B D E : C}
    (i : A ≅ B) (k : B ≅ E) (j : A ≅ D) (l : D ≅ E)
    (h : i ≪≫ k = j ≪≫ l) : i.symm ≪≫ j = k ≪≫ l.symm := by
  apply Iso.ext
  apply (cancel_epi i.hom).mp
  apply (cancel_mono l.hom).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using (congrArg Iso.hom h).symm

theorem fiberIso_reindex_inv {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (b : Term B) (σ : Δ ⟶ Γ) :
    (Functor.isoWhiskerLeft (raisedSub σ).mapElements (fiberIso f b)).symm ≪≫
      iso (fiberReindexIso f b σ) =
    fiberReindexIso (map f) (raiseTerm b) (raisedSub σ) ≪≫
      (fiberIso (Functor.whiskerLeft σ.mapElements f) (b.reindex σ)).symm :=
  inverse_square _ _ _ _ (fiberIso_reindex f b σ)

theorem lowerFiberIso_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) :
    Functor.isoWhiskerLeft (totalIso (reindex B σ)).hom.mapElements
      (genericFiberReindexIso (map f) (raisedSub σ)) ≪≫
      lowerFiberIso (Functor.whiskerLeft σ.mapElements f) =
    Functor.isoWhiskerLeft (raisedSub (liftSub B σ)).mapElements (lowerFiberIso f) ≪≫
      iso (genericFiberReindexIso f σ) := by
  apply Iso.ext
  let F := Functor.whiskerLeft (projection (family B)).mapElements (map f)
  let p := generic (family B)
  let Q := Functor.isoWhiskerLeft (raisedSub (liftSub B σ)).mapElements
    (fiberReindexIso F p (totalIso B).hom)
  let J := fiberIso (Functor.whiskerLeft (projection (reindex B σ)).mapElements
    (Functor.whiskerLeft σ.mapElements f)) (generic (reindex B σ))
  have hP := (fiberReindexIso_comp F p (liftSub (family B) (raisedSub σ))
    (totalIso (reindex B σ)).hom).trans
      (fiberReindexIso_comp F p (totalIso B).hom (raisedSub (liftSub B σ))).symm
  have h := fiberIso_reindex_inv (Functor.whiskerLeft (projection B).mapElements f)
    (generic B) (liftSub B σ)
  exact (congrArg (fun e => e ≫ J.inv) (congrArg Iso.hom hP)).trans
    (congrArg (fun e => Q.hom ≫ e) (congrArg Iso.hom h).symm)


theorem lowerEquivalence_reindex {Γ Δ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (E : HomotopyEquivalence (map f)) (σ : Δ ⟶ Γ) :
    lowerEquivalence (f := Functor.whiskerLeft σ.mapElements f) (E.reindex (raisedSub σ)) =
      (lowerEquivalence (f := f) E).reindex σ := by
  apply HomotopyEquivalence.ext
  let C := homotopyFiber (Functor.whiskerLeft (projection (reindex B σ)).mapElements
    (Functor.whiskerLeft σ.mapElements f)) (generic (reindex B σ))
  let c := (E.fibers.reindex (totalIso B).hom).transport (lowerFiberIso f)
  have hL := (lowerEquivalence_fibers (f := Functor.whiskerLeft σ.mapElements f)
    (E.reindex (raisedSub σ))).trans
      (congrArg (lowerContractible (A := C)) (E.fibers.reindex_transport_comp
        (liftSub (family B) (raisedSub σ)) (genericFiberReindexIso (map f) (raisedSub σ))
        (totalIso (reindex B σ)).hom (lowerFiberIso (Functor.whiskerLeft σ.mapElements f))))
  have hR := (congrArg (fun d => (d.reindex (liftSub B σ)).transport (genericFiberReindexIso f σ))
      (lowerEquivalence_fibers E)).trans
    ((congrArg (fun d => d.transport (genericFiberReindexIso f σ))
      (lowerContractible_reindex c (liftSub B σ)).symm).trans
    ((lowerContractible_transport
      (A := reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B))
        (liftSub B σ)) (B := C) (c.reindex (raisedSub (liftSub B σ)))
      (genericFiberReindexIso f σ)).symm.trans
      (congrArg (lowerContractible (A := C)) (E.fibers.reindex_transport_comp
        (totalIso B).hom (lowerFiberIso f) (raisedSub (liftSub B σ))
        (iso (genericFiberReindexIso f σ))))))
  exact hL.trans ((congrArg (fun e => lowerContractible (A := C)
    ((E.fibers.reindex (raisedSub (liftSub B σ) ≫ (totalIso B).hom)).transport e))
      (lowerFiberIso_reindex f σ)).trans hR.symm)

end Raising
namespace SmallUniverse

theorem lowerChartEquivalence_reindex {Γ Θ : Context.{u}} {Ξ : Context.{u+1}}
    (a b : Ξ ⟶ smallFamilyCodes.{u}) (σ : raisedContext Γ ⟶ Ξ)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) (τ : Θ ⟶ Γ) :
    lowerChartEquivalence a b (raisedSub τ ≫ σ) f E =
      (lowerChartEquivalence a b σ f E).reindex τ := by
  have h := E.reindex_comp σ (raisedSub τ)
  exact (congrArg (fun e => Raising.lowerEquivalence
    (f := Functor.whiskerLeft τ.mapElements (lowerChartMap a b σ f)) e) h.symm).trans
      (Raising.lowerEquivalence_reindex (f := lowerChartMap a b σ f) (E.reindex σ) τ)

end SmallUniverse
end SquareKit.Cubical.Presheaf
