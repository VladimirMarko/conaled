import SquareKit.Internal.Cubical.ScaledBox

/-! A composition operation supplies whole fillers through the De Morgan
connection and the added zero face. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

noncomputable def Composition.fill {Γ Δ : Context.{u}} {A : Family Γ} (C : Composition A)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ) (b : OpenBox (reindex A p) φ) :
    Term (reindex A p) :=
  (C.comp (scaleInterval Δ ≫ p) (scaledFace φ) (scaledBox b)).convert
    (congrArg (fun q => reindex A (q ≫ p)) (scaleInterval_one Δ))

theorem Composition.fill_val_heq {Γ Δ : Context.{u}} {A : Family Γ} (C : Composition A)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ) (b : OpenBox (reindex A p) φ)
    (x : (total (interval Δ)).Elements) :
    HEq ((C.fill p φ b).val x)
      ((C.comp (scaleInterval Δ ≫ p) (scaledFace φ) (scaledBox b)).val x) :=
  Term.convert_val_heq _ _ x

theorem Composition.fill_fills {Γ Δ : Context.{u}} {A : Family Γ} {C : Composition A}
    (h : C.Lawful) (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex A p) φ) : b.Fills (C.fill p φ b) := by
  constructor
  · apply Term.ext
    intro x
    let y := (endpointSub Δ false).mapElements.obj x
    have hz : (intervalFace Δ false).full y :=
      (Cofibration.full_endpoint (generic (interval Δ)) false y).mpr rfl
    have hf : (scaledFace φ).full y := (Cofibration.full_join _ _ y).mpr (Or.inr hz)
    have hc := h.boundary (scaleInterval Δ ≫ p) (scaledFace φ) (scaledBox b) y hf
    have hv := glueValue_right (b.tube.reindex (scaleInterval Δ)) (scaledZeroSection b.base)
      (fun z hp hk => b.endpoint_compatible ((scaleInterval Δ).mapElements.obj z) hp
        (scaleInterval_outer_zero z hk))
      ((endpointSub (total (interval Δ)) true).mapElements.obj y) hf hz
    apply eq_of_heq
    exact (C.fill_val_heq p φ b y).trans ((heq_of_eq (hc.trans hv)).trans
      (endpointSection_val (reindex A p) false b.base _ _))
  · intro x hx
    have hf : (scaledFace φ).full x := (Cofibration.full_join _ _ x).mpr (Or.inl hx)
    have hc := h.boundary (scaleInterval Δ ≫ p) (scaledFace φ) (scaledBox b) x hf
    have hv := glueValue_left (b.tube.reindex (scaleInterval Δ)) (scaledZeroSection b.base)
      ((endpointSub (total (interval Δ)) true).mapElements.obj x) hf hx
    apply eq_of_heq
    apply (C.fill_val_heq p φ b x).trans ((heq_of_eq (hc.trans hv)).trans ?_)
    have he : (scaleInterval Δ).mapElements.obj
        ((endpointSub (total (interval Δ)) true).mapElements.obj x) = x :=
      congrArg (fun q => q.mapElements.obj x) (scaleInterval_one Δ)
    exact b.tube.val_heq he _ hx

theorem Composition.fill_reindex {Γ Δ Θ : Context.{u}} {A : Family Γ} {C : Composition A}
    (h : C.Lawful) (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex A p) φ) (σ : Θ ⟶ Δ) :
    C.fill (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ) =
      (C.fill p φ b).reindex (liftSub (interval Δ) σ) := by
  have hu := h.uniform (scaleInterval Δ ≫ p) (scaledFace φ) (scaledBox b)
    (liftSub (interval Δ) σ)
  have hc := congrArg
    (fun box => C.comp (scaleInterval Θ ≫ (liftSub (interval Δ) σ ≫ p))
      (scaledFace (φ.reindex σ)) box) (scaledBox_reindex b σ)
  have ht := hc.symm.trans hu
  apply Term.ext
  intro x
  apply eq_of_heq
  exact (C.fill_val_heq (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ) x).trans
    ((heq_of_eq (congrArg (fun t => t.val x) ht)).trans
      (C.fill_val_heq p φ b ((liftSub (interval Δ) σ).mapElements.obj x)).symm)

noncomputable def Composition.toFilling {Γ : Context.{u}} {A : Family Γ}
    (C : Composition A) : Filling A where
  fill := C.fill

theorem Composition.toFilling_lawful {Γ : Context.{u}} {A : Family Γ} {C : Composition A}
    (h : C.Lawful) : C.toFilling.Lawful where
  fills := Composition.fill_fills h
  uniform := Composition.fill_reindex h

end SquareKit.Cubical.Presheaf
