import SquareKit.Internal.Cubical.Filling
import SquareKit.Internal.Cubical.Conversion

/-! Generalized transport uses a constant tube precisely on the face where
its family is constant. Empty-face transport has no extra identity law. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def RestrictedConstancy {Γ : Context.{u}} (A : Family (total (interval Γ)))
    (φ : Cofibration Γ) : Prop :=
  reindex A (restrictInclusion (φ.reindex (projection (interval Γ)))) =
    reindex (reindex (reindex A (endpointSub Γ false)) (projection (interval Γ)))
      (restrictInclusion (φ.reindex (projection (interval Γ))))

theorem RestrictedConstancy.reindex {Γ Δ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Cofibration Γ} (h : RestrictedConstancy A φ) (σ : Δ ⟶ Γ) :
    RestrictedConstancy (Presheaf.reindex A (liftSub (interval Γ) σ)) (φ.reindex σ) :=
  congrArg (fun C => Presheaf.reindex C
    (restrictSubstitution (φ.reindex (projection (interval Γ))) (liftSub (interval Γ) σ))) h

private theorem convert_val_heq {Γ : Context.{u}} {A B : Family Γ} (h : A = B)
    (a : Term A) (x : Γ.Elements) : HEq ((a.convert h).val x) (a.val x) := by
  cases h
  rfl

def RestrictedConstancy.tube {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Cofibration Γ} (h : RestrictedConstancy A φ)
    (a : Term (Presheaf.reindex A (endpointSub Γ false))) :
    PartialSection A (φ.reindex (projection (interval Γ))) :=
  PartialSection.ofRestricted (((a.reindex (projection (interval Γ))).reindex
    (restrictInclusion (φ.reindex (projection (interval Γ))))).convert h.symm)

theorem RestrictedConstancy.tube_val {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Cofibration Γ} (h : RestrictedConstancy A φ)
    (a : Term (Presheaf.reindex A (endpointSub Γ false)))
    (x : (total (interval Γ)).Elements) (p : (φ.reindex (projection (interval Γ))).full x) :
    HEq ((h.tube a).val x p) (a.val ((projection (interval Γ)).mapElements.obj x)) :=
  convert_val_heq h.symm _ ((restrictContext (φ.reindex (projection (interval Γ)))).elementsMk
    x.obj ⟨x.val,p⟩)

def RestrictedConstancy.box {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Cofibration Γ} (h : RestrictedConstancy A φ)
    (a : Term (Presheaf.reindex A (endpointSub Γ false))) : OpenBox A φ where
  tube := h.tube a
  base := a
  boundary x p := eq_of_heq (h.tube_val a ((endpointSub Γ false).mapElements.obj x) p)

def Filling.transp {Γ : Context.{u}} {A : Family (total (interval Γ))} (F : Filling A)
    (φ : Cofibration Γ) (h : RestrictedConstancy A φ)
    (a : Term (Presheaf.reindex A (endpointSub Γ false))) :
    Term (Presheaf.reindex A (endpointSub Γ true)) := F.comp (𝟙 _) φ (h.box a)

theorem Filling.transp_on_face {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {F : Filling A} (hF : F.Lawful) (φ : Cofibration Γ) (h : RestrictedConstancy A φ)
    (a : Term (Presheaf.reindex A (endpointSub Γ false))) (x : Γ.Elements) (hx : φ.full x) :
    HEq ((F.transp φ h a).val x) (a.val x) :=
  (heq_of_eq (Filling.comp_boundary hF (𝟙 _) φ (h.box a) x hx)).trans
    (h.tube_val a ((endpointSub Γ true).mapElements.obj x) hx)

theorem RestrictedConstancy.box_reindex {Γ Δ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Cofibration Γ} (h : RestrictedConstancy A φ)
    (a : Term (Presheaf.reindex A (endpointSub Γ false))) (σ : Δ ⟶ Γ) :
    (h.box a).reindex σ = (h.reindex σ).box (a.reindex σ) := by
  apply OpenBox.ext
  · apply PartialSection.ext
    intro x p
    apply eq_of_heq
    exact (h.tube_val a ((liftSub (interval Γ) σ).mapElements.obj x) p).trans
      ((h.reindex σ).tube_val (a.reindex σ) x p).symm
  · rfl

theorem Filling.transp_reindex {Γ Δ : Context.{u}} {A : Family (total (interval Γ))}
    {F : Filling A} (hF : F.Lawful) (φ : Cofibration Γ) (h : RestrictedConstancy A φ)
    (a : Term (Presheaf.reindex A (endpointSub Γ false))) (σ : Δ ⟶ Γ) :
    (F.reindex (liftSub (interval Γ) σ)).transp (φ.reindex σ) (h.reindex σ) (a.reindex σ) =
      (F.transp φ h a).reindex σ := by
  change F.comp (liftSub (interval Γ) σ) (φ.reindex σ) ((h.reindex σ).box (a.reindex σ)) = _
  rw [← h.box_reindex a σ]
  exact Filling.comp_reindex hF (𝟙 _) φ (h.box a) σ

theorem RestrictedConstancy.endpoint_type {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Cofibration Γ} (h : RestrictedConstancy A φ) (x : Γ.Elements) (hx : φ.full x) :
    A.obj ((endpointSub Γ true).mapElements.obj x) = A.obj ((endpointSub Γ false).mapElements.obj x) :=
  congrArg (fun C => C.obj ((restrictContext (φ.reindex (projection (interval Γ)))).elementsMk x.obj
    ⟨((endpointSub Γ true).app x.obj x.val),hx⟩)) h

/-- The full-face result is equality in the actual endpoint fiber, using the
endpoint identification justified by restricted constancy. -/
theorem Filling.transp_computation {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {F : Filling A} (hF : F.Lawful) (φ : Cofibration Γ) (h : RestrictedConstancy A φ)
    (a : Term (Presheaf.reindex A (endpointSub Γ false))) (x : Γ.Elements) (hx : φ.full x) :
    (F.transp φ h a).val x = cast (h.endpoint_type x hx).symm (a.val x) :=
  eq_of_heq ((Filling.transp_on_face hF φ h a x hx).trans (cast_heq _ _).symm)

theorem discreteFamily_constant {Γ : Context.{u}} {T : Type u}
    (q : Term (constantFamily (total (interval Γ)) T)) (S : T → Type u) :
    discreteFamily q S = reindex (reindex (discreteFamily q S) (endpointSub Γ false))
      (projection (interval Γ)) := by
  have hq : q = (q.reindex (endpointSub Γ false)).reindex (projection (interval Γ)) := by
    apply Term.ext
    intro x
    exact (discreteIndex_zero q x).symm
  exact congrArg (fun q => discreteFamily q S) hq

theorem discreteFamily_restrictedConstant {Γ : Context.{u}} {T : Type u}
    (q : Term (constantFamily (total (interval Γ)) T)) (S : T → Type u) (φ : Cofibration Γ) :
    RestrictedConstancy (discreteFamily q S) φ :=
  congrArg (fun A => reindex A (restrictInclusion (φ.reindex (projection (interval Γ)))))
    (discreteFamily_constant q S)

end SquareKit.Cubical.Presheaf
