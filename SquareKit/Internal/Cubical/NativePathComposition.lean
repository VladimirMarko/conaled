import SquareKit.Internal.Cubical.HomotopyRetracts
import SquareKit.Internal.Cubical.PathFillingSubstitution

/-! Substitution and endpoint conventions for native path composition. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

@[simp] theorem homogeneousReindex_refl {Γ Δ : Context.{u}} {A : Family Γ}
    (a : Term A) (σ : Δ ⟶ Γ) :
    homogeneousReindex (homogeneousRefl a) σ = homogeneousRefl (a.reindex σ) := rfl

@[simp] theorem homogeneousReindex_reverse {Γ Δ : Context.{u}} {A : Family Γ}
    {a b : Term A} (p : Term (homogeneousPath A a b)) (σ : Δ ⟶ Γ) :
    homogeneousReindex (homogeneousReverse p) σ =
      homogeneousReverse (homogeneousReindex p σ) := rfl

@[simp] theorem homogeneousReindex_comp {Γ Δ Θ : Context.{u}} {A : Family Γ}
    {a b : Term A} (p : Term (homogeneousPath A a b)) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    homogeneousReindex (homogeneousReindex p σ) τ = homogeneousReindex p (τ ≫ σ) := rfl

@[simp] theorem homogeneousPathMap_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) {a b : Term A} (p : Term (homogeneousPath A a b)) (σ : Δ ⟶ Γ) :
    homogeneousReindex (homogeneousPathMap f p) σ =
      homogeneousPathMap (Functor.whiskerLeft σ.mapElements f) (homogeneousReindex p σ) := rfl

theorem homogeneousPath_cast_app {Γ : Context.{u}} {A : Family Γ}
    {a b c : Term A} (h : b = c) (p : Term (homogeneousPath A a b)) :
    pathApp (Term.map (eqToIso (congrArg (homogeneousPath A a) h)).hom p) = pathApp p := by
  cases h
  rfl

theorem OpenBox.map_empty {Γ : Context.{u}} {A B : Family (total (interval Γ))}
    (f : A ⟶ B) (a : Term (Presheaf.reindex A (endpointSub Γ false))) :
    (OpenBox.empty A a).map f =
      OpenBox.empty B (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements f) a) := by
  apply OpenBox.ext
  · apply PartialSection.ext
    intro x hx
    exact (Bool.false_ne_true hx).elim
  · rfl

theorem IntervalTransport.forward_transport {Γ : Context.{u}}
    {A B : Family (total (interval Γ))} (F : Filling A) (e : A ≅ B)
    (b : Term (reindex B (endpointSub Γ false))) :
    IntervalTransport.forward (F.transport e) (𝟙 Γ) b =
      Term.map e.hom (IntervalTransport.forward F (𝟙 Γ)
        (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements e.inv) b)) := by
  change Term.map e.hom (F.fill (𝟙 _) (Cofibration.bot Γ) ((OpenBox.empty B b).map e.inv)) = _
  exact congrArg (fun t => Term.map e.hom (F.fill (𝟙 _) (Cofibration.bot Γ) t))
    (OpenBox.map_empty e.inv b)

theorem IntervalTransport.forward_transport_map {Γ : Context.{u}}
    {A B : Family (total (interval Γ))} (F : Filling A) (e : A ≅ B)
    (a : Term (reindex A (endpointSub Γ false))) :
    IntervalTransport.forward (F.transport e) (𝟙 Γ)
      (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements e.hom) a) =
      Term.map e.hom (IntervalTransport.forward F (𝟙 Γ) a) :=
  (IntervalTransport.forward_transport F e _).trans
    (congrArg (fun t => Term.map e.hom (IntervalTransport.forward F (𝟙 Γ) t))
      (Term.map_iso_roundtrip (Functor.isoWhiskerLeft (endpointSub Γ false).mapElements e) a))

theorem IntervalTransport.map_transport_section {Γ : Context.{u}}
    {A B : Family (total (interval Γ))} (F : Filling A) (hF : F.Lawful) (e : A ≅ B)
    (b : Term (reindex B (endpointSub Γ false))) :
    Term.map (IntervalTransport.map (F.transport e)) b =
      Term.map (Functor.whiskerLeft (endpointSub Γ true).mapElements e.hom)
        (Term.map (IntervalTransport.map F)
          (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements e.inv) b)) := by
  exact (IntervalTransport.map_section _ (Filling.transport_lawful e F hF) b).trans
    ((congrArg (fun t => t.reindex (endpointSub Γ true)) (IntervalTransport.forward_transport F e b)).trans
      (congrArg (Term.map (Functor.whiskerLeft (endpointSub Γ true).mapElements e.hom))
        (IntervalTransport.map_section F hF
          (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements e.inv) b))).symm)

namespace NativeConcat
variable {Γ : Context.{u}} {A : Family Γ} {a b c : Term A}
    (F : Filling A) (hF : F.Lawful)
    (p : Term (homogeneousPath A a b)) (q : Term (homogeneousPath A b c))

theorem startIso_app (t : Term (reindex (line (a := a) q) (endpointSub Γ false))) :
    pathApp (Term.map (startIso q).hom t) =
      pathApp (Term.map (endpointIso q false).hom t) :=
  homogeneousPath_cast_app (pathApp_zero q) (Term.map (endpointIso q false).hom t)

theorem finishIso_app (t : Term (reindex (line (a := a) q) (endpointSub Γ true))) :
    pathApp (Term.map (finishIso q).hom t) =
      pathApp (Term.map (endpointIso q true).hom t) :=
  homogeneousPath_cast_app (pathApp_one q) (Term.map (endpointIso q true).hom t)

noncomputable def squarePath : Term (line (a := a) q) :=
  IntervalTransport.forward (filling q F hF) (𝟙 Γ) (Term.map (startIso q).inv p)

noncomputable def square := pathApp (squarePath F hF p q)

theorem square_left :
    (square F hF p q).reindex (endpointSub (total (interval Γ)) false) =
      a.reindex (projection (interval Γ)) := pathApp_zero (squarePath F hF p q)

theorem square_right :
    (square F hF p q).reindex (endpointSub (total (interval Γ)) true) = pathApp q :=
  pathApp_one (squarePath F hF p q)

theorem square_zero :
    (square F hF p q).reindex (liftSub (interval (total (interval Γ))) (endpointSub Γ false)) =
      pathApp p := by
  have h := IntervalTransport.forward_zero (filling q F hF)
    (pathFilling_lawful _ (hF.reindex _) _ _) (𝟙 Γ) (Term.map (startIso q).inv p)
  have he := congrArg (fun t => pathApp (Term.map (startIso q).hom t)) h
  exact (startIso_app q _).symm.trans (he.trans (congrArg pathApp (Term.map_iso_roundtrip (startIso q).symm p)))

theorem square_one :
    (square F hF p q).reindex (liftSub (interval (total (interval Γ))) (endpointSub Γ true)) =
      pathApp (homogeneousConcat F hF p q) := by
  have h := IntervalTransport.map_section (filling q F hF)
    (pathFilling_lawful _ (hF.reindex _) _ _) (Term.map (startIso q).inv p)
  exact (finishIso_app q _).symm.trans
    (congrArg (fun t => pathApp (Term.map (finishIso q).hom t)) h).symm

section Substitution
variable {Δ : Context.{u}} (σ : Δ ⟶ Γ)

def lineIso : reindex (line (a := a) q) (liftSub (interval Γ) σ) ≅
    line (a := a.reindex σ) (homogeneousReindex q σ) :=
  pathReindexIso _ _ _ (liftSub (interval Γ) σ)

theorem filling_reindex :
    ((filling q F hF).reindex (liftSub (interval Γ) σ)).transport (lineIso (a := a) q σ) =
      filling (homogeneousReindex q σ) (F.reindex σ) (hF.reindex σ) :=
  pathFilling_reindex_iso
    (F.reindex (projection (interval (total (interval Γ))) ≫ projection (interval Γ)))
    (hF.reindex _) (a.reindex (projection (interval Γ))) (pathApp q)
    (liftSub (interval Γ) σ)

theorem initial_reindex :
    Term.map (Functor.whiskerLeft (endpointSub Δ false).mapElements (lineIso (a := a) q σ).hom)
      ((Term.map (startIso q).inv p).reindex σ) =
    Term.map (startIso (homogeneousReindex q σ)).inv (homogeneousReindex p σ) := by
  apply Term.map_injective_of_iso (startIso (homogeneousReindex q σ))
  apply pathApp_injective
  have h := (startIso_app q (Term.map (startIso q).inv p)).symm.trans
    (congrArg pathApp (Term.map_iso_roundtrip (startIso q).symm p))
  exact (startIso_app (homogeneousReindex q σ) _).trans
    ((congrArg (fun t => t.reindex (liftSub (interval Γ) σ)) h).trans
      (congrArg pathApp (Term.map_iso_roundtrip
        (startIso (homogeneousReindex q σ)).symm (homogeneousReindex p σ))).symm)

theorem squarePath_reindex :
    Term.map (lineIso (a := a) q σ).hom ((squarePath F hF p q).reindex (liftSub (interval Γ) σ)) =
      squarePath (F.reindex σ) (hF.reindex σ) (homogeneousReindex p σ) (homogeneousReindex q σ) := by
  let L := liftSub (interval Γ) σ
  let e := lineIso (a := a) q σ
  let t := Term.map (startIso q).inv p
  have hi := initial_reindex p q σ
  have hf := filling_reindex (a := a) F hF q σ
  have hs := congrArg (fun K => IntervalTransport.forward K (𝟙 Δ)
    (Term.map (startIso (homogeneousReindex q σ)).inv (homogeneousReindex p σ))) hf.symm
  have ht := congrArg (IntervalTransport.forward (((filling q F hF).reindex L).transport e) (𝟙 Δ)) hi.symm
  have hu := IntervalTransport.forward_transport_map ((filling q F hF).reindex L) e (t.reindex σ)
  have hn := IntervalTransport.forward_reindex (filling q F hF)
    (pathFilling_lawful _ (hF.reindex _) _ _) (𝟙 Γ) t σ
  exact (hs.trans (ht.trans (hu.trans (congrArg (Term.map e.hom) hn)))).symm

end Substitution

end NativeConcat
/-- Substitution preserves the entire selected concatenated native path. -/
theorem homogeneousConcat_reindex {Γ Δ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) {a b c : Term A}
    (p : Term (homogeneousPath A a b)) (q : Term (homogeneousPath A b c)) (σ : Δ ⟶ Γ) :
    homogeneousReindex (homogeneousConcat F hF p q) σ =
      homogeneousConcat (F.reindex σ) (hF.reindex σ)
        (homogeneousReindex p σ) (homogeneousReindex q σ) := by
  apply pathApp_injective
  have hs := congrArg pathApp (NativeConcat.squarePath_reindex F hF p q σ)
  have he := congrArg (fun t => t.reindex
    (liftSub (interval (total (interval Δ))) (endpointSub Δ true))) hs
  exact (congrArg (fun t => t.reindex (liftSub (interval Γ) σ))
    (NativeConcat.square_one F hF p q)).symm.trans
      (he.trans (NativeConcat.square_one (F.reindex σ) (hF.reindex σ)
        (homogeneousReindex p σ) (homogeneousReindex q σ)))

end SquareKit.Cubical.Presheaf
