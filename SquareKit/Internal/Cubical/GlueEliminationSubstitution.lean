import SquareKit.Internal.Cubical.UnivalenceTransport

/-! Substitution of the actual elimination map of supplied Glue codes. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.Glue
open CategoryTheory
universe u

noncomputable def Datum.smallUnglue {Γ : Context.{u}} (D : Datum Γ) :
    D.smallFamily ⟶ D.ambient :=
  D.smallFamilyIso.hom ≫ compatibleUnglue D.face D.ambient D.faceFamily D.map

theorem Datum.smallUnglue_substitution {Γ Δ : Context.{u}} (D : Datum Γ)
    (σ : Δ ⟶ Γ) :
    Functor.whiskerLeft σ.mapElements D.smallUnglue =
      eqToHom (D.smallFamily_substitution σ) ≫ (D.reindex σ).smallUnglue := by
  ext x z
  let w := (eqToHom (D.smallFamily_substitution σ)).app x z
  let s := D.smallFiberEquiv (σ.mapElements.obj x) z
  have hw : HEq z w := (family_eqToIso_hom_heq (D.smallFamily_substitution σ) x z).symm
  have ht := D.smallToLocal_substitution σ x s
  have hz : HEq z (((D.reindex σ).smallFiberEquiv x).symm
      ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x s)) :=
    (heq_of_eq ((D.smallFiberEquiv (σ.mapElements.obj x)).symm_apply_apply z).symm).trans ht
  have he := eq_of_heq (hw.symm.trans hz)
  change s.ambient = ((D.reindex σ).smallFiberEquiv x w).ambient
  rw [he]
  exact (congrArg (fun q : (D.reindex σ).compatible.obj x => q.ambient)
    (((D.reindex σ).smallFiberEquiv x).apply_symm_apply
      ((compatibleReindexMap D.face D.ambient D.faceFamily D.map σ).app x s))).symm

private theorem whisker_cast {Γ Δ : Context.{u}} {A B : Family Γ}
    (h : A = B) (σ : Δ ⟶ Γ) :
    Functor.whiskerLeft σ.mapElements (eqToHom h) =
      eqToHom (congrArg (fun X => reindex X σ) h) := by
  cases h
  rfl

private theorem cast_square {Ξ : Context.{u}} {A B C D X : Family Ξ}
    (h : A = B) (k : B = C) (p : A = D) (q : D = C) (f : C ⟶ X) :
    eqToHom h ≫ eqToHom k ≫ f = eqToHom p ≫ eqToHom q ≫ f := by
  cases h
  cases k
  cases p
  rfl

theorem codeUnglue_substitution {Γ Δ : Context.{u}} (φ : Cofibration Γ)
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (t : raisedContext (restrictContext φ) ⟶ smallFamilyCodes.{u})
    (e : decode t ⟶ reindex (decode a) (restrictInclusion φ))
    (E : HomotopyEquivalence e) (σ : Δ ⟶ Γ) :
    Functor.whiskerLeft σ.mapElements (codeUnglue φ a t e E) =
      eqToHom (congrArg decode (code_substitution φ a t e E σ)) ≫
        codeUnglue (φ.reindex σ) (raisedSub σ ≫ a)
          (raisedSub (restrictSubstitution φ σ) ≫ t)
          (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)
          (E.reindex (restrictSubstitution φ σ)) := by
  let D := Datum.mk φ (decode a) (decode t) e
  let h₀ := LocalFamily.decodeCode_family_eq
    (LocalFamily.normalizedGlue φ (decodedLocalFamily a) (decodedLocalFamily t) e E)
  let h₁ := LocalFamily.decodeCode_family_eq
    (LocalFamily.normalizedGlue (φ.reindex σ) (decodedLocalFamily (raisedSub σ ≫ a))
      (decodedLocalFamily (raisedSub (restrictSubstitution φ σ) ≫ t))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)
      (E.reindex (restrictSubstitution φ σ)))
  change Functor.whiskerLeft σ.mapElements (eqToHom h₀) ≫
      Functor.whiskerLeft σ.mapElements D.smallUnglue =
    eqToHom _ ≫ eqToHom h₁ ≫ (D.reindex σ).smallUnglue
  rw [whisker_cast]
  refine (congrArg (fun k => eqToHom (congrArg (fun X => reindex X σ) h₀) ≫ k)
    (D.smallUnglue_substitution σ)).trans ?_
  exact cast_square (congrArg (fun X => reindex X σ) h₀)
    (D.smallFamily_substitution σ)
    (congrArg decode (code_substitution φ a t e E σ)) h₁ (D.reindex σ).smallUnglue

end SquareKit.Cubical.Presheaf.Glue
