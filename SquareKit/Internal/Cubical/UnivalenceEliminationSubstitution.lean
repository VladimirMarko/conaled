import SquareKit.Internal.Cubical.GlueEliminationSubstitution
import SquareKit.Internal.Cubical.UnivalenceSubstitution

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.Univalence
open CategoryTheory
universe u

private theorem cast_chain {Γ : Context.{u}} {A B C D : Family Γ}
    (h : A = B) (k : B = C) (r : A = C) (f : C ⟶ D) :
    eqToHom h ≫ eqToHom k ≫ f = eqToHom r ≫ f := by
  cases h
  cases k
  rfl

theorem unglueLine_reindex {Γ Δ : Context.{u}}
    (a b : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (f : decode a ⟶ decode b) (H : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    Functor.whiskerLeft (liftSub (interval Γ) σ).mapElements (unglueLine a b f H) =
      eqToHom (congrArg decode (uaCode_reindex a b σ f H)) ≫
        unglueLine (raisedSub σ ≫ a) (raisedSub σ ≫ b)
          (Functor.whiskerLeft σ.mapElements f) (H.reindex σ) := by
  let τ := liftSub (interval Γ) σ
  let ρ := restrictSubstitution face τ
  let a' := raisedSub σ ≫ a
  let b' := raisedSub σ ≫ b
  let f' := Functor.whiskerLeft σ.mapElements f
  let t := raisedSub ρ ≫ CodeSystem.boundary a b
  let t' := CodeSystem.boundary a' b'
  let e := Functor.whiskerLeft ρ.mapElements (boundaryMap a b f)
  let e' := boundaryMap a' b' f'
  let E := (boundaryEquivalence a b f H).reindex ρ
  let E' := boundaryEquivalence a' b' f' (H.reindex σ)
  have ht : t = t' := boundary_reindex a b σ
  have he : HEq e e' := boundaryMap_reindex a b σ f
  have hE : HEq E E' := boundaryEquivalence_reindex a b σ f H
  let h₀ := Glue.code_substitution face (ambient b) (CodeSystem.boundary a b)
    (boundaryMap a b f) (boundaryEquivalence a b f H) τ
  let h₁ := Glue.code_congr face (ambient b') t t' ht e e' he E E' hE
  have hg := Glue.codeUnglue_substitution face (ambient b) (CodeSystem.boundary a b)
    (boundaryMap a b f) (boundaryEquivalence a b f H) τ
  have hc := Glue.codeUnglue_congr face (ambient b') t t' ht e e' he E E' hE
  exact hg.trans ((congrArg (fun k => eqToHom (congrArg decode h₀) ≫ k) hc).trans
    (cast_chain (congrArg decode h₀) (congrArg decode h₁)
      (congrArg decode (uaCode_reindex a b σ f H)) (unglueLine a' b' f' (H.reindex σ))))

end SquareKit.Cubical.Presheaf.Univalence
