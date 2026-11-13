import SquareKit.Internal.Cubical.NativeUnivalenceSectionBeta
import SquareKit.Internal.Cubical.EquivalenceFamilyReindex

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u

private def nativePathIso {Γ Δ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})
    (σ : Δ ⟶ Γ) : reindex (paths a b) σ ≅ paths (σ ≫ a) (σ ≫ b) :=
  pathReindexIso (reindex (family Γ) (projection (interval Γ))) (term a) (term b) σ

private noncomputable def pathData {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
    (p : Term (paths a b)) : Σ f : liftedDecode a ⟶ liftedDecode b, HomotopyEquivalence f :=
  ⟨pathToMap p, pathToEquivalence p⟩

private theorem conjugate_sections {Γ Δ Θ : Context.{u+1}}
    (a b : Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (p : Term (reindex (paths (σ ≫ a) (σ ≫ b)) τ)) :
    Term.map
      (Functor.whiskerLeft τ.mapElements (nativePathIso a b σ).inv ≫
        Functor.whiskerLeft (τ ≫ σ).mapElements (pathToEquiv a b) ≫
        Functor.whiskerLeft τ.mapElements
          (EquivalenceFamilies.equivReindexIso (liftedDecode a) (liftedDecode b) σ).hom) p =
      Term.map (Functor.whiskerLeft τ.mapElements (pathToEquiv (σ ≫ a) (σ ≫ b))) p := by
  let Jp := nativePathIso a b σ
  let q := Term.map (Functor.whiskerLeft τ.mapElements Jp.inv) p
  let r : Term (paths ((τ ≫ σ) ≫ a) ((τ ≫ σ) ≫ b)) :=
    Term.map (nativePathIso a b (τ ≫ σ)).hom q
  let r' : Term (paths (τ ≫ σ ≫ a) (τ ≫ σ ≫ b)) :=
    Term.map (nativePathIso (σ ≫ a) (σ ≫ b) τ).hom p
  have hp : r = r' :=
    congrArg (Term.map (nativePathIso (σ ≫ a) (σ ≫ b) τ).hom)
      (Term.map_iso_roundtrip (Functor.isoWhiskerLeft τ.mapElements Jp).symm p)
  let old := Term.map (Functor.whiskerLeft (τ ≫ σ).mapElements (pathToEquiv a b)) q
  let S := EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) (τ ≫ σ)
  let T := EquivalenceFamilies.equivReindexSections
    (liftedDecode (σ ≫ a)) (liftedDecode (σ ≫ b)) τ
  have hβ : old = S (pathData r) := pathToEquiv_reindex_beta (τ ≫ σ) q
  have hdata : S.symm old = pathData r :=
    (congrArg S.symm hβ).trans (S.symm_apply_apply (pathData r))
  have hJ := EquivalenceFamilies.equivReindexIso_hom_reindex_sections
    (liftedDecode a) (liftedDecode b) σ τ old
  have hpath : pathData r = pathData r' :=
    @congrArg (Term (paths (τ ≫ σ ≫ a) (τ ≫ σ ≫ b)))
      (Σ f : liftedDecode (τ ≫ σ ≫ a) ⟶ liftedDecode (τ ≫ σ ≫ b), HomotopyEquivalence f)
      r r' pathData hp
  have hnew : Term.map (Functor.whiskerLeft τ.mapElements
      (pathToEquiv (σ ≫ a) (σ ≫ b))) p = T (pathData r') :=
    pathToEquiv_reindex_beta τ p
  exact hJ.trans ((congrArg T hdata).trans ((congrArg T hpath).trans hnew.symm))

/-- The forward native univalence map commutes with substitution through the
actual path and complete-equivalence presentation isomorphisms. -/
theorem pathToEquiv_conjugate_reindex {Γ Δ : Context.{u+1}}
    (a b : Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) :
    (pathReindexIso (reindex (family Γ) (projection (interval Γ)))
      (term a) (term b) σ).inv ≫
      Functor.whiskerLeft σ.mapElements (pathToEquiv a b) ≫
      (EquivalenceFamilies.equivReindexIso (liftedDecode a) (liftedDecode b) σ).hom =
      pathToEquiv (σ ≫ a) (σ ≫ b) := by
  let C := paths (σ ≫ a) (σ ≫ b)
  have h := conjugate_sections a b σ (projection C) (generic C)
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro p
  exact congrArg (fun t => t.val (extendObj C x p)) h

end SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
