import SquareKit.Internal.Cubical.NativePathSingleton
import SquareKit.Internal.Cubical.NativeUnivalenceComparison
import SquareKit.Internal.Cubical.NativeUnivalenceSectionBeta
import SquareKit.Internal.Cubical.EquivalenceFamilyReindex

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Γ Δ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})

private theorem pathPair_congr {a b : Δ ⟶ smallFamilyCodes.{u}}
    {p q : Term (paths a b)} (h : p = q) :
    (⟨pathToMap p,pathToEquivalence p⟩ : Σ f, HomotopyEquivalence f) =
      ⟨pathToMap q,pathToEquivalence q⟩ := by
  cases h
  rfl

/-- The supplied equivalence comparison, transported back through the faithful
native family isomorphism, retains the complete original section. -/
noncomputable def encodedRoundtripAt (σ : Δ ⟶ Γ)
    (s : Term (reindex (equivalences a b) σ)) :
    let S := EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ
    let e := S.symm s
    let q := ua (σ ≫ a) (σ ≫ b) e.1 e.2
    Term (homogeneousPath (reindex (equivalences a b) σ)
      (S ⟨pathToMap q,pathToEquivalence q⟩) s) := by
  let S := EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ
  let J := EquivalenceFamilies.equivReindexIso (liftedDecode a) (liftedDecode b) σ
  let e := S.symm s
  let q := ua (σ ≫ a) (σ ≫ b) e.1 e.2
  let c := Term.map (NativePathSingleton.reverseIso _ _).hom
    (uaEquivalenceComparison (σ ≫ a) (σ ≫ b) e.1 e.2)
  let r := homogeneousPathMap J.inv c
  exact pathLam (pathApp r)
    ((pathApp_zero r).trans
      (EquivalenceFamilies.equivReindexIso_inv_encode (liftedDecode a) (liftedDecode b) σ
        (pathToMap q) (pathToEquivalence q)))
    ((pathApp_one r).trans
      ((EquivalenceFamilies.equivReindexIso_inv_encode (liftedDecode a) (liftedDecode b) σ
        e.1 e.2).trans (S.apply_symm_apply s)))

/-- The actual native reverse map is a right inverse through a path retaining the
complete selected internal equivalence, in every substituted context. -/
noncomputable def rightInverseAt (σ : Δ ⟶ Γ)
    (s : Term (reindex (equivalences a b) σ)) :
    Term (homogeneousPath (reindex (equivalences a b) σ)
      (Term.map (Functor.whiskerLeft σ.mapElements (pathToEquiv a b))
        (Term.map (Functor.whiskerLeft σ.mapElements (equivToPath a b)) s)) s) := by
  let S := EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ
  let e := S.symm s
  let p := Term.map (Functor.whiskerLeft σ.mapElements (equivToPath a b)) s
  let t := Term.map (Functor.whiskerLeft σ.mapElements (pathToEquiv a b)) p
  let q := ua (σ ≫ a) (σ ≫ b) e.1 e.2
  have hp := equivToPath_reindex_beta (a := a) (b := b) σ s
  have ht : t = S ⟨pathToMap q,pathToEquivalence q⟩ :=
    (pathToEquiv_reindex_beta (a := a) (b := b) σ p).trans
      (congrArg S (pathPair_congr hp))
  let r := encodedRoundtripAt a b σ s
  exact pathLam (pathApp r) ((pathApp_zero r).trans ht.symm) (pathApp_one r)

noncomputable def rightInverseHomotopy :=
  rightInverseAt a b (projection (equivalences a b)) (generic (equivalences a b))

end SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
