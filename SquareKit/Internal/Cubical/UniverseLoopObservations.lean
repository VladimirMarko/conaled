import SquareKit.Internal.Cubical.NativeUnivalence
import SquareKit.Internal.Cubical.NativeUnivalenceSectionBeta

/-! Native two-paths preserve transport observations. Recovery retains the
original universe path through the native univalence round trip. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Γ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})

/-- Evaluate the transport of a variable universe path at a fixed input. -/
noncomputable def transportEvaluation (x : Term (liftedDecode a)) :
    paths a b ⟶ liftedDecode b :=
  EquivalenceFamilies.decodeMap (lam
    (Term.map (pathToMap (genericPath a b)) (x.reindex (projection (paths a b)))))

theorem transportEvaluation_beta (x : Term (liftedDecode a)) (p : Term (paths a b)) :
    Term.map (transportEvaluation a b x) p = Term.map (pathToMap p) x := by
  have h := congrArg Sigma.fst (pathEquivalence_generic p)
  exact (EquivalenceFamilies.decodeMap_lam_apply _ p).trans
    (congrArg (fun k => Term.map k x) h)

/-- A native path between universe paths gives a native path between their
actual transported outputs. No reflection to host equality is assumed. -/
noncomputable def transportTwoPath {p q : Term (paths a b)}
    (h : Term (homogeneousPath (paths a b) p q)) (x : Term (liftedDecode a)) :
    Term (homogeneousPath (liftedDecode b)
      (Term.map (pathToMap p) x) (Term.map (pathToMap q) x)) := by
  let r := homogeneousPathMap (transportEvaluation a b x) h
  exact pathLam (pathApp r)
    ((pathApp_zero r).trans (transportEvaluation_beta a b x p))
    ((pathApp_one r).trans (transportEvaluation_beta a b x q))

/-- Only a supplied observation into constant coefficients is reflected to Eq. -/
theorem twoPath_discrete_observation {S : Type (u+1)}
    (o : liftedDecode b ⟶ constantFamily Γ S) {p q : Term (paths a b)}
    (h : Term (homogeneousPath (paths a b) p q)) (x : Term (liftedDecode a)) :
    Term.map o (Term.map (pathToMap p) x) = Term.map o (Term.map (pathToMap q) x) :=
  discretePath_endpoints (homogeneousPathMap o (transportTwoPath a b h x))

noncomputable def recoverLoop (p : Term (paths a a)) :=
  Term.map (equivToPath a a) (Term.map (pathToEquiv a a) p)

noncomputable def recoverLoop_path (p : Term (paths a a)) :
    Term (homogeneousPath (paths a a) (recoverLoop a p) p) := leftInverseAt a a p

theorem recoverLoop_eq_ua (p : Term (paths a a)) :
    recoverLoop a p = ua a a (pathToMap p) (pathToEquivalence p) :=
  (congrArg (Term.map (equivToPath a a)) (pathToEquiv_beta p).symm).trans
    (equivToPath_beta (pathToMap p) (pathToEquivalence p))

private theorem ua_data_congr {Δ : Context.{u+1}} (c d : Δ ⟶ smallFamilyCodes.{u})
    (v w : Σ f : liftedDecode c ⟶ liftedDecode d, HomotopyEquivalence f)
    (h : v = w) : ua c d v.1 v.2 = ua c d w.1 w.2 := by
  cases h
  rfl

/-- Recomputing the recovered loop after substitution retains the selected
transport map and its complete contractible-fiber witness. -/
theorem recoverLoop_reindex {Δ : Context.{u+1}} (p : Term (paths a a)) (σ : Δ ⟶ Γ) :
    reindexPath (recoverLoop a p) σ = recoverLoop (σ ≫ a) (reindexPath p σ) := by
  have hd : (⟨Functor.whiskerLeft σ.mapElements (pathToMap p),
      (pathToEquivalence p).reindex σ⟩ :
      Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ a), HomotopyEquivalence f) =
      ⟨pathToMap (reindexPath p σ), pathToEquivalence (reindexPath p σ)⟩ :=
    Sigma.ext (pathToMap_reindex p σ) (pathToEquivalence_reindex p σ)
  exact (congrArg (fun q => reindexPath q σ) (recoverLoop_eq_ua a p)).trans
    ((ua_reindex a a (pathToMap p) (pathToEquivalence p) σ).trans
      ((ua_data_congr (σ ≫ a) (σ ≫ a) _ _ hd).trans
        (recoverLoop_eq_ua (σ ≫ a) (reindexPath p σ)).symm))

/-- Restrict the whole recovery witness and normalize both endpoints. This
constructs the parameterized witness; it does not identify it with a separately
recomputed choice of leftInverseAt. -/
noncomputable def recoverLoop_path_reindex {Δ : Context.{u+1}}
    (p : Term (paths a a)) (σ : Δ ⟶ Γ) :
    Term (homogeneousPath (paths (σ ≫ a) (σ ≫ a))
      (recoverLoop (σ ≫ a) (reindexPath p σ)) (reindexPath p σ)) := by
  let r := homogeneousPathMap
    (pathReindex (reindex (family Γ) (projection (interval Γ))) (term a) (term a) σ)
    (homogeneousReindex (recoverLoop_path a p) σ)
  exact pathLam (pathApp r) ((pathApp_zero r).trans (recoverLoop_reindex a p σ)) (pathApp_one r)

end SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
