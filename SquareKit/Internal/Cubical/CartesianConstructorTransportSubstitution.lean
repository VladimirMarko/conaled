import SquareKit.Internal.Cubical.CartesianConstructorTransport
import SquareKit.Internal.Cubical.CartesianLargeFamilyFillingRecovery

/-! Whole-section substitution and retained comparisons for freshly rebuilt
Cartesian constructors. The fixed Sigma and Pi constructions preserve their
complete selected comparison bodies across independent rebuilding. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

/-- Rebuilding the function filler over a changed family retains its native
argument and dependent-output algorithm through the full Pi adapter. -/
theorem FunctionFilling.fill_input_reindex {Γ Δ E : Context.{u}}
    {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B)
    (σ : E ⟶ Γ) (p : total (interval Δ) ⟶ E) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (pi A B) (p ≫ σ)) φ r) :
    fill (F.reindex σ) (hF.reindex σ) (G.reindex (liftSub A σ)) p φ r
        (b.map (Functor.whiskerLeft p.mapElements (piReindex A B σ))) =
      Term.map (Functor.whiskerLeft p.mapElements (piReindex A B σ))
        (fill F hF G (p ≫ σ) φ r b) := by
  apply Term.map_injective_of_iso (piReindexIso (reindex A σ) (reindex B (liftSub A σ)) p)
  exact (fill_normalize _ _ _ _ _ _ _).trans (fill_normalize F hF G (p ≫ σ) φ r b).symm

namespace SmallUniverse.LargeConstructors
variable {Ξ Ω : Context.{u+1}}

/-- A restricted result keeps the very comparison chosen before substitution. -/
theorem Result.transportComparison_body_reindex {C : Family (total (interval Ξ))}
    (R : Result C) (r s : Term (interval Ξ)) (z : Term C) (σ : Ω ⟶ Ξ) :
    pathApp ((R.reindex (intervalSub σ)).transportComparison
      (Term.reindex r σ) (Term.reindex s σ) (Term.reindex z (intervalSub σ))) =
      Term.reindex (pathApp (R.transportComparison r s z)) (intervalSub σ) :=
  IntervalTransport.prescribedLineComparison_body_reindex (NativeDecode.filling R.code)
    (NativeDecode.filling_lawful R.code) r s
    (Term.map (Functor.whiskerLeft (graph r).mapElements R.decoding.inv) (Term.reindex z (graph r)))
    (Term.map R.decoding.inv z) rfl σ

set_option backward.isDefEq.respectTransparency false in
theorem Result.comparisonInFamily_body_reindex {C : Family (total (interval Ξ))}
    (R : Result C) (r s : Term (interval Ξ)) (z : Term C) (σ : Ω ⟶ Ξ) :
    pathApp ((R.reindex (intervalSub σ)).comparisonInFamily
      (Term.reindex r σ) (Term.reindex s σ) (Term.reindex z (intervalSub σ))) =
      Term.reindex (pathApp (R.comparisonInFamily r s z)) (intervalSub σ) := by
  rw [Result.comparisonInFamily_body, Result.comparisonInFamily_body]
  have he := congrArg (Term.map (Functor.whiskerLeft (projection (interval Ω)).mapElements
    (Functor.whiskerLeft (graph (Term.reindex s σ)).mapElements
      (R.reindex (intervalSub σ)).decoding.hom))) (R.transportComparison_body_reindex r s z σ)
  exact he.trans (Term.map_reindex (Functor.whiskerLeft (projection (interval Ξ)).mapElements
    (Functor.whiskerLeft (graph s).mapElements R.decoding.hom))
    (pathApp (R.transportComparison r s z)) (intervalSub σ))

set_option maxHeartbeats 400000 in
theorem pairSection_reindex
    (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) (r : Term (interval Ξ))
    (z : Term (reindex (Cartesian.sigma (liftedDecode a) (liftedDecode b)) (graph r)))
    (σ : Ω ⟶ Ξ) :
    pairSection (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)
        (Term.reindex r σ) (Term.reindex z σ) =
      Term.reindex (pairSection a b r z) (intervalSub σ) :=
  IntervalTransport.line_reindex (sigmaFilling (NativeDecode.filling a)
    (NativeDecode.filling_lawful a) (NativeDecode.filling b))
    (sigmaFilling_lawful _ (NativeDecode.filling_lawful a) _ (NativeDecode.filling_lawful b))
    r (𝟙 Ξ) z σ

def functionInitialReindex
    (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) (r : Term (interval Ξ))
    (z : Term (reindex (Cartesian.pi (liftedDecode a) (liftedDecode b)) (graph r)))
    (σ : Ω ⟶ Ξ) :=
  Term.map (Functor.whiskerLeft (graph (Term.reindex r σ)).mapElements
    (piReindexIso (liftedDecode a) (liftedDecode b) (intervalSub σ)).hom) (Term.reindex z σ)

set_option backward.isDefEq.respectTransparency false in
theorem functionSection_reindex
    (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) (r : Term (interval Ξ))
    (z : Term (reindex (Cartesian.pi (liftedDecode a) (liftedDecode b)) (graph r)))
    (σ : Ω ⟶ Ξ) :
    functionSection (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)
        (Term.reindex r σ) (functionInitialReindex a b r z σ) =
      Term.map (piReindexIso (liftedDecode a) (liftedDecode b) (intervalSub σ)).hom
        (Term.reindex (functionSection a b r z) (intervalSub σ)) := by
  have hi := FunctionFilling.fill_input_reindex (NativeDecode.filling a)
    (NativeDecode.filling_lawful a) (NativeDecode.filling b) (intervalSub σ)
    (𝟙 _) Subcontext.bot (Term.reindex r σ)
    (IntervalTransport.emptyBox (Term.reindex r σ) (Term.reindex z σ))
  rw [OpenBox.map_emptyBox] at hi
  have hu := FunctionFilling.fill_uniform (NativeDecode.filling a)
    (NativeDecode.filling_lawful a) (NativeDecode.filling b) (NativeDecode.filling_lawful b)
    (𝟙 _) Subcontext.bot r (IntervalTransport.emptyBox r z) σ
  exact hi.trans (congrArg (Term.map
    (piReindexIso (liftedDecode a) (liftedDecode b) (intervalSub σ)).hom) hu)

/-- Map the complete freshly selected comparison into the original family. -/
noncomputable def Result.rebuiltComparison {C D : Family (total (interval Ξ))}
    (R : Result D) (e : C ≅ D) (r s : Term (interval Ξ))
    (z : Term C) (w : Term D) (hw : Term.map e.hom z = w) :
    Term (homogeneousPath (Cartesian.reindex C (graph s))
      (Term.map (Functor.whiskerLeft (graph s).mapElements e.inv)
        (R.transportInFamily r s (Term.reindex w (graph r)))) (Term.reindex z (graph s))) := by
  let q := homogeneousPathMap (Functor.whiskerLeft (graph s).mapElements e.inv)
    (R.comparisonInFamily r s w)
  have h : Term.map e.inv w = z := hw.symm ▸ Term.map_iso_roundtrip e z
  exact pathLam (pathApp q) (pathApp_zero q)
    ((pathApp_one q).trans (congrArg (fun t => Term.reindex t (graph s)) h))

/-- The two transports compare through the reconstructed section. Both selected
bodies occur in the resulting concatenation, without asserting their equality. -/
noncomputable def Result.compareRebuilt {C D : Family (total (interval Ξ))}
    (R : Result C) (S : Result D) (e : C ≅ D) (r s : Term (interval Ξ))
    (z : Term C) (w : Term D) (hw : Term.map e.hom z = w) :
    Term (homogeneousPath (Cartesian.reindex C (graph s))
      (R.transportInFamily r s (Term.reindex z (graph r)))
      (Term.map (Functor.whiskerLeft (graph s).mapElements e.inv)
        (S.transportInFamily r s (Term.reindex w (graph r))))) :=
  let F := (R.filling.transport R.decoding).reindex (graph s)
  let hF := (Filling.transport_lawful R.decoding R.filling R.lawful).reindex (graph s)
  homogeneousConcat F hF (R.comparisonInFamily r s z)
    (homogeneousReverse F hF (S.rebuiltComparison e r s z w hw))

noncomputable def pairRecomputedComparison
    (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Ξ))
    (z : Term (reindex (Cartesian.sigma (liftedDecode a) (liftedDecode b)) (graph r)))
    (σ : Ω ⟶ Ξ) :=
  ((sigma a b).reindex (intervalSub σ)).compareRebuilt
    (sigma (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)) (Iso.refl _)
    (Term.reindex r σ) (Term.reindex s σ) (Term.reindex (pairSection a b r z) (intervalSub σ))
    (pairSection (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)
      (Term.reindex r σ) (Term.reindex z σ)) (pairSection_reindex a b r z σ).symm

noncomputable def functionRecomputedComparison
    (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Ξ))
    (z : Term (reindex (Cartesian.pi (liftedDecode a) (liftedDecode b)) (graph r)))
    (σ : Ω ⟶ Ξ) :=
  ((pi a b).reindex (intervalSub σ)).compareRebuilt
    (pi (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b))
    (piReindexIso (liftedDecode a) (liftedDecode b) (intervalSub σ))
    (Term.reindex r σ) (Term.reindex s σ) (Term.reindex (functionSection a b r z) (intervalSub σ))
    (functionSection (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)
      (Term.reindex r σ) (functionInitialReindex a b r z σ)) (functionSection_reindex a b r z σ).symm

set_option backward.isDefEq.respectTransparency false in
/-- The target adapter retains the complete freshly selected body. -/
theorem Result.rebuiltComparison_body {C D : Family (total (interval Ξ))}
    (S : Result D) (e : C ≅ D) (r s : Term (interval Ξ))
    (z : Term C) (w : Term D) (hw : Term.map e.hom z = w) :
    pathApp (S.rebuiltComparison e r s z w hw) =
      Term.map (Functor.whiskerLeft (projection (interval Ξ)).mapElements
        (Functor.whiskerLeft (graph s).mapElements e.inv))
        (pathApp (S.comparisonInFamily r s w)) := by
  let q := homogeneousPathMap (Functor.whiskerLeft (graph s).mapElements e.inv)
    (S.comparisonInFamily r s w)
  have h : Term.map e.inv w = z := hw.symm ▸ Term.map_iso_roundtrip e z
  exact (pathApp_lam (pathApp q) (pathApp_zero q)
    ((pathApp_one q).trans (congrArg (fun t => Term.reindex t (graph s)) h))).trans
      (pathApp_lam _ _ _)

private theorem prescribed_comparison_body_congr {C : Family (total (interval Ξ))}
    {F G : Filling C} (hF : F.Lawful) (hG : G.Lawful) (h : F = G)
    (r s : Term (interval Ξ)) (z : Term C) :
    pathApp (IntervalTransport.prescribedLineComparison F hF r s
      (Term.reindex z (graph r)) z rfl) =
    pathApp (IntervalTransport.prescribedLineComparison G hG r s
      (Term.reindex z (graph r)) z rfl) := by
  cases h
  rfl

/-- Full canonical-operation preservation gives exact selected-body preservation
through the actual source and target decoder adapters. -/
theorem Result.comparison_body_eq_of_filling {C D : Family (total (interval Ξ))}
    (R : Result C) (S : Result D) (e : C ≅ D) (r s : Term (interval Ξ))
    (z : Term C) (w : Term D) (hw : Term.map e.hom z = w)
    (hF : (NativeDecode.filling R.code).transport
      (R.decoding ≪≫ e ≪≫ S.decoding.symm) = NativeDecode.filling S.code) :
    pathApp (R.comparisonInFamily r s z) = pathApp (S.rebuiltComparison e r s z w hw) := by
  let d := R.decoding ≪≫ e ≪≫ S.decoding.symm
  have hs : Term.map d.hom (Term.map R.decoding.inv z) = Term.map S.decoding.inv w :=
    (congrArg (fun t => Term.map S.decoding.inv (Term.map e.hom t))
      (Term.map_iso_roundtrip R.decoding.symm z)).trans
        (congrArg (Term.map S.decoding.inv) hw)
  have hn := IntervalTransport.prescribedLineComparison_body_transport
    (NativeDecode.filling R.code) (NativeDecode.filling_lawful R.code) r s
    (Term.reindex (Term.map R.decoding.inv z) (graph r)) (Term.map R.decoding.inv z) rfl d
  change (NativeDecode.filling R.code).transport d = NativeDecode.filling S.code at hF
  have hn' := (prescribed_comparison_body_congr
    (Filling.transport_lawful d (NativeDecode.filling R.code)
      (NativeDecode.filling_lawful R.code)) (NativeDecode.filling_lawful S.code)
    hF r s (Term.map d.hom (Term.map R.decoding.inv z))).symm.trans hn
  have hb : pathApp (S.transportComparison r s w) =
      Term.map (Functor.whiskerLeft (projection (interval Ξ)).mapElements
        (Functor.whiskerLeft (graph s).mapElements d.hom))
        (pathApp (R.transportComparison r s z)) :=
    (congrArg (fun t => pathApp (IntervalTransport.prescribedLineComparison
      (NativeDecode.filling S.code) (NativeDecode.filling_lawful S.code) r s
      (Term.reindex t (graph r)) t rfl)) hs).symm.trans hn'
  let E := Functor.isoWhiskerLeft (projection (interval Ξ) ≫ graph s).mapElements e
  let T := Functor.isoWhiskerLeft (projection (interval Ξ) ≫ graph s).mapElements S.decoding
  let t := Term.map (Functor.whiskerLeft (projection (interval Ξ)).mapElements
    (Functor.whiskerLeft (graph s).mapElements R.decoding.hom))
    (pathApp (R.transportComparison r s z))
  have hc := congrArg (fun q => Term.map E.inv (Term.map T.hom q)) hb
  have hr := (congrArg (Term.map E.inv)
    (Term.map_iso_roundtrip T.symm (Term.map E.hom t))).trans (Term.map_iso_roundtrip E t)
  rw [Result.rebuiltComparison_body, Result.comparisonInFamily_body, Result.comparisonInFamily_body]
  exact (hc.trans hr).symm

/-- Independent fixed Sigma rebuilding preserves the complete selected body
at arbitrary source and target caps. -/
theorem pair_comparison_body_recomputed
    (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Ξ))
    (z : Term (reindex (Cartesian.sigma (liftedDecode a) (liftedDecode b)) (graph r)))
    (σ : Ω ⟶ Ξ) :
    pathApp (((sigma a b).reindex (intervalSub σ)).comparisonInFamily
      (Term.reindex r σ) (Term.reindex s σ)
      (Term.reindex (pairSection a b r z) (intervalSub σ))) =
    pathApp ((sigma (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)).rebuiltComparison
      (Iso.refl _) (Term.reindex r σ) (Term.reindex s σ)
      (Term.reindex (pairSection a b r z) (intervalSub σ))
      (pairSection (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)
        (Term.reindex r σ) (Term.reindex z σ)) (pairSection_reindex a b r z σ).symm) := by
  apply Result.comparison_body_eq_of_filling
  exact sigmaSubstitution_native_filling a b (intervalSub σ)

/-- Independent fixed Pi rebuilding preserves the complete selected body
at arbitrary source and target caps. -/
theorem function_comparison_body_recomputed
    (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) (r s : Term (interval Ξ))
    (z : Term (reindex (Cartesian.pi (liftedDecode a) (liftedDecode b)) (graph r)))
    (σ : Ω ⟶ Ξ) :
    pathApp (((pi a b).reindex (intervalSub σ)).comparisonInFamily
      (Term.reindex r σ) (Term.reindex s σ)
      (Term.reindex (functionSection a b r z) (intervalSub σ))) =
    pathApp ((pi (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)).rebuiltComparison
      (piReindexIso (liftedDecode a) (liftedDecode b) (intervalSub σ)) (Term.reindex r σ) (Term.reindex s σ)
      (Term.reindex (functionSection a b r z) (intervalSub σ))
      (functionSection (intervalSub σ ≫ a) (liftSub (liftedDecode a) (intervalSub σ) ≫ b)
        (Term.reindex r σ) (functionInitialReindex a b r z σ)) (functionSection_reindex a b r z σ).symm) := by
  apply Result.comparison_body_eq_of_filling
  exact piSubstitution_native_filling a b (intervalSub σ)

end SmallUniverse.LargeConstructors
end SquareKit.Cubical.Cartesian
