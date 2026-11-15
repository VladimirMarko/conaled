import SquareKit.Internal.Cubical.NativeUnivalenceCharts
import SquareKit.Internal.Cubical.UnivalenceSubstitution

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Ξ : Context.{u+1}} (a b : Ξ ⟶ smallFamilyCodes.{u})
  (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)

theorem chartCode_reindex {Γ Δ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) (τ : Δ ⟶ Γ) :
    raisedSub (liftSub (interval Γ) τ) ≫ chartCode a b f E σ =
      chartCode a b f E (raisedSub τ ≫ σ) := by
  have h := Univalence.uaCode_reindex (σ ≫ a) (σ ≫ b) τ (lowerChartMap a b σ f)
    (lowerChartEquivalence a b σ f E)
  exact h.trans (congrArg (fun e => Univalence.uaCode
    (raisedSub τ ≫ σ ≫ a) (raisedSub τ ≫ σ ≫ b)
    (lowerChartMap a b (raisedSub τ ≫ σ) f) e)
    (lowerChartEquivalence_reindex a b σ f E τ).symm)

noncomputable def uaLine : Term (family (total (interval Ξ))) :=
  coherentLine a b f E (chartCode_reindex a b f E)

theorem uaLine_zero : (uaLine a b f E).reindex (endpointSub Ξ false) = term a :=
  coherentLine_zero a b f E (chartCode_reindex a b f E)

theorem uaLine_one : (uaLine a b f E).reindex (endpointSub Ξ true) = term b :=
  coherentLine_one a b f E (chartCode_reindex a b f E)

noncomputable def ua : Term (paths a b) :=
  uaFromCharts a b f E (chartCode_reindex a b f E)

noncomputable def genericEquivalence :
    Σ g : reindex (liftedDecode a) (projection (equivalences a b)) ⟶
      reindex (liftedDecode b) (projection (equivalences a b)), HomotopyEquivalence g :=
  (EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b)
    (projection (equivalences a b))).symm (generic (equivalences a b))

noncomputable def equivalencePathSection :
    Term (reindex (paths a b) (projection (equivalences a b))) :=
  Term.map (pathReindexIso (reindex (family Ξ) (projection (interval Ξ)))
    (term a) (term b) (projection (equivalences a b))).inv
    (ua (projection (equivalences a b) ≫ a) (projection (equivalences a b) ≫ b)
      (genericEquivalence a b).1 (genericEquivalence a b).2)

/-- The reverse operation is a native map out of the full internal equivalence family. -/
noncomputable def equivToPath : equivalences a b ⟶ paths a b :=
  EquivalenceFamilies.decodeMap (lam (equivalencePathSection a b))

end SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
