import SquareKit.Internal.Cubical.LargeFamilySubstitution
import SquareKit.Internal.Cubical.NaturalUnivalenceLaws

/-! Transport comparisons for constructed dependent pairs and functions. The
comparison with the universal decoder's chosen transport is a native path;
it does not assert equality of independently chosen filling operations. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.LargeConstructors
open CategoryTheory NativeUnivalence
universe u
variable {Ξ : Context.{u+1}}

/-- The actual code line supplied to a constructor by a universe path. -/
def inputLine {a₀ a₁ : Ξ ⟶ smallFamilyCodes.{u}} (p : Term (paths a₀ a₁)) :
    total (interval Ξ) ⟶ smallFamilyCodes.{u} := code (pathApp p)

def Result.codePath {C : Family (total (interval Ξ))} (R : Result C) :
    Term (paths (endpointSub Ξ false ≫ R.code) (endpointSub Ξ true ≫ R.code)) :=
  pathOfCode _ _ R.code rfl rfl

theorem Result.codePath_transport {C : Family (total (interval Ξ))} (R : Result C) :
    NativeUnivalence.pathToMap R.codePath = IntervalTransport.map (NativeDecode.filling R.code) := rfl

/-- Both endpoints use the actual inverse decoder comparison. -/
noncomputable def Result.transportComparison {C : Family (total (interval Ξ))}
    (R : Result C) (z : Term C) :
    Term (homogeneousPath (Presheaf.reindex (liftedDecode R.code) (endpointSub Ξ true))
      (Term.map (IntervalTransport.map (NativeDecode.filling R.code))
        ((Term.map R.decoding.inv z).reindex (endpointSub Ξ false)))
      ((Term.map R.decoding.inv z).reindex (endpointSub Ξ true))) :=
  NativeTransportComposition.sectionComparison (NativeDecode.filling R.code)
    (NativeDecode.filling_lawful R.code) (Term.map R.decoding.inv z)

theorem Result.transportComparison_body_reindex {Ω : Context.{u+1}}
    {C : Family (total (interval Ξ))} (R : Result C) (z : Term C) (σ : Ω ⟶ Ξ) :
    pathApp ((R.reindex (liftSub (interval Ξ) σ)).transportComparison
      (z.reindex (liftSub (interval Ξ) σ))) =
      (pathApp (R.transportComparison z)).reindex (liftSub (interval Ξ) σ) :=
  NativeTransportComposition.sectionComparison_body_reindex (NativeDecode.filling R.code)
    (NativeDecode.filling_lawful R.code) (Term.map R.decoding.inv z) σ

noncomputable def Result.transportFromSection {C : Family (total (interval Ξ))}
    (R : Result C) (z : Term C) (t : Term (Presheaf.reindex C (endpointSub Ξ false)))
    (hz : z.reindex (endpointSub Ξ false) = t) :
    Term (homogeneousPath (Presheaf.reindex (liftedDecode R.code) (endpointSub Ξ true))
      (Term.map (IntervalTransport.map (NativeDecode.filling R.code))
        (Term.map (Functor.whiskerLeft (endpointSub Ξ false).mapElements R.decoding.inv) t))
      (Term.map (Functor.whiskerLeft (endpointSub Ξ true).mapElements R.decoding.inv)
        (z.reindex (endpointSub Ξ true)))) :=
  let q := R.transportComparison z
  pathLam (pathApp q)
    ((pathApp_zero q).trans (congrArg (Term.map (IntervalTransport.map (NativeDecode.filling R.code)))
      (congrArg (Term.map (Functor.whiskerLeft (endpointSub Ξ false).mapElements R.decoding.inv)) hz)))
    (pathApp_one q)

theorem inputLine_zero {a₀ a₁ : Ξ ⟶ smallFamilyCodes.{u}} (p : Term (paths a₀ a₁)) :
    endpointSub Ξ false ≫ inputLine p = a₀ := congrArg code (pathApp_zero p)

theorem inputLine_one {a₀ a₁ : Ξ ⟶ smallFamilyCodes.{u}} (p : Term (paths a₀ a₁)) :
    endpointSub Ξ true ≫ inputLine p = a₁ := congrArg code (pathApp_one p)

section Pair
variable (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
  (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u})
  (z : Term (Presheaf.reindex (Presheaf.sigma (liftedDecode a) (liftedDecode b)) (endpointSub Ξ false)))

noncomputable def pairFirst : Term (liftedDecode a) :=
  (NativeDecode.filling a).fill (𝟙 _) (Cofibration.bot Ξ)
    (OpenBox.sigmaFst (B := Presheaf.reindex (liftedDecode b) (liftSub (liftedDecode a) (𝟙 _)))
      (OpenBox.empty _ z))

noncomputable def pairSecond : Term (Presheaf.reindex (liftedDecode b) (pair (𝟙 _) (pairFirst a b z))) :=
  (NativeDecode.filling b).fill (pair (𝟙 _) (pairFirst a b z)) (Cofibration.bot Ξ)
    (OpenBox.sigmaSnd (B := reindex (liftedDecode b) (liftSub (liftedDecode a) (𝟙 _)))
      (OpenBox.empty _ z) (pairFirst a b z)
      ((NativeDecode.filling_lawful a).fills (𝟙 _) (Cofibration.bot Ξ)
        (OpenBox.sigmaFst (B := reindex (liftedDecode b) (liftSub (liftedDecode a) (𝟙 _)))
          (OpenBox.empty _ z))))

/-- Fill the first component, then the dependent component along that very section. -/
noncomputable def pairSection : Term (Presheaf.sigma (liftedDecode a) (liftedDecode b)) :=
  sigmaIntro (pairFirst a b z) (pairSecond a b z)

theorem pairSection_zero : (pairSection a b z).reindex (endpointSub Ξ false) = z :=
  IntervalTransport.forward_zero
    (sigmaFilling (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling b))
    (sigmaFilling_lawful (NativeDecode.filling a) (NativeDecode.filling_lawful a)
      (NativeDecode.filling b) (NativeDecode.filling_lawful b)) (𝟙 Ξ) z

noncomputable def pairTransportFormula := (sigma a b).transportFromSection (pairSection a b z) z (pairSection_zero a b z)

end Pair

/-- Instantiate the pair formula along an actual supplied universe path. The
second code may vary over the entire dependent display of that line. -/
noncomputable def pairAlongPath {a₀ a₁ : Ξ ⟶ smallFamilyCodes.{u}}
    (p : Term (paths a₀ a₁))
    (b : total (liftedDecode (inputLine p)) ⟶ smallFamilyCodes.{u})
    (z : Term (Presheaf.reindex (Presheaf.sigma (liftedDecode (inputLine p)) (liftedDecode b))
      (endpointSub Ξ false))) := pairTransportFormula (inputLine p) b z

section Function
variable (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
  (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u})
  (z : Term (Presheaf.reindex (Presheaf.pi (liftedDecode a) (liftedDecode b)) (endpointSub Ξ false)))

/-- The full selected function algorithm: extend the argument backwards and
compose its dependent value. Scaling retains the initial function at dimension
zero and produces a whole section, including all intermediate dimensions. -/
noncomputable def functionSection : Term (Presheaf.pi (liftedDecode a) (liftedDecode b)) :=
  (FunctionComposition.comp (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling b).toComposition (scaleInterval Ξ)
    (scaledFace (Cofibration.bot Ξ)) (scaledBox (OpenBox.empty _ z))).convert
      (congrArg (fun q => Presheaf.reindex (Presheaf.pi (liftedDecode a) (liftedDecode b)) q)
        (scaleInterval_one Ξ))

theorem functionSection_selected : functionSection a b z =
    IntervalTransport.forward
      (piFilling (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling b))
      (𝟙 Ξ) z := rfl

theorem functionSection_zero : (functionSection a b z).reindex (endpointSub Ξ false) = z :=
  IntervalTransport.forward_zero
    (piFilling (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling b))
    (piFilling_lawful (NativeDecode.filling a) (NativeDecode.filling_lawful a)
      (NativeDecode.filling b) (NativeDecode.filling_lawful b)) (𝟙 Ξ) z

noncomputable def functionTransportFormula := (pi a b).transportFromSection (functionSection a b z) z (functionSection_zero a b z)
end Function

noncomputable def functionAlongPath {a₀ a₁ : Ξ ⟶ smallFamilyCodes.{u}}
    (p : Term (paths a₀ a₁))
    (b : total (liftedDecode (inputLine p)) ⟶ smallFamilyCodes.{u})
    (z : Term (Presheaf.reindex (Presheaf.pi (liftedDecode (inputLine p)) (liftedDecode b))
      (endpointSub Ξ false))) := functionTransportFormula (inputLine p) b z

end SquareKit.Cubical.Presheaf.SmallUniverse.LargeConstructors
