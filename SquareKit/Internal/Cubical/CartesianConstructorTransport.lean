import SquareKit.Internal.Cubical.CartesianLargeFamilySubstitution
import SquareKit.Internal.Cubical.CartesianTransportConcatenation

/-! Native Cartesian transport of dependent pairs and functions. The algorithms
retain their whole sections and compare with the canonical decoder transport by
chosen native paths. Source caps may be arbitrary interval sections. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

theorem Term.map_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (t : Term A) (σ : Δ ⟶ Γ) :
    Term.map (Functor.whiskerLeft σ.mapElements f) (Term.reindex t σ) =
      Term.reindex (Term.map f t) σ := rfl

theorem OpenBox.sigmaFst_emptyBox {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {B : Family (total A)} (r : Term (interval Γ))
    (z : Term (Cartesian.reindex (sigma A B) (graph r))) :
    (IntervalTransport.emptyBox r z).sigmaFst = IntervalTransport.emptyBox r
      (Cartesian.sigmaFst (B := Cartesian.reindex B (liftSub A (graph r))) z) := by
  apply OpenBox.ext
  · apply PartialSection.ext
    intro x h
    exact h.elim
  · rfl

theorem OpenBox.map_emptyBox {Γ : Context.{u}} {A B : Family (total (interval Γ))}
    (f : A ⟶ B) (r : Term (interval Γ)) (z : Term (Cartesian.reindex A (graph r))) :
    (IntervalTransport.emptyBox r z).map f = IntervalTransport.emptyBox r
      (Term.map (Functor.whiskerLeft (graph r).mapElements f) z) := by
  apply OpenBox.ext
  · apply PartialSection.ext
    intro x h
    exact h.elim
  · rfl

/-- Only the observation is discrete; the path and its family remain native. -/
theorem homogeneousPath_observe {Γ : Context.{u}} {A : Family Γ} {S : Type u}
    (v : A ⟶ constantFamily Γ S) {a b : Term A} (p : Term (homogeneousPath A a b)) :
    Term.map v a = Term.map v b := by
  let q := homogeneousPathMap v p
  apply Term.ext
  intro x
  exact (congrArg (fun t => t.val x) (pathApp_zero q)).symm.trans
    ((constant_section_interval (pathApp q) x ((endpoint Γ false).val x)
      ((endpoint Γ true).val x)).trans (congrArg (fun t => t.val x) (pathApp_one q)))

private theorem mapped_path_retarget_body {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) {a b : Term A} (p : Term (homogeneousPath A a b))
    {c : Term B} (h : Term.map f b = c) :
    pathApp (pathLam (pathApp (homogeneousPathMap f p)) (pathApp_zero _)
      ((pathApp_one _).trans h)) =
      Term.map (Functor.whiskerLeft (projection (interval Γ)).mapElements f) (pathApp p) :=
  (pathApp_lam _ _ _).trans (pathApp_lam _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Observe a dependent function at a fixed argument without discarding its
restriction-indexed function value or its dependent output family. -/
def piObservation {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)} {S : Type u}
    (v : B ⟶ constantFamily (total A) S) (a : Term A) : pi A B ⟶ constantFamily Γ S where
  app x := TypeCat.ofHom (fun p => v.app (extendObj A x (a.val x)) (p.val (𝟙 x) (a.val x)))
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro p
    have hn := v.naturality_apply (extendHom A f (a.val x)) (p.val (𝟙 x) (a.val x))
    have hp := p.naturality (𝟙 x) f (a.val x)
    change v.app (extendObj A y (a.val y)) (p.val (f ≫ 𝟙 y) (a.val y)) =
      v.app (extendObj A x (a.val x)) (p.val (𝟙 x) (a.val x))
    change v.app (extendObj A y (A.map f (a.val x)))
      (B.map (extendHom A f (a.val x)) (p.val (𝟙 x) (a.val x))) =
      v.app (extendObj A x (a.val x)) (p.val (𝟙 x) (a.val x)) at hn
    rw [hp, Category.id_comp] at hn
    rw [Category.comp_id]
    exact (congrArg (fun z => v.app (extendObj A y z) (p.val f z)) (a.property f)).symm.trans hn

namespace SmallUniverse.LargeConstructors
open NativeUnivalence
variable {Ξ : Context.{u+1}}

/-- A constructor's actual output code line, with both endpoint codes retained. -/
def Result.codePath {C : Family (total (interval Ξ))} (R : Result C) :
    Term (paths (endpointSub Ξ false ≫ R.code) (endpointSub Ξ true ≫ R.code)) :=
  pathOfCode _ _ R.code rfl rfl

theorem Result.codePath_transport {C : Family (total (interval Ξ))} (R : Result C) :
    pathToMap R.codePath =
      IntervalTransport.map (NativeDecode.filling R.code) (endpoint Ξ false) (endpoint Ξ true) :=
  (CodeTransport.map_path R.codePath).symm

/-- The body is derived by the canonical decoder's evaluation lifting. -/
noncomputable def Result.transportFromSection {C : Family (total (interval Ξ))}
    (R : Result C) (r s : Term (interval Ξ)) (z : Term C)
    (t : Term (Cartesian.reindex C (graph r))) (hz : Term.reindex z (graph r) = t) :
    Term (homogeneousPath (Cartesian.reindex (liftedDecode R.code) (graph s))
      (Term.map (IntervalTransport.map (NativeDecode.filling R.code) r s)
        (Term.map (Functor.whiskerLeft (graph r).mapElements R.decoding.inv) t))
      (Term.map (Functor.whiskerLeft (graph s).mapElements R.decoding.inv)
        (Term.reindex z (graph s)))) :=
  IntervalTransport.prescribedLineComparison (NativeDecode.filling R.code)
    (NativeDecode.filling_lawful R.code) r s
    (Term.map (Functor.whiskerLeft (graph r).mapElements R.decoding.inv) t)
    (Term.map R.decoding.inv z)
    (congrArg (Term.map (Functor.whiskerLeft (graph r).mapElements R.decoding.inv)) hz)

noncomputable def Result.transportComparison {C : Family (total (interval Ξ))}
    (R : Result C) (r s : Term (interval Ξ)) (z : Term C) :=
  R.transportFromSection r s z (Term.reindex z (graph r)) rfl

/-- Actual canonical transport, expressed in the constructor family. -/
noncomputable def Result.transportInFamily {C : Family (total (interval Ξ))}
    (R : Result C) (r s : Term (interval Ξ)) (t : Term (Cartesian.reindex C (graph r))) :
    Term (Cartesian.reindex C (graph s)) :=
  Term.map (Functor.whiskerLeft (graph s).mapElements R.decoding.hom)
    (Term.map (IntervalTransport.map (NativeDecode.filling R.code) r s)
      (Term.map (Functor.whiskerLeft (graph r).mapElements R.decoding.inv) t))

/-- Both decoder maps remain in the chosen comparison; no operation equality is
assumed between the canonical and returned fillers. -/
noncomputable def Result.comparisonInFamily {C : Family (total (interval Ξ))}
    (R : Result C) (r s : Term (interval Ξ)) (z : Term C) :
    Term (homogeneousPath (Cartesian.reindex C (graph s))
      (R.transportInFamily r s (Term.reindex z (graph r))) (Term.reindex z (graph s))) := by
  let q := homogeneousPathMap (Functor.whiskerLeft (graph s).mapElements R.decoding.hom)
    (R.transportComparison r s z)
  exact pathLam (pathApp q) (pathApp_zero q)
    ((pathApp_one q).trans (Term.map_iso_roundtrip
      (Functor.isoWhiskerLeft (graph s).mapElements R.decoding).symm _))

set_option backward.isDefEq.respectTransparency false in
theorem Result.comparisonInFamily_body {C : Family (total (interval Ξ))}
    (R : Result C) (r s : Term (interval Ξ)) (z : Term C) :
    pathApp (R.comparisonInFamily r s z) =
      Term.map (Functor.whiskerLeft (projection (interval Ξ)).mapElements
        (Functor.whiskerLeft (graph s).mapElements R.decoding.hom))
        (pathApp (R.transportComparison r s z)) := by
  exact mapped_path_retarget_body (Functor.whiskerLeft (graph s).mapElements R.decoding.hom)
    (R.transportComparison r s z)
    (Term.map_iso_roundtrip (Functor.isoWhiskerLeft (graph s).mapElements R.decoding).symm _)

/-- Reverse transport recovers the entire source field by a native path. -/
noncomputable def Result.roundTripComparison {C : Family (total (interval Ξ))}
    (R : Result C) (r s : Term (interval Ξ)) (t : Term (Cartesian.reindex C (graph r))) :
    Term (homogeneousPath (Cartesian.reindex C (graph r))
      (R.transportInFamily s r (R.transportInFamily r s t)) t) := by
  let F := NativeDecode.filling R.code
  have hF := NativeDecode.filling_lawful R.code
  let a := Term.map (Functor.whiskerLeft (graph r).mapElements R.decoding.inv) t
  let z := IntervalTransport.line F r (𝟙 Ξ) a
  let forward := Term.map (IntervalTransport.map F r s) a
  let p := IntervalTransport.prescribedLineComparison F hF s r forward z
    (IntervalTransport.map_section F hF r s a).symm
  let q := homogeneousPathMap (Functor.whiskerLeft (graph r).mapElements R.decoding.hom) p
  have hs : R.transportInFamily s r (R.transportInFamily r s t) =
      Term.map (Functor.whiskerLeft (graph r).mapElements R.decoding.hom)
        (Term.map (IntervalTransport.map F s r) forward) :=
    congrArg (fun b => Term.map (Functor.whiskerLeft (graph r).mapElements R.decoding.hom)
      (Term.map (IntervalTransport.map F s r) b))
      (Term.map_iso_roundtrip (Functor.isoWhiskerLeft (graph s).mapElements R.decoding) forward)
  have ht := (congrArg (Term.map (Functor.whiskerLeft (graph r).mapElements R.decoding.hom))
    (IntervalTransport.line_source F hF r (𝟙 Ξ) a)).trans
    (Term.map_iso_roundtrip (Functor.isoWhiskerLeft (graph r).mapElements R.decoding).symm t)
  exact pathLam (pathApp q) ((pathApp_zero q).trans hs.symm) ((pathApp_one q).trans ht)

section Pair
variable (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
  (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) (r : Term (interval Ξ))
  (z : Term (Cartesian.reindex (Cartesian.sigma (liftedDecode a) (liftedDecode b)) (graph r)))

noncomputable def pairFirst : Term (liftedDecode a) :=
  (NativeDecode.filling a).fill (𝟙 _) Subcontext.bot r
    (OpenBox.sigmaFst (B := Cartesian.reindex (liftedDecode b) (liftSub (liftedDecode a) (𝟙 _)))
      (IntervalTransport.emptyBox r z))

noncomputable def pairSecond : Term (Cartesian.reindex (liftedDecode b) (pair (𝟙 _) (pairFirst a b r z))) :=
  (NativeDecode.filling b).fill (pair (𝟙 _) (pairFirst a b r z)) Subcontext.bot r
    (OpenBox.sigmaSnd (B := Cartesian.reindex (liftedDecode b) (liftSub (liftedDecode a) (𝟙 _)))
      (IntervalTransport.emptyBox r z) (pairFirst a b r z)
      ((NativeDecode.filling_lawful a).fills (𝟙 _) Subcontext.bot r _))

/-- Fill the first component and then its dependent field along that section. -/
noncomputable def pairSection : Term (Cartesian.sigma (liftedDecode a) (liftedDecode b)) :=
  sigmaIntro (pairFirst a b r z) (pairSecond a b r z)

theorem pairSection_selected : pairSection a b r z =
    IntervalTransport.line
      (sigmaFilling (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling b))
      r (𝟙 Ξ) z := rfl

theorem pairSection_source : Term.reindex (pairSection a b r z) (graph r) = z :=
  IntervalTransport.line_source _
    (sigmaFilling_lawful _ (NativeDecode.filling_lawful a) _ (NativeDecode.filling_lawful b)) r (𝟙 Ξ) z

set_option backward.isDefEq.respectTransparency false in
theorem pairFirst_target (s : Term (interval Ξ)) :
    Term.reindex (pairFirst a b r z) (graph s) =
      Term.map (IntervalTransport.map (NativeDecode.filling a) r s)
        (Cartesian.sigmaFst (B := Cartesian.reindex (liftedDecode b) (liftSub (liftedDecode a) (graph r))) z) :=
by
  unfold pairFirst
  rw [OpenBox.sigmaFst_emptyBox]
  exact (IntervalTransport.map_section (NativeDecode.filling a) (NativeDecode.filling_lawful a) r s
    (Cartesian.sigmaFst (B := Cartesian.reindex (liftedDecode b) (liftSub (liftedDecode a) (graph r))) z)).symm


noncomputable def pairTransportFormula (s : Term (interval Ξ)) :=
  (sigma a b).transportFromSection r s (pairSection a b r z) z (pairSection_source a b r z)

end Pair

section Function
variable (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
  (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u}) (r : Term (interval Ξ))
  (z : Term (Cartesian.reindex (Cartesian.pi (liftedDecode a) (liftedDecode b)) (graph r)))

/-- The generic target argument is extended backwards from its variable cap. -/
noncomputable def functionArgument := FunctionFilling.argument (NativeDecode.filling a) (𝟙 _)

noncomputable def functionBody :=
  FunctionFilling.body (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling b) (𝟙 _) Subcontext.bot r (IntervalTransport.emptyBox r z)

/-- Native Cartesian function filling keeps every restriction-indexed argument. -/
noncomputable def functionSection : Term (Cartesian.pi (liftedDecode a) (liftedDecode b)) :=
  FunctionFilling.fill (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling b) (𝟙 _) Subcontext.bot r (IntervalTransport.emptyBox r z)

theorem functionSection_selected : functionSection a b r z =
    IntervalTransport.line
      (piFilling (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling b))
      r (𝟙 Ξ) z := rfl

theorem functionSection_source : Term.reindex (functionSection a b r z) (graph r) = z :=
  FunctionFilling.fill_cap _ (NativeDecode.filling_lawful a) _ (NativeDecode.filling_lawful b)
    (𝟙 _) Subcontext.bot r (IntervalTransport.emptyBox r z)

theorem functionSection_apply : Cartesian.app (functionSection a b r z) = functionBody a b r z :=
  congrArg Cartesian.app (FunctionFilling.fill_normalize (NativeDecode.filling a)
    (NativeDecode.filling_lawful a) (NativeDecode.filling b) (𝟙 _) Subcontext.bot r _)

noncomputable def functionTransportFormula (s : Term (interval Ξ)) :=
  (pi a b).transportFromSection r s (functionSection a b r z) z (functionSection_source a b r z)

end Function

/-- The input is the actual supplied native universe path, with its source and
target codes. The dependent code ranges over its full decoded display. -/
noncomputable def pairAlongPath {a₀ a₁ : Ξ ⟶ smallFamilyCodes.{u}}
    (p : Term (paths a₀ a₁))
    (b : total (liftedDecode (codeOfPath p)) ⟶ smallFamilyCodes.{u})
    (z : Term (Cartesian.reindex (Cartesian.sigma (liftedDecode (codeOfPath p)) (liftedDecode b))
      (endpointSub Ξ false))) :=
  pairTransportFormula (codeOfPath p) b (endpoint Ξ false) z (endpoint Ξ true)

set_option backward.isDefEq.respectTransparency false in
/-- The first component follows the actual native universe transport, including
the source and target code conversions. -/
theorem pairFirst_path {a₀ a₁ : Ξ ⟶ smallFamilyCodes.{u}}
    (p : Term (paths a₀ a₁))
    (b : total (liftedDecode (codeOfPath p)) ⟶ smallFamilyCodes.{u})
    (z : Term (Cartesian.reindex (Cartesian.sigma (liftedDecode (codeOfPath p)) (liftedDecode b))
      (endpointSub Ξ false))) :
    CodeTransport.cast (codeOfPath_one p)
        (Term.reindex (pairFirst (codeOfPath p) b (endpoint Ξ false) z) (endpointSub Ξ true)) =
      Term.map (pathToMap p) (CodeTransport.cast (codeOfPath_zero p)
        (Cartesian.sigmaFst (B := Cartesian.reindex (liftedDecode b)
          (liftSub (liftedDecode (codeOfPath p)) (endpointSub Ξ false))) z)) := by
  have ht := pairFirst_target (codeOfPath p) b (endpoint Ξ false) z (endpoint Ξ true)
  apply (congrArg (CodeTransport.cast (codeOfPath_one p)) ht).trans
  let t := Cartesian.sigmaFst (B := Cartesian.reindex (liftedDecode b)
    (liftSub (liftedDecode (codeOfPath p)) (endpointSub Ξ false))) z
  have hm := CodeTransport.map_apply (codeOfPath p) a₀ a₁ (codeOfPath_zero p) (codeOfPath_one p)
    (CodeTransport.cast (codeOfPath_zero p) t)
  simp only [CodeTransport.cast_trans, CodeTransport.cast_refl] at hm
  exact hm.symm.trans (congrArg (fun f => Term.map f (CodeTransport.cast (codeOfPath_zero p) t))
    (CodeTransport.map_path p))


noncomputable def functionAlongPath {a₀ a₁ : Ξ ⟶ smallFamilyCodes.{u}}
    (p : Term (paths a₀ a₁))
    (b : total (liftedDecode (codeOfPath p)) ⟶ smallFamilyCodes.{u})
    (z : Term (Cartesian.reindex (Cartesian.pi (liftedDecode (codeOfPath p)) (liftedDecode b))
      (endpointSub Ξ false))) :=
  functionTransportFormula (codeOfPath p) b (endpoint Ξ false) z (endpoint Ξ true)

end SmallUniverse.LargeConstructors
end SquareKit.Cubical.Cartesian
