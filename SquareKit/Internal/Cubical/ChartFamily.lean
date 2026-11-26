import SquareKit.Internal.Cubical.ConstructorTransport
import SquareKit.Internal.Cubical.EquivalenceExtension
import SquareKit.Internal.Cubical.ComprehensionTransport

/-! Finite-label chart predicates in a fixed small universe over arbitrary larger
contexts. The returned filler is the constructor's selected operation. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.ChartFamily
open CategoryTheory
universe u
variable {Ξ Ω : Context.{u+1}}

abbrev Count (Ξ : Context.{u+1}) := Term (constantFamily Ξ (ULift.{u+1} Nat))

def labels (n : Count Ξ) : Family Ξ :=
  discreteFamily n (fun k => ULift.{u+1} (Fin k.down))

def labelPresentation (n : Count Ξ) : SmallPresentation.Data (labels n) where
  Fiber x := ULift.{u} (Fin (n.val x).down)
  equiv _ := Equiv.ulift.trans Equiv.ulift.symm

def labelFilling (n : Count Ξ) : Filling (labels n) :=
  discreteFilling n (fun k => ULift.{u+1} (Fin k.down))

theorem labelFilling_lawful (n : Count Ξ) : (labelFilling n).Lawful :=
  discreteFilling_lawful _ _

noncomputable def labelCode (n : Count Ξ) : LargeConstructors.Result (labels n) :=
  LargeConstructors.construct (labelPresentation n) (labelFilling n) (labelFilling_lawful n)

abbrev labelContext (n : Count Ξ) := total (labels n)

def labelProjection (n : Count Ξ) : labelContext n ⟶ Ξ := projection (labels n)

noncomputable def labelContextIso (n : Count Ξ) :
    total (liftedDecode (labelCode n).code) ≅ labelContext n :=
  totalIso (labelCode n).decoding

theorem label_selected (n : Count Ξ) :
    (labelCode n).filling.transport (labelCode n).decoding = labelFilling n :=
  LargeConstructors.construct_filling _ _ _

/-- Only count, codes and actual sections are inputs. -/
structure Inputs (Ξ : Context.{u+1}) where
  count : Count Ξ
  Y : Ξ ⟶ smallFamilyCodes.{u}
  D : labelContext count ⟶ smallFamilyCodes.{u}
  target : Term (liftedDecode (projection (liftedDecode D) ≫ labelProjection count ≫ Y))
  endpoint : Term (liftedDecode Y)

/-- Extend by Y and use its actual generic variable as endpoint. -/
def genericEndpoint (n : Count Ξ) (Y : Ξ ⟶ smallFamilyCodes.{u})
    (D : labelContext n ⟶ smallFamilyCodes.{u})
    (s : Term (liftedDecode (projection (liftedDecode D) ≫ labelProjection n ≫ Y))) :
    Inputs (total (liftedDecode Y)) where
  count := n.reindex (projection (liftedDecode Y))
  Y := projection (liftedDecode Y) ≫ Y
  D := liftSub (labels n) (projection (liftedDecode Y)) ≫ D
  target := s.reindex (liftSub (liftedDecode D) (liftSub (labels n) (projection (liftedDecode Y))))
  endpoint := generic (liftedDecode Y)

namespace Inputs
variable (I : Inputs Ξ)

abbrev domain := liftedDecode I.D
abbrev display := projection I.domain ≫ labelProjection I.count
abbrev weakenedEndpoint := I.endpoint.reindex I.display
abbrev pathBody := projection (interval (total I.domain)) ≫ I.display ≫ I.Y
abbrev paths := homogeneousPath (liftedDecode (I.display ≫ I.Y)) I.target I.weakenedEndpoint
abbrev inner := Presheaf.sigma I.domain I.paths
abbrev outer := Presheaf.sigma (labels I.count) I.inner

def selectedLabel (z : Term I.outer) : Term (labels I.count) := sigmaFst z
def selectedDomain (z : Term I.outer) :
    Term (reindex I.domain (pair (𝟙 Ξ) (I.selectedLabel z))) :=
  sigmaFst (A := reindex I.domain (pair (𝟙 Ξ) (I.selectedLabel z)))
    (B := reindex I.paths (liftSub I.domain (pair (𝟙 Ξ) (I.selectedLabel z)))) (sigmaSnd z)
def selectedDisplay (z : Term I.outer) : Ξ ⟶ total I.domain :=
  pair (pair (𝟙 Ξ) (I.selectedLabel z)) (I.selectedDomain z)
def selectedPath (z : Term I.outer) : Term (reindex I.paths (I.selectedDisplay z)) :=
  sigmaSnd (A := reindex I.domain (pair (𝟙 Ξ) (I.selectedLabel z)))
    (B := reindex I.paths (liftSub I.domain (pair (𝟙 Ξ) (I.selectedLabel z)))) (sigmaSnd z)

def selectedNativePath (z : Term I.outer) :
    Term (homogeneousPath (reindex (liftedDecode (I.display ≫ I.Y)) (I.selectedDisplay z))
      (I.target.reindex (I.selectedDisplay z)) (I.weakenedEndpoint.reindex (I.selectedDisplay z))) :=
  Term.map (pathReindexIso (liftedDecode I.pathBody) I.target I.weakenedEndpoint
    (I.selectedDisplay z)).hom (I.selectedPath z)

noncomputable def pathResult : LargeConstructors.Result I.paths :=
  LargeConstructors.path I.pathBody I.target I.weakenedEndpoint

noncomputable def pathPresentation : SmallPresentation.Data I.paths :=
  SmallPresentation.Data.path _ (decodePresentation I.pathBody) I.target I.weakenedEndpoint

noncomputable def pathFiller : Filling I.paths :=
  pathFilling (NativeDecode.filling I.pathBody) (NativeDecode.filling_lawful _) I.target I.weakenedEndpoint

theorem pathFiller_lawful : I.pathFiller.Lawful := pathFilling_lawful _ (NativeDecode.filling_lawful _) _ _

noncomputable def innerPresentation : SmallPresentation.Data I.inner :=
  (decodePresentation I.D).sigma I.pathPresentation
noncomputable def innerFiller : Filling I.inner :=
  sigmaFilling (NativeDecode.filling I.D) (NativeDecode.filling_lawful _) I.pathFiller

theorem innerFiller_lawful : I.innerFiller.Lawful :=
  sigmaFilling_lawful _ (NativeDecode.filling_lawful _) _ I.pathFiller_lawful

noncomputable def innerResult : LargeConstructors.Result I.inner :=
  LargeConstructors.construct I.innerPresentation I.innerFiller I.innerFiller_lawful

/-- The stock code constructor also composes, with its own selected filler.
Its second provider is the universal decoder of the returned Path code. -/
noncomputable def encodedInner := LargeConstructors.sigma I.D I.pathResult.code

noncomputable def encodedInnerDecoding : liftedDecode I.encodedInner.code ≅ I.inner :=
  I.encodedInner.decoding ≪≫ sigmaSecondIso _ I.pathResult.decoding

theorem encodedInner_selected :
    I.encodedInner.filling.transport I.encodedInnerDecoding =
      sigmaFilling (NativeDecode.filling I.D) (NativeDecode.filling_lawful _)
        ((NativeDecode.filling I.pathResult.code).transport I.pathResult.decoding) := by
  rw [encodedInnerDecoding, ← Filling.transport_trans]
  change ((LargeConstructors.construct _ _ _).filling.transport
    (LargeConstructors.construct _ _ _).decoding).transport _ = _
  rw [LargeConstructors.construct_filling, sigmaFilling_transport_second]

noncomputable def outerFiller : Filling I.outer :=
  sigmaFilling (labelFilling I.count) (labelFilling_lawful _) I.innerFiller

theorem outerFiller_lawful : I.outerFiller.Lawful :=
  sigmaFilling_lawful _ (labelFilling_lawful _) _ I.innerFiller_lawful

noncomputable def outerResult : LargeConstructors.Result I.outer :=
  LargeConstructors.construct ((labelPresentation I.count).sigma I.innerPresentation)
    I.outerFiller I.outerFiller_lawful

theorem path_selected : I.pathResult.filling.transport I.pathResult.decoding = I.pathFiller :=
  LargeConstructors.construct_filling _ _ _
theorem inner_selected : I.innerResult.filling.transport I.innerResult.decoding = I.innerFiller :=
  LargeConstructors.construct_filling _ _ _
theorem outer_selected : I.outerResult.filling.transport I.outerResult.decoding = I.outerFiller :=
  LargeConstructors.construct_filling _ _ _

abbrev labelLift (σ : Ω ⟶ Ξ) := liftSub (labels I.count) σ
abbrev domainLift (σ : Ω ⟶ Ξ) := liftSub I.domain (I.labelLift σ)

def substitute (σ : Ω ⟶ Ξ) : Inputs Ω where
  count := I.count.reindex σ
  Y := σ ≫ I.Y
  D := I.labelLift σ ≫ I.D
  target := I.target.reindex (I.domainLift σ)
  endpoint := I.endpoint.reindex σ

noncomputable def pathSubstitution (σ : Ω ⟶ Ξ) :
    reindex I.paths (I.domainLift σ) ≅ (I.substitute σ).paths :=
  pathReindexIso _ _ _ (I.domainLift σ)
noncomputable def innerSubstitution (σ : Ω ⟶ Ξ) :
    reindex I.inner (I.labelLift σ) ≅ (I.substitute σ).inner :=
  sigmaSecondIso _ (I.pathSubstitution σ)
noncomputable def outerSubstitution (σ : Ω ⟶ Ξ) :
    reindex I.outer σ ≅ (I.substitute σ).outer :=
  sigmaSecondIso _ (I.innerSubstitution σ)

theorem pathFiller_substitution (σ : Ω ⟶ Ξ) :
    (I.pathFiller.reindex (I.domainLift σ)).transport (I.pathSubstitution σ) =
      (I.substitute σ).pathFiller :=
  pathFilling_reindex_iso _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem innerFiller_substitution (σ : Ω ⟶ Ξ) :
    (I.innerFiller.reindex (I.labelLift σ)).transport (I.innerSubstitution σ) =
      (I.substitute σ).innerFiller := by
  change (sigmaFilling ((NativeDecode.filling I.D).reindex (I.labelLift σ))
    ((NativeDecode.filling_lawful I.D).reindex (I.labelLift σ))
    (I.pathFiller.reindex (I.domainLift σ))).transport
    (sigmaSecondIso _ (I.pathSubstitution σ)) = _
  rw [sigmaFilling_transport_second, pathFiller_substitution]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem outerFiller_substitution (σ : Ω ⟶ Ξ) :
    (I.outerFiller.reindex σ).transport (I.outerSubstitution σ) =
      (I.substitute σ).outerFiller := by
  change (sigmaFilling ((labelFilling I.count).reindex σ)
    ((labelFilling_lawful I.count).reindex σ)
    (I.innerFiller.reindex (I.labelLift σ))).transport
    (sigmaSecondIso _ (I.innerSubstitution σ)) = _
  rw [sigmaFilling_transport_second, innerFiller_substitution]
  rfl

noncomputable def innerComparison (σ : Ω ⟶ Ξ) :
    liftedDecode (I.labelLift σ ≫ I.innerResult.code) ≅
      liftedDecode (I.substitute σ).innerResult.code :=
  Functor.isoWhiskerLeft (I.labelLift σ).mapElements I.innerResult.decoding ≪≫
    I.innerSubstitution σ ≪≫ (I.substitute σ).innerResult.decoding.symm

noncomputable def outerComparison (σ : Ω ⟶ Ξ) :
    liftedDecode (σ ≫ I.outerResult.code) ≅ liftedDecode (I.substitute σ).outerResult.code :=
  Functor.isoWhiskerLeft σ.mapElements I.outerResult.decoding ≪≫
    I.outerSubstitution σ ≪≫ (I.substitute σ).outerResult.decoding.symm

set_option backward.isDefEq.respectTransparency false in
private theorem selectedComparison {Γ Δ : Context.{u+1}} {A : Family Γ} {B : Family Δ}
    (P : SmallPresentation.Data A) (F : Filling A) (hF : F.Lawful)
    (Q : SmallPresentation.Data B) (G : Filling B) (hG : G.Lawful)
    (σ : Δ ⟶ Γ) (e : reindex A σ ≅ B) (h : (F.reindex σ).transport e = G) :
    ((LargeConstructors.construct P F hF).filling.reindex σ).transport
      (Functor.isoWhiskerLeft σ.mapElements (LargeConstructors.construct P F hF).decoding ≪≫
        e ≪≫ (LargeConstructors.construct Q G hG).decoding.symm) =
      (LargeConstructors.construct Q G hG).filling := by
  let d := Functor.isoWhiskerLeft σ.mapElements (P.nativeIso F hF)
  let c := Q.nativeIso G hG
  change ((F.reindex σ).transport d.symm).transport (d ≪≫ e ≪≫ c.symm) = G.transport c.symm
  calc
    _ = (F.reindex σ).transport (e ≪≫ c.symm) := by
      rw [Filling.transport_trans]
      congr 1
      simp
    _ = ((F.reindex σ).transport e).transport c.symm := rfl
    _ = G.transport c.symm := congrArg (fun H => H.transport c.symm) h

theorem innerComparison_filling (σ : Ω ⟶ Ξ) :
    (I.innerResult.filling.reindex (I.labelLift σ)).transport (I.innerComparison σ) =
      (I.substitute σ).innerResult.filling :=
  selectedComparison _ _ _ _ _ _ _ _ (I.innerFiller_substitution σ)

theorem outerComparison_filling (σ : Ω ⟶ Ξ) :
    (I.outerResult.filling.reindex σ).transport (I.outerComparison σ) =
      (I.substitute σ).outerResult.filling :=
  selectedComparison _ _ _ _ _ _ _ _ (I.outerFiller_substitution σ)

end Inputs
end SquareKit.Cubical.Presheaf.SmallUniverse.ChartFamily
