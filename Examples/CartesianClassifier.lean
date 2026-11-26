import Examples.CartesianFilling
import Examples.CartesianPackageRecomputation
import SquareKit.Internal.Cubical.CartesianClassifierComparison
import SquareKit.Internal.Cubical.CartesianPiFilling
import SquareKit.Internal.Cubical.CartesianUnivalence
import SquareKit.Internal.Cubical.CartesianEquivalenceComposition

/-! Checked dependent constructors and finite classifier comparisons over Cartesian
contexts. The examples retain chosen operations, actual ua concatenation, and
the faces of the independent and aligned higher comparisons. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.ClassifierExamples
open CategoryTheory SquareKit.Cubical.Cartesian
universe u

abbrev tags (Γ : Context.{u}) := constantFamily Γ (ULift.{u} Bool)

def branch (Γ : Context.{u}) : Family (total (tags Γ)) where
  obj x := ULift.{u} (Fin (if x.val.2.down then 2 else 1))
  map f := eqToHom (congrArg (fun b => ULift.{u} (Fin (if b.down then 2 else 1)))
    ((generic (tags Γ)).property f))
  map_id _ := rfl
  map_comp _ _ := (eqToHom_trans _ _).symm

theorem branch_restrictions (Γ : Context.{u}) : BijectiveRestrictions (branch Γ) := by
  intro x y f
  exact (eqToIso (congrArg (fun b => ULift.{u} (Fin (if b.down then 2 else 1)))
    ((generic (tags Γ)).property f))).toEquiv.bijective

def tagFilling (Γ : Context.{u}) : Filling (tags Γ) := presentedFilling (Iso.refl _)
theorem tagFilling_lawful (Γ : Context.{u}) : (tagFilling Γ).Lawful := presentedFilling_lawful _

noncomputable def sumFilling (Γ : Context.{u}) : Filling (sigma (tags Γ) (branch Γ)) :=
  sigmaFilling (tagFilling Γ) (tagFilling_lawful Γ) (bijectiveFilling (branch_restrictions Γ))

theorem sumFilling_lawful (Γ : Context.{u}) : (sumFilling Γ).Lawful :=
  sigmaFilling_lawful _ (tagFilling_lawful Γ) _ (bijectiveFilling_lawful (branch_restrictions Γ))

noncomputable def functionFilling (Γ : Context.{u}) : Filling (pi (tags Γ) (branch Γ)) :=
  piFilling (tagFilling Γ) (tagFilling_lawful Γ) (bijectiveFilling (branch_restrictions Γ))

theorem functionFilling_lawful (Γ : Context.{u}) : (functionFilling Γ).Lawful :=
  piFilling_lawful _ (tagFilling_lawful Γ) _ (bijectiveFilling_lawful (branch_restrictions Γ))

/-- Even a variable source agrees with its cap on every source=target face. -/
theorem dependent_function_diagonal {Γ Δ : Context.{u}}
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r s : Term (interval Δ))
    (b : OpenBox (reindex (pi (tags Γ) (branch Γ)) p) φ r) (x : Δ.Elements)
    (h : r.val x = s.val x) :
    HEq (((functionFilling Γ).comp p φ r s b).val x) (b.base.val x) :=
  Filling.comp_diagonal (functionFilling_lawful Γ) p φ r s b x h

/-- Arbitrary context substitutions retain the chosen dependent-sum operation. -/
theorem dependent_sum_substitution {Γ Δ Θ : Context.{u}}
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (sigma (tags Γ) (branch Γ)) p) φ r) (σ : Θ ⟶ Δ) :
    (sumFilling Γ).fill (intervalSub σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ) =
      Term.reindex ((sumFilling Γ).fill p φ r b) (intervalSub σ) :=
  (sumFilling_lawful Γ).uniform p φ r b σ

noncomputable def branchLoopFilling (Γ : Context.{u}) :
    Filling (homogeneousPath (reindex (branch Γ) (projection (branch Γ)))
      (generic (branch Γ)) (generic (branch Γ))) :=
  pathFilling ((bijectiveFilling (branch_restrictions Γ)).reindex
    (projection (interval (total (branch Γ))) ≫ projection (branch Γ)))
    ((bijectiveFilling_lawful (branch_restrictions Γ)).reindex _) _ _

theorem branchLoopFilling_lawful (Γ : Context.{u}) : (branchLoopFilling Γ).Lawful :=
  pathFilling_lawful _ ((bijectiveFilling_lawful (branch_restrictions Γ)).reindex _) _ _

theorem false_branch {Γ : Context.{u}} (x : Γ.Elements) :
    (branch Γ).obj (extendObj (tags Γ) x ⟨false⟩) = ULift.{u} (Fin 1) := rfl

theorem true_branch {Γ : Context.{u}} (x : Γ.Elements) :
    (branch Γ).obj (extendObj (tags Γ) x ⟨true⟩) = ULift.{u} (Fin 2) := rfl

def swapTags (Γ : Context.{u}) : tags Γ ≅ tags Γ where
  hom := { app := fun _ => TypeCat.ofHom (fun b => ⟨!b.down⟩), naturality := fun _ _ _ => rfl }
  inv := { app := fun _ => TypeCat.ofHom (fun b => ⟨!b.down⟩), naturality := fun _ _ _ => rfl }
  hom_inv_id := by ext x b; cases b with | up b => cases b <;> rfl
  inv_hom_id := by ext x b; cases b with | up b => cases b <;> rfl

noncomputable def swapEquivalence (Γ : Context.{u}) : HomotopyEquivalence (swapTags Γ).hom :=
  HomotopyEquivalence.ofIso (swapTags Γ) (tagFilling Γ) (tagFilling_lawful Γ)

noncomputable def swapViaComposition (Γ : Context.{u}) : HomotopyEquivalence (swapTags Γ).hom :=
  (HomotopyEquivalence.identity (tagFilling Γ) (tagFilling_lawful Γ)).comp (swapEquivalence Γ)
    (tagFilling Γ) (tagFilling_lawful Γ) (tagFilling Γ) (tagFilling_lawful Γ)
    (tagFilling Γ) (tagFilling_lawful Γ)

noncomputable def swapWitnessComparison (Γ : Context.{u}) : Term (homogeneousPath
    (EquivalenceFamilies.isEquiv (swapTags Γ).hom)
    (EquivalenceFamilies.encodeIsEquiv (swapEquivalence Γ))
    (EquivalenceFamilies.encodeIsEquiv (swapViaComposition Γ))) :=
  EquivalenceFamilies.isEquivPath _ (tagFilling Γ) (tagFilling_lawful Γ)
    (tagFilling Γ) (tagFilling_lawful Γ) _ _

noncomputable def tagRecord (Γ : Context.{u}) : LocalFamily Γ :=
  LocalFamily.ofFilling (tags Γ) (tagFilling Γ) (tagFilling_lawful Γ)

noncomputable def swapCodeLoop (Γ : Context.{u}) : Term (homogeneousPath
    (SmallUniverse.family (raisedContext Γ))
    (SmallUniverse.term (tagRecord Γ).code) (SmallUniverse.term (tagRecord Γ).code)) :=
  NativeUa.path (tagRecord Γ) (tagRecord Γ) (swapTags Γ).hom (swapEquivalence Γ)

theorem swap_true {Γ : Context.{u}} (x : Γ.Elements) :
    (swapTags Γ).hom.app x ⟨true⟩ = ⟨false⟩ := rfl


open ClassifierComparison
abbrev finiteBool : FiniteCode := ⟨Bool, inferInstance⟩
abbrev finiteThree : FiniteCode := ⟨Fin 3, inferInstance⟩
def swap01 : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
def swap12 : Fin 3 ≃ Fin 3 := Equiv.swap 1 2
example : Selected.action finiteBool (Equiv.refl Bool) false = false :=
  Selected.action_eq _ _ _
example : Selected.action finiteBool (Equiv.swap false true) false = true := by
  rw [Selected.action_eq]
  decide
example : Selected.action finiteThree (swap01.trans swap12) 0 = 2 := by
  rw [Selected.action_eq]
  decide
example : Selected.action finiteThree (swap12.trans swap01) 0 = 1 := by
  rw [Selected.action_eq]
  decide
example : Selected.action finiteThree (swap01.trans swap12) 0 ≠
    Selected.action finiteThree (swap12.trans swap01) 0 := by
  simp only [Selected.action_eq]
  decide

end SquareKit.Cubical.Cartesian.ClassifierExamples

namespace SquareKit.Cubical.Cartesian.ClassifierExamples.Package
open CategoryTheory
open Examples.CartesianPackageRecomputation
open Examples.CartesianWitnessPreservation
open Examples.CubicalStateTransport

noncomputable def carrier : LocalFamily
    (total (interval (restrict Presheaf.terminal))) :=
  ⟨selectedCarrier, (presentedFilling selectedPresentation).toLocal,
    Filling.toLocal_lawful (presentedFilling_lawful selectedPresentation)⟩

noncomputable abbrev decoder := decode carrier.code
noncomputable def presentation := carrier.decodeCodeIso ≪≫ selectedPresentation

/-- Recompute all five fields on the classified carrier, using its full decoder
presentation at every generalized argument. -/
noncomputable def classified : Term (packageFamily decoder) :=
  recomputed presentation (endpointTerm (restrict Presheaf.terminal) false) selectedHostPackage

noncomputable def adapter : packageFamily decoder ≅ packageFamily selectedCarrier :=
  packagePresentation presentation ≪≫ (packagePresentation selectedPresentation).symm

theorem adapter_pull {Γ : Context} {A B : Family Γ} {S : Type}
    (e : A ≅ constantFamily Γ S) (d : B ≅ constantFamily Γ S) (p : StatePackage S) :
    Term.map ((packagePresentation e ≪≫ (packagePresentation d).symm).hom)
      (pullTargetPackage e p) = pullTargetPackage d p := by
  apply Term.ext
  intro x
  change fromConstant d x (toConstant e x (fromConstant e x p)) = fromConstant d x p
  rw [to_from]

/-- The complete original package is recovered, including generalized step and
invariant fields and both dependent proofs. -/
theorem full_package : Term.map adapter.hom classified = recomputedSelected := by
  rw [classified, recomputed_eq, recomputedSelected, recomputed_eq]
  exact adapter_pull presentation selectedPresentation selectedHostPackage

theorem original_package (x : (total (interval (restrict Presheaf.terminal))).Elements) :
    (Term.map adapter.hom classified).val x = cartesianPackage x :=
  (congrArg (fun t => t.val x) full_package).trans (recomputedSelected_eq x)

theorem selected_operation : decodedLocalFamily carrier.code = carrier := carrier.decodeCode_record

theorem full_package_reindex {Δ : Context} (σ : Δ ⟶ total (interval (restrict Presheaf.terminal))) :
    Term.reindex (Term.map adapter.hom classified) σ = Term.reindex recomputedSelected σ :=
  congrArg (fun t => Term.reindex t σ) full_package
end SquareKit.Cubical.Cartesian.ClassifierExamples.Package

namespace SquareKit.Cubical.Cartesian.ClassifierExamples.FiniteSpan
open CategoryTheory ClassifierComparison
open Examples.FiniteUniverseLoops
abbrev finiteThree : FiniteCode := ⟨Fin 3, inferInstance⟩

/-- The same finite square mediates both realizations. -/
def commonT := VertexSystem.compositionSquare finiteThree swap01 swap12

theorem commonT_selected : commonT = VertexSystem.compositionSquare finiteThree
    (Selected.arrow finiteThree swap01) (Selected.arrow finiteThree swap12) := by
  rw [Selected.arrow_eq, Selected.arrow_eq]
  rfl

/-- Keep the exact original source witness and its existing comparison leg. -/
noncomputable abbrev originalH := Examples.FiniteUniverseLoops.swapComposition
noncomputable abbrev omegaR := Examples.CartesianSelectedRecomputation.relativeThreePath
noncomputable abbrev sourceAligned := Examples.CartesianSelectedRecomputation.recomputedSquare

theorem omegaR_original : Presheaf.Term.reindex (Presheaf.pathApp omegaR)
    (Presheaf.endpointSub _ false) = originalH :=
  Examples.CartesianSelectedRecomputation.relativeThreePath_zero

theorem omegaR_aligned : Presheaf.Term.reindex (Presheaf.pathApp omegaR)
    (Presheaf.endpointSub _ true) = sourceAligned :=
  Examples.CartesianSelectedRecomputation.relativeThreePath_one

noncomputable def classifiedT := NativeNerve.realizedComposition finiteThree swap01 swap12

theorem classifiedT_body : RelativeComparison.squareBody classifiedT =
    SmallUniverse.term (NativeNerve.compositionNerve _ finiteThree swap01 swap12 ≫ classifyFinite) :=
  NativeNerve.realizedComposition_body _ _ _

theorem sourceT_body :
    Presheaf.SmallUniverse.NativeUnivalence.comparisonSquare
      (RealizedNerve.realizedComposition finiteThree swap01 swap12) =
      Presheaf.SmallUniverse.term (compositionNerve _ finiteThree swap01 swap12 ≫ realizeDM) :=
  RealizedNerve.realizedComposition_body _ _ _

/-- Restriction retains the original relative three-path itself, not merely its
observed endpoint permutation. -/
noncomputable def restrictedOmegaR := restrictTerm omegaR

theorem omegaR_comp {Δ Θ : Presheaf.Context.{1}}
    (σ : Δ ⟶ Presheaf.raisedContext Presheaf.terminal) (τ : Θ ⟶ Δ) :
    Presheaf.RelativeComparison.SquareSubstitutionLaw omegaR σ τ :=
  Examples.CartesianSelectedRecomputation.relativeAt_comp σ τ
theorem native_commonT {Γ : Context.{1}} {I : Cubeᵒᵖ}
    (x : (total (interval (total (interval Γ)))).obj I) :
    (NativeNerve.compositionNerve Γ finiteThree swap01 swap12).app I x =
      commonT.reindex (Cube.vertices (Cube.pair x.2.down x.1.2.down)) := rfl

theorem source_commonT {Γ : Presheaf.Context.{1}} {I : SquareKit.Cubical.Cubeᵒᵖ}
    (x : (Presheaf.total (Presheaf.interval (Presheaf.total (Presheaf.interval Γ)))).obj I) :
    (compositionNerve Γ finiteThree swap01 swap12).app I x =
      commonT.reindex (dmVertices (SquareKit.Cubical.Cube.pair x.2.down x.1.2.down)) := rfl

end SquareKit.Cubical.Cartesian.ClassifierExamples.FiniteSpan

namespace SquareKit.Cubical.Cartesian.ClassifierExamples
open CategoryTheory ClassifierComparison

theorem native_bool_separation :
    NativeNerve.uaLoop finiteBool (Equiv.swap false true) ≠ NativeNerve.uaLoop finiteBool (Equiv.refl Bool) := by
  intro h
  have h₀ := congrArg (fun e : Bool ≃ Bool => e false) (NativeNerve.uaLoop_injective finiteBool h)
  change true = false at h₀
  cases h₀

theorem native_noncommuting_orders :
    NativeNerve.uaConcatenation finiteThree swap01 swap12 ≠ NativeNerve.uaConcatenation finiteThree swap12 swap01 := by
  intro h
  have h₀ := congrArg (fun e : Fin 3 ≃ Fin 3 => e 0)
    (NativeNerve.uaConcatenation_order finiteThree swap01 swap12 h)
  change (2 : Fin 3) = 1 at h₀
  exact (by decide : (2 : Fin 3) ≠ 1) h₀

namespace FiniteSpan
noncomputable abbrev nativeH := NativeComparison.selectedPath finiteThree
  Examples.FiniteUniverseLoops.swap01 Examples.FiniteUniverseLoops.swap12
noncomputable abbrev nativeReverseH := NativeComparison.selectedPath finiteThree
  Examples.FiniteUniverseLoops.swap12 Examples.FiniteUniverseLoops.swap01
noncomputable abbrev alignmentL := NativeComparison.alignmentL finiteThree
  Examples.FiniteUniverseLoops.swap01 Examples.FiniteUniverseLoops.swap12
noncomputable abbrev omegaU := NativeComparison.omegaU finiteThree
  Examples.FiniteUniverseLoops.swap01 Examples.FiniteUniverseLoops.swap12

/-- The native target witness connects ua of the chosen composite to actual path concatenation. -/
theorem nativeH_source : Term.reindex (pathApp nativeH) (endpointSub _ false) =
    NativeNerve.uaComposite finiteThree Examples.FiniteUniverseLoops.swap01 Examples.FiniteUniverseLoops.swap12 :=
  pathApp_zero _
theorem nativeH_target : Term.reindex (pathApp nativeH) (endpointSub _ true) =
    NativeNerve.uaConcatenation finiteThree Examples.FiniteUniverseLoops.swap01 Examples.FiniteUniverseLoops.swap12 :=
  pathApp_one _
theorem omegaU_independent : Term.reindex (pathApp omegaU) (endpointSub _ false) = nativeH := pathApp_zero _
theorem alignment_commonT : Term.reindex alignmentL (endpointSub (total (interval (raisedContext NativeNerve.point))) false) =
    pathApp classifiedT := NativeComparison.alignment_original _ _ _
example : RelativeComparison.SquareSubstitutionLaw omegaU
    (𝟙 (raisedContext NativeNerve.point)) (𝟙 (raisedContext NativeNerve.point)) :=
  RelativeComparison.squareSubstitutionLaw _ _ _
end FiniteSpan
end SquareKit.Cubical.Cartesian.ClassifierExamples
