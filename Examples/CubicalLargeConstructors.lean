import SquareKit.Internal.Cubical.ConstructorTransport
import Examples.CubicalSmallFamilies
import Examples.CubicalStatePackageUa

/-! Larger-context constructor clients, retaining the whole-package ua regression.
The context contains a natural parameter and a generic small-universe code. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalLargeConstructors
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SmallUniverse
open CubicalPresheaf

abbrev base : Context.{1} := raisedContext naturals
abbrev context : Context.{1} := total (SmallUniverse.family base)
def baseProjection : context ⟶ base := projection (SmallUniverse.family base)
def parameter : context ⟶ smallFamilyCodes.{0} := SmallUniverse.code (generic (SmallUniverse.family base))

/-- The domain may itself be the generic universe parameter. -/
noncomputable def genericSum := LargeConstructors.sigma parameter (projection (liftedDecode parameter) ≫ parameter)
noncomputable def genericProduct := LargeConstructors.pi parameter (projection (liftedDecode parameter) ≫ parameter)

def naturalsCode : context ⟶ smallFamilyCodes.{0} := baseProjection ≫ CubicalSmallFamilies.natCode

def dependentDisplay : total (liftedDecode naturalsCode) ⟶ raisedContext (total (Presheaf.decode CubicalSmallFamilies.natCode)) :=
  liftSub (Raising.family (Presheaf.decode CubicalSmallFamilies.natCode)) baseProjection ≫
    (Raising.totalIso (Presheaf.decode CubicalSmallFamilies.natCode)).inv

def varyingCode : total (liftedDecode naturalsCode) ⟶ smallFamilyCodes.{0} :=
  dependentDisplay ≫ CubicalSmallFamilies.dependentCode

noncomputable def sum := LargeConstructors.sigma naturalsCode varyingCode
noncomputable def product := LargeConstructors.pi naturalsCode varyingCode

def successorSub : context ⟶ context :=
  liftSub (SmallUniverse.family base) (raisedSub successor)
def twiceSub : context ⟶ context :=
  liftSub (SmallUniverse.family base) (raisedSub twice)

def point (n : Nat) : context.Elements := context.elementsMk (Opposite.op ⟨0⟩)
  ⟨⟨n⟩, (CubicalSmallFamilies.natCode.app (Opposite.op ⟨0⟩) ⟨(0 : Nat)⟩)⟩

theorem successor_nonidentity : successorSub ≠ 𝟙 context := by
  intro h
  have e := congrArg (fun f : context ⟶ context => (f.app (Opposite.op ⟨0⟩) (point 0).val).1.down) h
  cases e

theorem twice_nonidentity : twiceSub ≠ 𝟙 context := by
  intro h
  have e := congrArg (fun f : context ⟶ context => (f.app (Opposite.op ⟨0⟩) (point 1).val).1.down) h
  cases e

def atArgument (n : Nat) : (total (liftedDecode naturalsCode)).Elements :=
  extendObj (liftedDecode naturalsCode) (point 0) ⟨n⟩

def varyingFiber (n : Nat) : (liftedDecode varyingCode).obj (atArgument n) ≃ Fin (n+1) :=
  Equiv.ulift.trans ((CubicalSmallFamilies.dependentDecode.app (CubicalSmallFamilies.atArgument n)).toEquiv)

theorem varying_fibers : ¬ Nonempty
    ((liftedDecode varyingCode).obj (atArgument 0) ≃ (liftedDecode varyingCode).obj (atArgument 1)) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr ((varyingFiber 0).symm.trans (e.trans (varyingFiber 1)))
  simp at h

noncomputable def sumSuccessor := LargeConstructors.sigmaSubstitution naturalsCode varyingCode successorSub
noncomputable def sumTwice := LargeConstructors.sigmaSubstitution naturalsCode varyingCode twiceSub
noncomputable def sumComposite := LargeConstructors.sigmaSubstitution naturalsCode varyingCode (twiceSub ≫ successorSub)
noncomputable def productSuccessor := LargeConstructors.piSubstitution naturalsCode varyingCode successorSub
noncomputable def productTwice := LargeConstructors.piSubstitution naturalsCode varyingCode twiceSub
noncomputable def productComposite := LargeConstructors.piSubstitution naturalsCode varyingCode (twiceSub ≫ successorSub)

example : (sum.filling.reindex (twiceSub ≫ successorSub)).transport sumComposite =
    (LargeConstructors.sigma ((twiceSub ≫ successorSub) ≫ naturalsCode)
      (liftSub (liftedDecode naturalsCode) (twiceSub ≫ successorSub) ≫ varyingCode)).filling :=
  LargeConstructors.sigmaSubstitution_filling _ _ _

example : (product.filling.reindex (twiceSub ≫ successorSub)).transport productComposite =
    (LargeConstructors.pi ((twiceSub ≫ successorSub) ≫ naturalsCode)
      (liftSub (liftedDecode naturalsCode) (twiceSub ≫ successorSub) ≫ varyingCode)).filling :=
  LargeConstructors.piSubstitution_filling _ _ _

/-- A separate base-indexed family makes the change under substitutions observable. -/
def countCode : context ⟶ smallFamilyCodes.{0} := baseProjection ≫ CubicalSmallFamilies.selectedCode
noncomputable def countSum := LargeConstructors.sigma countCode (projection (liftedDecode countCode) ≫ parameter)

def countFiber (n : Nat) : (liftedDecode countCode).obj (point n) ≃ Fin (n+1) :=
  Equiv.ulift.trans ((CubicalSmallFamilies.selectedDecode.app (naturals.elementsMk (Opposite.op ⟨0⟩) n)).toEquiv)

def successorCountFiber : (liftedDecode (successorSub ≫ countCode)).obj (point 2) ≃ Fin 4 := countFiber 3
def twiceCountFiber : (liftedDecode (twiceSub ≫ countCode)).obj (point 2) ≃ Fin 5 := countFiber 4
def compositeCountFiber : (liftedDecode (twiceSub ≫ successorSub ≫ countCode)).obj (point 2) ≃ Fin 6 := countFiber 5

noncomputable def countSumSuccessor := LargeConstructors.sigmaSubstitution countCode
  (projection (liftedDecode countCode) ≫ parameter) successorSub
noncomputable def countSumTwice := LargeConstructors.sigmaSubstitution countCode
  (projection (liftedDecode countCode) ≫ parameter) twiceSub
noncomputable def countSumComposite := LargeConstructors.sigmaSubstitution countCode
  (projection (liftedDecode countCode) ≫ parameter) (twiceSub ≫ successorSub)

def suppliedPath : Term (NativeUnivalence.paths naturalsCode naturalsCode) :=
  homogeneousRefl (SmallUniverse.term naturalsCode)

def suppliedDependentCode : total (liftedDecode (LargeConstructors.inputLine suppliedPath)) ⟶ smallFamilyCodes.{0} :=
  liftSub (liftedDecode naturalsCode) (projection (interval context)) ≫ varyingCode

/-- These clients take actual initial dependent values and return native paths
for transport, rather than assuming either transport comparison. -/
noncomputable def pairClient
    (z : Term (Presheaf.sigma (liftedDecode naturalsCode) (liftedDecode varyingCode))) :=
  LargeConstructors.pairAlongPath suppliedPath suppliedDependentCode z

noncomputable def functionClient
    (z : Term (Presheaf.pi (liftedDecode naturalsCode) (liftedDecode varyingCode))) :=
  LargeConstructors.functionAlongPath suppliedPath suppliedDependentCode
    (Term.map (piReindexIso (liftedDecode (LargeConstructors.inputLine suppliedPath))
      (liftedDecode suppliedDependentCode) (endpointSub context false)).inv z)

def emptyCode : context ⟶ smallFamilyCodes.{0} :=
  baseProjection ≫ discreteCode (CubicalSmallFamilies.unitIndex naturals) (fun _ => Empty)

def emptyFiber (x : context.Elements) : (liftedDecode emptyCode).obj x ≃ Empty :=
  Equiv.ulift.trans ((discreteCodeDecodeIso (CubicalSmallFamilies.unitIndex naturals)
    (fun _ => Empty)).app ((Raising.lowerElements naturals).obj (baseProjection.mapElements.obj x))).toEquiv

noncomputable def emptySum := LargeConstructors.sigma emptyCode
  (projection (liftedDecode emptyCode) ≫ parameter)

/-- A decoder equivalence cannot create inhabitants of an empty domain. -/
theorem empty_sum_rejected (x : context.Elements) : IsEmpty ((liftedDecode emptySum.code).obj x) :=
  ⟨fun z => Empty.elim (emptyFiber x ((emptySum.decoding.hom.app x z).1))⟩

noncomputable def emptyProduct := LargeConstructors.pi emptyCode
  (projection (liftedDecode emptyCode) ≫ emptyCode)

def emptyBody : Term (liftedDecode (projection (liftedDecode emptyCode) ≫ emptyCode)) where
  val x := Empty.elim (emptyFiber ((projection (liftedDecode emptyCode)).mapElements.obj x) x.val.2)
  property {x} _ := Empty.elim (emptyFiber ((projection (liftedDecode emptyCode)).mapElements.obj x) x.val.2)

noncomputable def emptyFunction : Term (liftedDecode emptyProduct.code) :=
  Term.map emptyProduct.decoding.inv (lam emptyBody)

theorem emptyFunction_unique (z : Term (liftedDecode emptyProduct.code)) : z = emptyFunction := by
  apply Term.map_injective_of_iso emptyProduct.decoding
  apply Term.ext
  intro x
  apply PiElement.ext
  intro y f a
  exact Empty.elim (emptyFiber y a)

def constantNatural (n : Nat) : Term (constantFamily naturals Nat) where
  val _ := n
  property _ := rfl

def naturalSection (n : Nat) : Term (liftedDecode naturalsCode) :=
  (Raising.raiseTerm (Term.map CubicalSmallFamilies.natDecode.inv (constantNatural n))).reindex baseProjection

def observeNatural : liftedDecode naturalsCode ⟶ constantFamily context (ULift.{1} Nat) :=
  Functor.whiskerLeft baseProjection.mapElements (Raising.map CubicalSmallFamilies.natDecode.hom)

noncomputable def incompatiblePath := LargeConstructors.path
  (projection (interval context) ≫ naturalsCode) (naturalSection 0) (naturalSection 1)

theorem incompatible_endpoints_rejected : ¬ Nonempty (Term (liftedDecode incompatiblePath.code)) := by
  rintro ⟨z⟩
  have q := Term.map incompatiblePath.decoding.hom z
  have h := discretePath_endpoints (homogeneousPathMap observeNatural q)
  have e := congrArg (fun t => (t.val (point 0)).down) h
  change (CubicalSmallFamilies.natDecode.hom.app _
      (CubicalSmallFamilies.natDecode.inv.app _ (0 : Nat))) =
    (CubicalSmallFamilies.natDecode.hom.app _
      (CubicalSmallFamilies.natDecode.inv.app _ (1 : Nat))) at e
  have h₀ := congrArg (fun k => k.app (naturals.elementsMk (Opposite.op ⟨0⟩) (0 : Nat)) (0 : Nat))
    CubicalSmallFamilies.natDecode.inv_hom_id
  have h₁ := congrArg (fun k => k.app (naturals.elementsMk (Opposite.op ⟨0⟩) (0 : Nat)) (1 : Nat))
    CubicalSmallFamilies.natDecode.inv_hom_id
  exact Nat.zero_ne_one (h₀.symm.trans (e.trans h₁))

noncomputable def pathSuccessor := LargeConstructors.pathSubstitution
  (projection (interval context) ≫ naturalsCode) (naturalSection 0) (naturalSection 1) successorSub
noncomputable def pathTwice := LargeConstructors.pathSubstitution
  (projection (interval context) ≫ naturalsCode) (naturalSection 0) (naturalSection 1) twiceSub
noncomputable def pathComposite := LargeConstructors.pathSubstitution
  (projection (interval context) ≫ naturalsCode) (naturalSection 0) (naturalSection 1) (twiceSub ≫ successorSub)

def smallLast : Term (discreteFamily CubicalSmallFamilies.argument (fun n => Fin (n+1))) where
  val x := Fin.last (CubicalSmallFamilies.argument.val x)
  property f := CubicalDiscreteFilling.cast_last _ _ (CubicalSmallFamilies.argument.property f)

def dependentLast : Term (liftedDecode varyingCode) :=
  (Raising.raiseTerm (Term.map CubicalSmallFamilies.dependentDecode.inv smallLast)).reindex dependentDisplay

def initialPair : Term (Presheaf.sigma (liftedDecode naturalsCode) (liftedDecode varyingCode)) :=
  sigmaIntro (naturalSection 0) (dependentLast.reindex (pair (𝟙 context) (naturalSection 0)))

def initialFunction : Term (Presheaf.pi (liftedDecode naturalsCode) (liftedDecode varyingCode)) := lam dependentLast

noncomputable def checkedPairTransport := pairClient initialPair
noncomputable def checkedFunctionTransport := functionClient initialFunction

noncomputable def reflexivePath := LargeConstructors.path
  (projection (interval context) ≫ naturalsCode) (naturalSection 0) (naturalSection 0)
noncomputable def reflexivePathSection : Term (liftedDecode reflexivePath.code) :=
  Term.map reflexivePath.decoding.inv (homogeneousRefl (naturalSection 0))

/-- Full equivalence classification retains the selected contraction record of
an actual decoder substitution isomorphism. -/
noncomputable def substitutionEquivalence := HomotopyEquivalence.ofIso sumSuccessor

example :
    (⟨Functor.whiskerLeft
      (UnivalenceLawParameters.classifyEquivalence (successorSub ≫ sum.code)
        (LargeConstructors.sigma (successorSub ≫ naturalsCode)
          (liftSub (liftedDecode naturalsCode) successorSub ≫ varyingCode)).code
        sumSuccessor.hom substitutionEquivalence).mapElements
      UnivalenceLawParameters.universalEquivalence.1,
      UnivalenceLawParameters.universalEquivalence.2.reindex
        (UnivalenceLawParameters.classifyEquivalence (successorSub ≫ sum.code)
          (LargeConstructors.sigma (successorSub ≫ naturalsCode)
            (liftSub (liftedDecode naturalsCode) successorSub ≫ varyingCode)).code
          sumSuccessor.hom substitutionEquivalence)⟩ :
      Σ f : liftedDecode (successorSub ≫ sum.code) ⟶
        liftedDecode (LargeConstructors.sigma (successorSub ≫ naturalsCode)
          (liftSub (liftedDecode naturalsCode) successorSub ≫ varyingCode)).code,
        HomotopyEquivalence f) = ⟨sumSuccessor.hom,substitutionEquivalence⟩ :=
  UnivalenceLawParameters.universalEquivalence_beta _ _ _ _

noncomputable def substitutionUaIdentity := NaturalUnivalenceLaws.identity (successorSub ≫ sum.code)

noncomputable def firstSubstitutionIso := Functor.isoWhiskerLeft twiceSub.mapElements sumSuccessor
noncomputable def secondSubstitutionIso := LargeConstructors.sigmaSubstitution
  (successorSub ≫ naturalsCode) (liftSub (liftedDecode naturalsCode) successorSub ≫ varyingCode) twiceSub

noncomputable def substitutionUaComposition := NaturalUnivalenceLaws.composition
  ((twiceSub ≫ successorSub) ≫ sum.code)
  (twiceSub ≫ (LargeConstructors.sigma (successorSub ≫ naturalsCode)
    (liftSub (liftedDecode naturalsCode) successorSub ≫ varyingCode)).code)
  (LargeConstructors.sigma ((twiceSub ≫ successorSub) ≫ naturalsCode)
    (liftSub (liftedDecode naturalsCode) (twiceSub ≫ successorSub) ≫ varyingCode)).code
  firstSubstitutionIso.hom (HomotopyEquivalence.ofIso firstSubstitutionIso)
  secondSubstitutionIso.hom (HomotopyEquivalence.ofIso secondSubstitutionIso)

example : sumComposite = firstSubstitutionIso ≪≫ secondSubstitutionIso :=
  LargeConstructors.sigmaSubstitution_comp _ _ _ _

end Examples.CubicalLargeConstructors
