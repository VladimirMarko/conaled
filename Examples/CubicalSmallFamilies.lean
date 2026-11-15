import SquareKit.Internal.Cubical.SmallFamilySubstitution
import Examples.CubicalLocalFilling

/-! Small codes include an integer fiber and a genuinely dependent finite fiber.
The constructor comparisons retain native providers and explicit substitutions. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalSmallFamilies
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open CubicalPresheaf

def unitIndex (Γ : Context) : Term (constantFamily Γ Unit) where
  val _ := ()
  property _ := rfl

def natCode : raisedContext naturals ⟶ smallFamilyCodes :=
  discreteCode (unitIndex naturals) (fun _ => Nat)

def natDecode : decode natCode ≅ constantFamily naturals Nat :=
  discreteCode_decode (unitIndex naturals) (fun _ => Nat)

def intCode : raisedContext naturals ⟶ smallFamilyCodes :=
  discreteCode (unitIndex naturals) (fun _ => Int)

def intDecode : decode intCode ≅ constantFamily naturals Int :=
  discreteCode_decode (unitIndex naturals) (fun _ => Int)

/-- Read the actual decoded argument, not just a constant in its base context. -/
def argument : Term (constantFamily (total (decode natCode)) Nat) :=
  Term.map (Functor.whiskerLeft (projection (decode natCode)).mapElements natDecode.hom)
    (generic (decode natCode))

def dependentCode : raisedContext (total (decode natCode)) ⟶ smallFamilyCodes :=
  discreteCode argument (fun n => Fin (n+1))

def dependentDecode : decode dependentCode ≅ discreteFamily argument (fun n => Fin (n+1)) :=
  discreteCode_decode argument (fun n => Fin (n+1))

def atArgument (n : Nat) : (total (decode natCode)).Elements :=
  (total (decode natCode)).elementsMk (Opposite.op ⟨0⟩) ⟨(0 : Nat),n⟩

theorem nonconstant_decoded_fibers : ¬ Nonempty
    ((decode dependentCode).obj (atArgument 0) ≃ (decode dependentCode).obj (atArgument 1)) := by
  rintro ⟨e⟩
  have e₀ : (decode dependentCode).obj (atArgument 0) ≃ Fin 1 :=
    (dependentDecode.app (atArgument 0)).toEquiv
  have e₁ : (decode dependentCode).obj (atArgument 1) ≃ Fin 2 :=
    (dependentDecode.app (atArgument 1)).toEquiv
  have h := Fintype.card_congr (e₀.symm.trans (e.trans e₁))
  simp at h

def selectArgument : naturals ⟶ total (decode natCode) :=
  pair (𝟙 naturals) (Term.map natDecode.inv CubicalDiscreteFilling.index)

abbrev selectedCode := raisedSub selectArgument ≫ dependentCode

theorem two_substitutions :
    decodedLocalFamily (raisedSub twice ≫ raisedSub successor ≫ selectedCode) =
      ((decodedLocalFamily selectedCode).reindex successor).reindex twice := by
  rw [decodedLocalFamily_reindex, decodedLocalFamily_reindex]

def selectedDecode : decode selectedCode ≅
    discreteFamily CubicalDiscreteFilling.index (fun n => Fin (n+1)) :=
  Functor.isoWhiskerLeft selectArgument.mapElements dependentDecode

def selectedLast : Term (decode selectedCode) :=
  Term.map selectedDecode.inv CubicalDiscreteFilling.finiteLast

theorem selected_last_retained : Term.map selectedDecode.hom selectedLast =
    CubicalDiscreteFilling.finiteLast := by
  apply Term.ext
  intro x
  exact congrArg (fun η => η.app x (CubicalDiscreteFilling.finiteLast.val x)) selectedDecode.inv_hom_id

theorem selected_last_at_two :
    (((Term.map selectedDecode.hom selectedLast).reindex successor).reindex twice).val
      (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : Nat)) = (5 : Fin 6) := by
  rw [selected_last_retained]
  rfl

def sigmaComparison : decode (sigmaCode natCode dependentCode) ≅
    sigma (decode natCode) (decode dependentCode) := sigmaCode_decode natCode dependentCode

noncomputable def piComparison : decode (piCode natCode dependentCode) ≅
    pi (decode natCode) (decode dependentCode) := piCode_decode natCode dependentCode

def sigmaSubstitution : decode (raisedSub successor ≫ sigmaCode natCode dependentCode) ≅
    decode (sigmaCode (raisedSub successor ≫ natCode)
      (raisedSub (liftSub (decode natCode) successor) ≫ dependentCode)) :=
  sigmaCode_reindex natCode dependentCode successor

noncomputable def piSubstitution : decode (raisedSub twice ≫ piCode natCode dependentCode) ≅
    decode (piCode (raisedSub twice ≫ natCode)
      (raisedSub (liftSub (decode natCode) twice) ≫ dependentCode)) :=
  piCode_reindex natCode dependentCode twice


def sumCode := sigmaCode natCode dependentCode

def unitOverSum : raisedContext (total (decode sumCode)) ⟶ smallFamilyCodes :=
  discreteCode (unitIndex (total (decode sumCode))) (fun _ => Unit)

noncomputable def functionsCode := piCode sumCode unitOverSum

noncomputable def functionSection : Term (decode functionsCode) :=
  Term.map (piCode_decode sumCode unitOverSum).inv
    (lam (Term.map (discreteCode_decode (unitIndex (total (decode sumCode))) (fun _ => Unit)).inv
      (unitIndex (total (decode sumCode)))))

noncomputable def pathBody := raisedSub (projection (interval naturals)) ≫ functionsCode

noncomputable def composedPathCode := pathCode pathBody
  (functionSection.reindex (endpointSub naturals false ≫ projection (interval naturals)))
  (functionSection.reindex (endpointSub naturals true ≫ projection (interval naturals)))

noncomputable def composedPathComparison : decode composedPathCode ≅
    path (decode pathBody)
      (functionSection.reindex (endpointSub naturals false ≫ projection (interval naturals)))
      (functionSection.reindex (endpointSub naturals true ≫ projection (interval naturals))) :=
  pathCode_decode pathBody _ _

noncomputable def composedPathSubstitution :
    decode (raisedSub successor ≫ composedPathCode) ≅
      decode (pathCode (raisedSub (liftSub (interval naturals) successor) ≫ pathBody)
        ((functionSection.reindex (endpointSub naturals false ≫ projection (interval naturals))).reindex successor)
        ((functionSection.reindex (endpointSub naturals true ≫ projection (interval naturals))).reindex successor)) :=
  pathCode_reindex pathBody _ _ successor


-- Elaboration rejection checks, not impossibility theorems about bare families.
example : True := by
  fail_if_success
    have _ : Context.{0} := smallFamilyCodes.{0}
  trivial

example : True := by
  fail_if_success
    have _ : LocalFamily naturals := { family := constantFamily naturals Nat }
  trivial

example : True := by
  fail_if_success
    have _ : (LocalFamily.discrete (unitIndex naturals) (fun _ => Nat)).filling.Lawful :=
      { fills := (LocalFamily.discrete (unitIndex naturals) (fun _ => Nat)).lawful.fills }
  trivial

end Examples.CubicalSmallFamilies
