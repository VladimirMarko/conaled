import Examples.LocalDisplacement.Controls
import Applications.Orbifold.LocalDisplacement.Descent
import Examples.AtlasIsotropy

/-! Ordinary endpoint/differential callers, parenthesized composition, and labels. -/
noncomputable section
open CategoryTheory
open scoped ComplexConjugate
namespace Examples.LocalDisplacement
open Orbifold Orbifold.LocalDisplacement
open Orbifolds.QuarterTurn (quarterTurn)

/-- The shared tree law transports all intermediate domain proofs. -/
theorem rotated_left :
    (leftTree.map (fun z => phase quarterTurn*z)).eval gyroAdd =
        Complex.I * leftTree.eval gyroAdd ∧
      (leftTree.map (fun z => phase quarterTurn*z)).Valid U gyroAdd :=
  tree_rotation quarterTurn leftTree left_valid

/-- Repeated representation changes use the same tree theorem again. -/
theorem rotated_twice (g h : QuarterTurn.C4) :
    ((leftTree.map (fun z => phase g*z)).map (fun z => phase h*z)).eval gyroAdd =
      phase h*(phase g*leftTree.eval gyroAdd) := by
  obtain ⟨he,hv⟩ := tree_rotation g leftTree left_valid
  rw [(tree_rotation h _ hv).1,he]

theorem fifth_mem : (1/5 : ℂ) ∈ U := by norm_num [U,Complex.normSq_apply]

theorem alignment_values : endpoint 1 (1/5) (1/5) = 5/13 ∧
    endpoint (quarterTurn^2) (1/5) (1/5) = 0 := by
  simpa [endpoint,phase,quarterTurn,neg_div] using QuarterTurn.quotient_addition_values

theorem alignment_changes_endpoint :
    endpoint 1 (1/5) (1/5) ≠ endpoint (quarterTurn^2) (1/5) (1/5) := by
  rw [alignment_values.1,alignment_values.2]
  norm_num

theorem alignments_admitted : Aligned 1 (1/5) (1/5) ∧ Aligned (quarterTurn^2) (1/5) (1/5) := by
  constructor
  · refine ⟨fifth_mem,by simpa [phase] using fifth_mem,?_⟩
    change endpoint 1 (1/5) (1/5) ∈ U
    rw [alignment_values.1]
    norm_num [U,Complex.normSq_apply]
  · refine ⟨fifth_mem,?_,?_⟩
    · norm_num [phase,quarterTurn,U,Complex.normSq_apply]
    · change endpoint (quarterTurn^2) (1/5) (1/5) ∈ U
      rw [alignment_values.2]
      exact zero_mem

/-- Ordinary direct use: no tree wrapper or timed-path state is required. -/
theorem direct_derivative : HasDerivAt (endpoint 1 (1/5)) (150/169 : ℂ) (1/5) := by
  have h := endpoint_derivative 1 fifth_mem fifth_mem
  convert h using 1
  norm_num [differential,phase,Complex.normSq_apply,map_ofNat]

theorem changed_derivative :
    HasDerivAt (endpoint (quarterTurn^2) (1/5)) (-25/24 : ℂ) (1/5) := by
  have h := endpoint_derivative (quarterTurn^2) fifth_mem fifth_mem
  convert h using 1
  norm_num [differential,phase,quarterTurn,Complex.normSq_apply,map_ofNat]

/-- Three leaves, two applications; the intermediate-domain proof comes from
an independently checked noncollinear tree. -/
theorem right_tree_derivative :
    HasDerivAt (fun z => endpoint 1 a (endpoint 1 b z))
      (differential 1 a (endpoint 1 b a) (differential 1 b a 1)) a := by
  apply composed_derivative 1 1 a_mem b_mem a_mem
  simpa [endpoint,phase] using reversed_admissible.2.2

example (h k g : QuarterTurn.C4) :
    endpoint (relabel h k g) (phase h*a) (phase k*b) = phase h*endpoint g a b :=
  endpoint_relabel h k g a b

example (h k g : QuarterTurn.C4) (v : ℂ) :
    differential (relabel h k g) (phase h*a) (phase k*b) (phase k*v) =
      phase h*differential g a b v := differential_relabel h k g a b v

/-- The selected action arrow exposes its original label. -/
example : (alignmentArrow (quarterTurn^2) QuarterTurn.fifth).hom = quarterTurn^2 :=
  alignmentArrow_label _ _

/-- Recover existing quotient-position failure; this is not a new obstruction. -/
example : Quotient.mk (MulAction.orbitRel QuarterTurn.C4 Disk) QuarterTurn.fifth =
    Quotient.mk _ QuarterTurn.minusFifth := QuarterTurn.second_inputs_same_orbit

example : Quotient.mk (MulAction.orbitRel QuarterTurn.C4 Disk) QuarterTurn.doubledFifth ≠
    Quotient.mk _ Orbifolds.QuarterTurn.origin := QuarterTurn.addition_outputs_different_orbits

def pairInput : Input 1 := ⟨(a,b),by simpa [Aligned,phase] using pair_admissible⟩

def pairArrow : (↑pairInput : ActionCategory QuarterTurn.C4 (Input 1)) ⟶
    (↑(quarterTurn • pairInput) : ActionCategory QuarterTurn.C4 (Input 1)) :=
  Functor.Elements.homMk quarterTurn rfl

example : ((endpointFunctor 1).map pairArrow).hom = quarterTurn := endpointFunctor_label _ _

example : (output 1 pairInput : ℂ) =
    (1010/10001 : ℂ) + (990/10001 : ℂ)*Complex.I := by
  simpa [output,pairInput,endpoint,phase] using pair_value

example : (endpointSquare 1).spec (Quotient.mk _ pairInput) =
    Quotient.mk _ (output 1 pairInput) := ((endpointSquare 1).commutes pairInput).symm

/-- Existing ineffective labels stay distinct even when endpoints and tangent
observations coincide. Keep the product label, not just its first projection. -/
theorem ineffective_labels_distinct : AtlasIsotropy.selectedLabel 1 ≠
    AtlasIsotropy.selectedLabel AtlasIsotropy.kernel := by
  intro h
  apply AtlasIsotropy.different_closings
  exact Functor.Elements.Hom.ext h

theorem ineffective_endpoint (a b : ℂ) :
    endpoint (AtlasIsotropy.selectedLabel 1).1 a b =
      endpoint (AtlasIsotropy.selectedLabel AtlasIsotropy.kernel).1 a b := rfl

theorem ineffective_differential (a b v : ℂ) :
    differential (AtlasIsotropy.selectedLabel 1).1 a b v =
      differential (AtlasIsotropy.selectedLabel AtlasIsotropy.kernel).1 a b v := rfl

example (v : ℂ) : AtlasIsotropy.closed 1 v = AtlasIsotropy.closed AtlasIsotropy.kernel v :=
  AtlasIsotropy.same_observation v

/-- Explicit division consumers use constructed branches and recover inputs. -/
example : leftDivide a (gyroAdd a b) = b := left_unique a_mem b_mem rfl
example : rightDivide b (gyroAdd a b) = a :=
  right_unique b_mem pair_admissible.2.2 a_mem rfl

theorem pair_left_branch : LeftBranch a (gyroAdd a b) :=
  ⟨a_mem,pair_admissible.2.2,by rw [left_unique a_mem b_mem rfl]; exact b_mem⟩

theorem pair_right_branch : RightBranch b (gyroAdd a b) :=
  ⟨b_mem,pair_admissible.2.2,by
    rw [right_unique b_mem pair_admissible.2.2 a_mem rfl]; exact a_mem⟩

example : Admissible a (leftDivide a (gyroAdd a b)) := left_branch_admissible pair_left_branch
example : Admissible (rightDivide b (gyroAdd a b)) b := right_branch_admissible pair_right_branch

end Examples.LocalDisplacement
