import SquareKit.FiniteDependentCorrespondence
import Examples.GroupoidCorrespondence

/-! Full witness recovery through the finite dependent comma example.
The imported ordinary clients retain their original pullback hypotheses. -/
noncomputable section
namespace Examples.FiniteDependentCorrespondence
open CategoryTheory
open SquareKit.FiniteDependentCorrespondence
open SquareKit.Internal.PathTransport
set_option autoImplicit false

example : Bicategory.Strict FiniteFiber := inferInstance
example : Finite FiniteFiber := inferInstance
example (m n : Q) : Finite (FiberCell m n) := inferInstance
example : Finite H := inferInstance
example : Finite Boolean.H := inferInstance
example (p q : Boolean.H) : Finite (p ⟶ q) := inferInstance
example (p q : H) : Finite (p ⟶ q) := inferInstance
example : Groupoid H := homGroupoid

example (m n : Q) (c : arrow m ⟶ arrow n) :
    dependentCellEquiv m n ((dependentCellEquiv m n).symm c) = c :=
  (dependentCellEquiv m n).apply_symm_apply c
example (m n : Q) (d : Coordinates m n) :
    (dependentCellEquiv m n).symm (dependentCellEquiv m n d) = d :=
  (dependentCellEquiv m n).symm_apply_apply d

example : selectedOne ≠ selectedThree := selected_distinct
example : selectedOne ≫ selectedOne ≠ 𝟙 (arrow 0) := selectedOne_square_ne_identity
example : selectedOne ≫ selectedThree = 𝟙 (arrow 0) := selectedOne_three
example : (dependentCellEquiv 0 0).symm (selectedOne ≫ selectedOne) = ⟨(0,2), by decide⟩ := by
  rw [selectedOne_square]
  exact (dependentCellEquiv 0 0).symm_apply_apply _
example (m : Q) : ¬ ∃ t : Packet, packetView t = (m,m,1,0) := packet_zero_rejected m

/-- Both parallel witnesses survive both bracketings with the cancelling tail. -/
example : packetView (interpretRight (reassociate.functor.obj (leftCell selectedOne 1 1))) =
    (0,0,1,1) := by rw [interpretation_reassociate]; exact selectedOne_tail11
example : packetView (interpretRight (reassociate.functor.obj (leftCell selectedThree 1 1))) =
    (0,0,1,3) := by rw [interpretation_reassociate]; exact selectedThree_tail11

/-- The noncancelling tail checks the later arrow coordinates as well. -/
example : packetView (interpretRight (reassociate.functor.obj (leftCell selectedOne 1 0))) =
    (1,1,1,1) := by rw [interpretation_reassociate]; exact selectedOne_tail10
example : packetView (interpretRight (reassociate.functor.obj (leftCell selectedThree 1 0))) =
    (1,1,1,3) := by rw [interpretation_reassociate]; exact selectedThree_tail10

example (c : Boolean.Left) :
    Boolean.leftNormal.symm (normalRepresentation.symm (leftNormal (mapLeft.obj c))) = c :=
  mapLeft_recovery c
example (c : Boolean.Right) :
    Boolean.rightNormal.symm (normalRepresentation.symm (rightNormal (mapRight.obj c))) = c :=
  mapRight_recovery c
example (t : Boolean.Packet) : packetRepresentation.symm (packetRepresentation t) = t :=
  packetRepresentation.symm_apply_apply t
example (t : Packet) : packetRepresentation (packetRepresentation.symm t) = t :=
  packetRepresentation.apply_symm_apply t

example : packetView (interpretLeft
    (mapLeft.obj (Boolean.leftCell Boolean.selectedOne true true))) = (0,0,1,1) := by
  rw [mapLeft_selectedOne]
  exact selectedOne_tail11
example : packetView (interpretLeft
    (mapLeft.obj (Boolean.leftCell Boolean.selectedThree true true))) = (0,0,1,3) := by
  rw [mapLeft_selectedThree]
  exact selectedThree_tail11
example : packetView (interpretRight
    (mapRight.obj (Boolean.reassociate.functor.obj
      (Boolean.leftCell Boolean.selectedOne true false)))) = (1,1,1,1) := by
  rw [← representation_reassociate_obj, interpretation_reassociate, mapLeft_selectedOne]
  exact selectedOne_tail10
example : packetView (interpretRight
    (mapRight.obj (Boolean.reassociate.functor.obj
      (Boolean.leftCell Boolean.selectedThree true false)))) = (1,1,1,3) := by
  rw [← representation_reassociate_obj, interpretation_reassociate, mapLeft_selectedThree]
  exact selectedThree_tail10

/-- The comma construction also recovers arbitrary ordinary chosen Type pullbacks. -/
example {A X : Type} (f : A ⟶ X) (V : CategoryTheory.Over X)
    (a : A) (x : {v : V.left // V.hom v = f a}) :
    ((SquareKit.GroupoidCorrespondence.discretePullback V.hom f).functor.obj
      ⟨⟨x.val⟩,⟨a⟩,Discrete.eqToHom x.property⟩).as =
      SquareKit.IndexedSumBaseChange.encode f V a x :=
  SquareKit.GroupoidCorrespondence.discretePullback_encode f V a x

end Examples.FiniteDependentCorrespondence
