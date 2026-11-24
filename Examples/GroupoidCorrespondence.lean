import SquareKit.GroupoidCorrespondence
import Examples.SecondIdentity
import Examples.SpanAction
import Examples.SpanInterpretation

/-! Boundary labels survive selected comma composition, reassociation and
representation change. Discrete recovery uses the ordinary chosen span data. -/
set_option autoImplicit false
noncomputable section
namespace Examples.GroupoidCorrespondence
open CategoryTheory Limits ConcreteCategory SquareKit.GroupoidCorrespondence
open SecondIdentity

example : Groupoid (Boundary Label) := inferInstance
example : Groupoid (Left Label) := inferInstance
example : Groupoid (Right Label) := inferInstance
example : Category.{0} (Left Label) := inferInstance

/-- Here the same group elements are boundary 1-arrows, not the 2-cells of
SecondIdentity's double delooping. -/
def zeroBoundary : Boundary Label := boundary Label zeroCell
def oneBoundary : Boundary Label := boundary Label oneCell

theorem boundary_distinct : zeroBoundary ≠ oneBoundary := by
  intro h
  exact cell_distinct (congrArg Comma.hom h)

/-- The strict object-level pullback forgets the selected group arrow. -/
abbrev Strict := {p : Point × Point // (point Label).obj p.1 = (point Label).obj p.2}
def erase (c : Boundary Label) : Strict := ⟨(c.left,c.right),Subsingleton.elim _ _⟩

theorem no_boundary_observation :
    ¬ ∃ observe : Strict → Nat, ∀ c : Boundary Label, observe (erase c) = labelObservation c.hom := by
  rintro ⟨observe,h⟩
  have same : erase zeroBoundary = erase oneBoundary := Subsingleton.elim _ _
  have bad := (h zeroBoundary).symm.trans ((congrArg observe same).trans (h oneBoundary))
  exact (by decide : (0 : Nat) ≠ 1) bad

/-- The selected three-span chain has independent boundary and Boolean data. -/
def input (b : Bool) : Left Bit := left Bit (Multiplicative.ofAdd true) b

def output (b : Bool) : Right Label :=
  (reassociate Label).functor.obj ((changeLeft encode).functor.obj (input b))

theorem output_boundary (b : Bool) : (output b).hom = oneCell := by
  exact changeLeft_boundary encode (input b)
theorem output_boolean (b : Bool) : (output b).right.right.as = b := rfl

theorem represented_routes (b : Bool) : output b =
    (changeRight encode).functor.obj ((reassociate Bit).functor.obj (input b)) :=
  representation_reassociate encode (input b)

theorem output_observation (b : Bool) : labelObservation (output b).hom = 1 := by
  rw [output_boundary]
  rfl

theorem boolean_distinct : output false ≠ output true := by
  intro h
  have bad := congrArg (fun c : Right Label => c.right.right.as) h
  exact Bool.false_ne_true bad

example (c : Left Bit) : (reassociate Bit).inverse.obj ((reassociate Bit).functor.obj c) = c :=
  reassociate_roundtrip Bit c
example (c : Left Bit) : (changeLeft encode).inverse.obj ((changeLeft encode).functor.obj c) = c :=
  changeLeft_roundtrip encode c
example (b : Bool) :
    (headFromRight Label).obj (output b) =
      (rightUnit Label).functor.obj ((forgetBoolean Label).obj ((changeLeft encode).functor.obj (input b))) :=
  reassociate_unit Label _
example : (leftUnit Label).functor.obj ((leftUnit Label).inverse.obj oneBoundary) = oneBoundary :=
  leftUnit_recovery Label _
example : (rightUnit Label).functor.obj ((rightUnit Label).inverse.obj oneBoundary) = oneBoundary :=
  rightUnit_recovery Label _

/-- Reuse the independent 2-cell erasure test without confusing its dimension
with the group arrow retained above. -/
example {C : Type} [Category C] (x y : LocallyDiscrete C) (f g : x ⟶ y)
    (forget : SquareKit.DoubleDelooping.Cell Label → (f ⟶ g)) :
    ¬ ∃ observe : (f ⟶ g) → Nat, ∀ c, observe (forget c) = labelObservation c :=
  no_groupoid_observation x y f g forget

namespace Ordinary
open SquareKit IndexedSumBaseChange
open Examples.SpanAction

def two : Comma (discreteMap duplicate.r) (discreteMap matchDouble.l) :=
  ⟨⟨(3,true)⟩,⟨3⟩,Discrete.eqToHom rfl⟩
theorem two_chosen : ((discretePullback duplicate.r matchDouble.l).functor.obj two).as = chosenTwo :=
  discretePullback_encode matchDouble.l (Over.mk duplicate.r) 3 ⟨(3,true),rfl⟩

def three : Comma (discreteMap firstTwo.r) (discreteMap forgetBase.l) :=
  (discretePullback firstTwo.r forgetBase.l).inverse.obj ⟨chosenThree⟩
theorem three_chosen : ((discretePullback firstTwo.r forgetBase.l).functor.obj three).as = chosenThree :=
  congrArg Discrete.as (IsDiscrete.eq_of_hom ((discretePullback firstTwo.r forgetBase.l).counitIso.hom.app ⟨chosenThree⟩))
example : three.left.as = chosenTwo := by
  change ((discretePullback firstTwo.r forgetBase.l).inverse.obj ⟨chosenThree⟩).left.as = _
  rw [discretePullback_inverse_fst, chosenThree_first]
example : three.right.as = (4,1) := by
  rw [show three.right.as = pullback.snd firstTwo.r forgetBase.l chosenThree from
    discretePullback_inverse_snd _ _ _]
  exact join_second firstTwo forgetBase chosenTwo (4,1) _

/-- The ordinary compositor consumes exactly the recovered chosen input. -/
def commaInput := (discretePullback values.hom allThree.l).inverse.obj ⟨Examples.SpanAction.input⟩
theorem compositor_on_comma :
    ((SquareKit.SpanAction.compositionIso firstTwo forgetBase).hom.app values).left
      ((discretePullback values.hom allThree.l).functor.obj commaInput).as =
    ((SquareKit.SpanAction.compositionIso firstTwo forgetBase).hom.app values).left Examples.SpanAction.input := by
  congr 1
  exact congrArg Discrete.as
    (IsDiscrete.eq_of_hom ((discretePullback values.hom allThree.l).counitIso.hom.app ⟨Examples.SpanAction.input⟩))

/-- Ordinary noninvertible apex maps are retained by the existing route. -/
example : ¬ Function.Injective collapse.hom := by
  intro h
  have bad := congrArg Prod.snd (h (show collapse.hom (3,false) = collapse.hom (3,true) from rfl))
  exact Bool.false_ne_true bad
end Ordinary

namespace Native
open SquareKit IndexedSumFamilies
universe u
variable {Γ Δ : Type u} (I : Γ → Type u) (P : (γ : Γ) → I γ → Type u) (σ : Δ ⟶ Γ)
open Examples.SpanAction

def commaInput (δ : Δ) (s : Selected I P (σ δ)) :=
  (discretePullback (family I P).hom (Span.comp (sumSpan I) (substitutionSpan σ)).l).inverse.obj
    ⟨nativeInput I P σ δ s⟩

theorem input_recovery (δ : Δ) (s : Selected I P (σ δ)) :
    ((discretePullback (family I P).hom (Span.comp (sumSpan I) (substitutionSpan σ)).l).functor.obj
      (commaInput I P σ δ s)).as = nativeInput I P σ δ s :=
  congrArg Discrete.as (IsDiscrete.eq_of_hom
    ((discretePullback (family I P).hom (Span.comp (sumSpan I) (substitutionSpan σ)).l).counitIso.hom.app _))

theorem selected_recovery (δ : Δ) (s : Selected I P (σ δ)) :
    ((Over.pullback σ).map ((Over.map (indexMap I)).map
      ((Over.pullbackId (X := Sigma I)).hom.app (family I P)))).left
      (((SquareKit.SpanAction.compositionIso (sumSpan I) (substitutionSpan σ)).hom.app (family I P)).left
        ((discretePullback (family I P).hom (Span.comp (sumSpan I) (substitutionSpan σ)).l).functor.obj
          (commaInput I P σ δ s)).as) = first I P σ δ s := by
  rw [input_recovery]
  exact native_recovery I P σ δ s
end Native

namespace Interpreted
open Examples.SpanInterpretation

def commaOutput :=
  (discretePullback interpretedValues.hom interpreted.l).inverse.obj ⟨nativeInput⟩
theorem output_recovery :
    ((SquareKit.SpanInterpretation.actionIso both selectedSpan).hom.app values).left sourceInput =
      ((discretePullback interpretedValues.hom interpreted.l).functor.obj commaOutput).as := by
  rw [Examples.SpanInterpretation.output]
  exact (congrArg Discrete.as (IsDiscrete.eq_of_hom
    ((discretePullback interpretedValues.hom interpreted.l).counitIso.hom.app ⟨nativeInput⟩))).symm
example : ¬ PreservesFiniteLimits second := Examples.MatesBaseChange.forget_not_leftExact
example : ¬ PreservesLimitsOfShape WalkingCospan truncation := truncation_not_preserving
end Interpreted
end Examples.GroupoidCorrespondence
