import SquareKit.SpanInterpretation
import Examples.MatesBaseChange

/-! Two successive slice-forgetting interpretations retain the selected payload and apex.
The truncation control shows why pullback preservation cannot be omitted. -/
noncomputable section
namespace Examples.SpanInterpretation
open CategoryTheory Limits ConcreteCategory SquareKit SpanAction SpanInterpretation
open IndexedSumBaseChange

abbrev colored (X : Type) : Over Bool := Over.mk (↾fun _ : X => true)
abbrev base : Over Bool := colored Nat
abbrev nestedBase : Over base := Over.mk (𝟙 base)
abbrev displayed : Over base := Over.mk (Over.homMk (U := colored (Nat × Bool)) (↾Prod.fst : Nat × Bool ⟶ Nat) (by rfl))
abbrev selectedSpan : Spans nestedBase nestedBase :=
  ⟨displayed, Over.homMk displayed.hom, Over.homMk displayed.hom, trivial, trivial⟩
abbrev payloads : Over base := Over.mk (Over.homMk (U := colored ((n : Nat) × Fin (n+1)))
  (↾fun p : (n : Nat) × Fin (n+1) => p.1) (by rfl))
abbrev values : Over nestedBase := Over.mk (Over.homMk payloads.hom)
abbrev first : Over base ⥤ Over Bool := Over.forget base
abbrev second : Over Bool ⥤ Type := Over.forget Bool
abbrev both := first ⋙ second
abbrev interpreted := span both selectedSpan
abbrev interpretedValues := (Over.post both).obj values
abbrev payload : interpretedValues.left := ⟨3, ⟨3, by decide⟩⟩

def nativeInput : (action interpreted).obj interpretedValues |>.left :=
  encode interpreted.l interpretedValues (3,true) ⟨payload, rfl⟩

def sourceInput : both.obj ((action selectedSpan).obj values).left :=
  ((actionIso both selectedSpan).inv.app values).left nativeInput

theorem output : ((actionIso both selectedSpan).hom.app values).left sourceInput = nativeInput := by
  exact congr_hom (congrArg CommaMorphism.left
    ((actionIso both selectedSpan).inv_hom_id_app values)) nativeInput

example : pullback.fst (both.map values.hom) (both.map selectedSpan.l)
    (((actionIso both selectedSpan).hom.app values).left sourceInput) = payload := by
  rw [output]
  exact encode_value interpreted.l interpretedValues (3,true) ⟨payload,rfl⟩
example : pullback.snd (both.map values.hom) (both.map selectedSpan.l)
    (((actionIso both selectedSpan).hom.app values).left sourceInput) = (3,true) := by
  rw [output]
  exact encode_base interpreted.l interpretedValues (3,true) ⟨payload,rfl⟩

/-- The source representative itself has the independently specified payload and apex.
These use projection preservation, beyond the inverse/forward roundtrip. -/
theorem source_value : both.map (pullback.fst values.hom selectedSpan.l) sourceInput = payload := by
  have h := congr_hom (action_value both selectedSpan values) sourceInput
  rw [← h]
  change pullback.fst (both.map values.hom) (both.map selectedSpan.l)
    (((actionIso both selectedSpan).hom.app values).left sourceInput) = payload
  rw [output]
  exact encode_value interpreted.l interpretedValues (3,true) ⟨payload,rfl⟩
theorem source_apex : both.map (pullback.snd values.hom selectedSpan.l) sourceInput = (3,true) := by
  have h := congr_hom (action_apex both selectedSpan values) sourceInput
  rw [← h]
  change pullback.snd (both.map values.hom) (both.map selectedSpan.l)
    (((actionIso both selectedSpan).hom.app values).left sourceInput) = (3,true)
  rw [output]
  exact encode_base interpreted.l interpretedValues (3,true) ⟨payload,rfl⟩

/-- Forget the outer display, then its Bool coloring: both comparisons retain the chosen input. -/
theorem successive :
    (((actionIso second (span first selectedSpan)).hom.app ((Over.post first).obj values)).left)
      (second.map ((actionIso first selectedSpan).hom.app values).left sourceInput) = nativeInput := by
  have h := congr_hom (action_composition first second selectedSpan values) sourceInput
  exact h.symm.trans output

example : Pseudofunctor.StrongTrans (SpanAction.pseudofunctor (C := Over Bool))
    ((pseudofunctor second).comp (SpanAction.pseudofunctor (C := Type))) := transformation second
example : ¬ PreservesFiniteLimits second := MatesBaseChange.forget_not_leftExact

/-- This is the actual span-action/Beck–Chevalley compatibility after two interpretations. -/
example := beckChevalley_transport both
  (X := ⟨nestedBase⟩) (Y := ⟨nestedBase⟩) (Z := ⟨nestedBase⟩) selectedSpan selectedSpan values

/-- Inhabitedness forgets distinctions needed to form pullbacks. -/
def truncation : Type ⥤ Type where
  obj X := PLift (Nonempty X)
  map f := ↾fun x => ⟨x.down.map f⟩
  map_id _ := by apply ConcreteCategory.hom_ext; intro x; exact Subsingleton.elim _ _
  map_comp _ _ := by apply ConcreteCategory.hom_ext; intro x; exact Subsingleton.elim _ _
abbrev falseMap : PUnit ⟶ Bool := ↾fun _ => false
abbrev trueMap : PUnit ⟶ Bool := ↾fun _ => true

theorem no_source : IsEmpty (pullback falseMap trueMap) := ⟨fun p => by
  have h := congr_hom (pullback.condition (f := falseMap) (g := trueMap)) p
  exact Bool.false_ne_true h⟩

def lostMatch : pullback (truncation.map falseMap) (truncation.map trueMap) :=
  encode (truncation.map trueMap) (Over.mk (truncation.map falseMap))
    ⟨⟨PUnit.unit⟩⟩ ⟨⟨⟨PUnit.unit⟩⟩, (by apply PLift.ext; apply Subsingleton.elim)⟩

theorem comparison_not_surjective :
    ¬ Function.Surjective (pullbackComparison truncation falseMap trueMap) := by
  intro h
  obtain ⟨p,_⟩ := h lostMatch
  obtain ⟨q⟩ := p.down
  exact no_source.false q

theorem truncation_not_preserving : ¬ PreservesLimitsOfShape WalkingCospan truncation := by
  intro h
  let := h
  have hi : IsIso (pullbackComparison truncation falseMap trueMap) := inferInstance
  exact comparison_not_surjective ((isIso_iff_bijective _).mp hi).2
end Examples.SpanInterpretation
