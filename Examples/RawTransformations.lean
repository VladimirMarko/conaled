import SquareKit.RawTransformation
import SquareKit.MorphismRestriction
import Mathlib.CategoryTheory.Category.Pointed
import Examples.WitnessEquivalence
import Examples.SpanInterpretationComposition

/-! Semantic transformations, genuine operation restrictions, and retained structured comparisons. -/
namespace Examples.RawTransformations
open SquareKit CategoryTheory

/-- The Boolean tag is raw arrow data; its NAND operation is not associative. -/
def tagged : CategoryOps Unit where
  Hom _ _ := Nat × Bool
  ident := (0, false)
  comp g f := (g.1 + f.1, !(g.2 && f.2))

def meaning : HomEquiv tagged where
  homSetoid _ _ := ⟨fun f g => f.1 = g.1, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

theorem congruence : CategoryCongr tagged meaning where
  comp hg hf := congrArg₂ Nat.add hg hf

theorem laws : CategoryLaws tagged meaning where
  id_comp f := Nat.zero_add f.1
  comp_id f := Nat.add_zero f.1
  assoc h g f := Nat.add_assoc h.1 g.1 f.1

theorem raw_not_associative :
    @tagged.comp () () () (@tagged.comp () () () (0, false) (0, false)) (0, true) ≠
      @tagged.comp () () () (0, false) (@tagged.comp () () () (0, false) (0, true)) := by
  change (0, false) ≠ (0, true)
  decide

theorem no_equality_laws : ¬ CategoryLaws tagged (equality tagged) :=
  fun L => raw_not_associative (L.assoc (a := ()) (b := ()) (c := ()) (d := ()) _ _ _)

def shift (n : Nat) (tag : Bool) : RawTransformation (RawMap.id tagged) (RawMap.id tagged) :=
  ⟨fun _ => (n, tag)⟩

theorem shift_natural (n : Nat) (tag : Bool) : RawTransformation.Natural meaning (shift n tag) :=
  fun f => Nat.add_comm f.1 n

theorem shift_nonidentity : ¬ RawTransformation.Rel meaning (shift 1 false)
    (RawTransformation.id (RawMap.id tagged)) := by
  intro h
  have := h ()
  change (1 : Nat) = 0 at this
  omega

theorem two_shifts : RawTransformation.Rel meaning
    ((shift 1 false).comp (shift 1 true)) (shift 2 false) := fun _ => rfl

example : RawTransformation.Natural meaning ((shift 1 false).comp (shift 1 true)) :=
  RawTransformation.comp_natural congruence laws (shift_natural _ _) (shift_natural _ _)

theorem tags_distinct : shift 1 false ≠ shift 1 true := by
  intro h
  have := congrArg (fun α => (α.app ()).2) h
  exact Bool.false_ne_true this

theorem tags_related : RawTransformation.Rel meaning (shift 1 false) (shift 1 true) := fun _ => rfl

local instance : Category (HomQuotient tagged meaning) := HomQuotient.category congruence laws

def onClasses (n : Nat) (tag : Bool) :=
  RawTransformation.quotient congruence laws congruence laws
    (RawMap.id_laws meaning) (RawMap.id_laws meaning) (shift n tag) (shift_natural n tag)

theorem erased_tags_equal : onClasses 1 false = onClasses 1 true :=
  (RawTransformation.quotient_eq_iff congruence laws congruence laws
    (RawMap.id_laws meaning) (RawMap.id_laws meaning) _ _ _ _).2 tags_related

theorem no_representative_recovery : ¬ Function.Injective (onClasses 1) := by
  intro h
  exact Bool.false_ne_true (h erased_tags_equal)

theorem quotient_nonidentity : onClasses 1 false ≠
    𝟙 ((RawMap.id tagged).quotientFunctor (RawMap.id_laws meaning) congruence laws congruence laws) := by
  intro h
  apply shift_nonidentity
  apply (RawTransformation.quotient_eq_iff congruence laws congruence laws
    (RawMap.id_laws meaning) (RawMap.id_laws meaning) _ _ (shift_natural _ _)
    (RawTransformation.id_natural laws _)).1
  exact h

theorem quotient_two_shifts :
    (onClasses 1 false ≫ onClasses 1 true).app ⟨()⟩ =
      HomQuotient.classOf (E := meaning) (2, false) := by
  have h := RawTransformation.quotient_comp congruence laws congruence laws
    (RawMap.id_laws meaning) (RawMap.id_laws meaning) (RawMap.id_laws meaning)
    (shift 1 false) (shift 1 true) (shift_natural _ _) (shift_natural _ _)
  exact (congrArg (fun η => η.app ⟨()⟩) h).symm.trans (Quotient.sound (two_shifts ()))

/-- This arrow action fails identity preservation, but prewhiskering still makes sense. -/
def unpreserving : RawMap tagged tagged := ⟨id, fun _ => (7, false)⟩

theorem unpreserving_no_laws : ¬ MapLaws unpreserving (equality tagged) meaning := by
  intro L
  have h := L.ident (a := ())
  change (7 : Nat) = 0 at h
  omega

example : RawTransformation.Natural meaning
    (RawTransformation.whiskerLeft unpreserving (shift 1 false)) :=
  RawTransformation.whiskerLeft_natural unpreserving (shift_natural _ _)

example : RawTransformation.Rel meaning
    (RawTransformation.horizontal ((shift 1 false).comp (shift 2 false))
      ((shift 3 false).comp (shift 4 false)))
    ((RawTransformation.horizontal (shift 1 false) (shift 3 false)).comp
      (RawTransformation.horizontal (shift 2 false) (shift 4 false))) :=
  RawTransformation.interchange congruence laws (RawMap.id_laws meaning) _ _ _ _ (shift_natural _ _)

/-- A noncommuting component fails naturality even in an equality-lawful target. -/
def endomaps : CategoryOps Unit where
  Hom _ _ := Nat → Nat
  ident := id
  comp g f := g ∘ f

def successor : RawTransformation (RawMap.id endomaps) (RawMap.id endomaps) := ⟨fun _ => Nat.succ⟩

theorem successor_not_natural : ¬ RawTransformation.Natural (equality endomaps) successor := by
  intro h
  have h0 := congrFun (h (a := ()) (b := ()) (fun _ => 0)) 0
  change (0 : Nat) = 1 at h0
  omega

/-- Preserving the selected nullary operation restricts arrows to zero-preserving maps. -/
def preservesZero {a b : Unit} (f : endomaps.Hom a b) := PLift (f 0 = 0)

def zeroClosure : MorphismRestriction.CategoryClosure endomaps preservesZero where
  ident := ⟨rfl⟩
  comp {_a _b _c} {g _f} hg hf := ⟨(congrArg g hf.down).trans hg.down⟩

/-- The native category and the raw restricted presentation recover each entire arrow. -/
def pointedHomEquiv :
    MorphismRestriction.Hom endomaps preservesZero () () ≃ (Pointed.of (0 : Nat) ⟶ Pointed.of (0 : Nat)) where
  toFun f := ⟨f.arrow, f.sat.down⟩
  invFun f := ⟨f.toFun, ⟨f.map_point⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

example : pointedHomEquiv (MorphismRestriction.ops zeroClosure).ident = 𝟙 (Pointed.of (0 : Nat)) := rfl
example (f g : (MorphismRestriction.ops zeroClosure).Hom () ()) :
    pointedHomEquiv ((MorphismRestriction.ops zeroClosure).comp g f) =
      pointedHomEquiv f ≫ pointedHomEquiv g := rfl

theorem successor_excluded : ¬ Nonempty (preservesZero (a := ()) (b := ()) Nat.succ) := by
  rintro ⟨h⟩
  exact Nat.noConfusion h.down

/-- No migration is needed for ordinary natural transformations. -/
example {A B : Type} [Category A] [Category B] {F G H : A ⥤ B} (α : F ⟶ G) (β : G ⟶ H) :
    RawTransformation.toNatTrans (RawMap.ofFunctor_laws F) (RawMap.ofFunctor_laws H)
      ((RawTransformation.ofNatTrans α).comp (RawTransformation.ofNatTrans β))
      (RawTransformation.comp_natural (equalityCongr _) (ofCategoryLaws B)
        (RawTransformation.ofNatTrans_natural α) (RawTransformation.ofNatTrans_natural β)) = α ≫ β := rfl

/-- The family-side comparison retains complete modifications, beyond component observations. -/
example : SpanInterpretation.tripleComparisonLeft
    SpanInterpretationComposition.outer SpanInterpretation.first SpanInterpretation.second =
    SpanInterpretation.tripleComparisonRight
      SpanInterpretationComposition.outer SpanInterpretation.first SpanInterpretation.second :=
  SquareKit.SpanInterpretation.composition_associativity _ _ _

/-- Existing witness operations do not acquire associativity from semantic extension. -/
example := WitnessEquivalence.trans_not_associative
example := WitnessEquivalence.squares_distinct
example := WitnessEquivalence.erased_squares_equal
end Examples.RawTransformations
