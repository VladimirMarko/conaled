import SquareKit.Internal.PathTransport.ComparisonProjections
import Examples.FamilyMapElimination

/-! Noninvertible comparison families retain selected C4 arrows through
comprehension, substitution and pairing. -/
noncomputable section
namespace Examples.GroupoidComparison
open CategoryTheory SquareKit.Internal.PathTransport.GroupoidModel
open Comparison FamilyMapElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local instance : Groupoid (Discrete PUnit) := Groupoid.ofIsGroupoid

def context : Comparison.Context.{0} := ⟨Grpd.of (Discrete PUnit), Grpd.of (Discrete PUnit), 𝟭 _⟩
def family : Comparison.Family context := ⟨before (Cat.of (Discrete PUnit)), after (Cat.of (Discrete PUnit)), familyMap (Cat.of (Discrete PUnit))⟩
def chosenSection : Comparison.Section family where
  left := inhabitBefore (Cat.of (Discrete PUnit))
  right := (inhabitBefore (Cat.of (Discrete PUnit))).familyImage (familyMap (Cat.of (Discrete PUnit)))
  commutes := rfl

example : ¬ Function.Injective (family.map.app (Discrete.mk PUnit.unit)).obj := collapse_not_injective
example : ¬ (family.map.app (Discrete.mk PUnit.unit)).Full := collapse_not_full

def point (b : Bool) : family.extend.left := ⟨Discrete.mk PUnit.unit, (Discrete.mk b,p)⟩
def loop (b : Bool) (g : p ⟶ p) : point b ⟶ point b := ⟨𝟙 _, selected b g⟩

example (b : Bool) (g : p ⟶ p) :
    (family.extend.map.map (loop b g)).fiber = g := by
  simp [Family.extend, family, context, loop, familyMap, selected, collapse,
    Grothendieck.map, before, after, constant, Grpd.forgetToCat]

example (b : Bool) : Function.Injective (fun g : p ⟶ p => family.extend.map.map (loop b g)) := by
  intro g h he
  have hf := Grothendieck.congr he
  simpa [Family.extend, family, context, loop, familyMap, selected, collapse,
    Grothendieck.map, Grothendieck.pre, before, after, constant, Grpd.forgetToCat] using hf

/-- Reindexing constructs the comparison for an open caller's substitution. -/
example {Δ : Comparison.Context.{0}} (σ : Comparison.Substitution Δ context) :
    (chosenSection.reindex σ).left.familyImage (family.reindex σ).map =
      (chosenSection.reindex σ).right.reindex Δ.map := (chosenSection.reindex σ).commutes

/-- Pairing really extends the selected substitution. -/
example {Δ : Comparison.Context.{0}} (σ : Comparison.Substitution Δ context)
    (t : Comparison.Section (family.reindex σ)) :
    Comparison.Substitution.comp family.weaken (family.pair σ t) = σ :=
  family.weaken_pair σ t

/-- A noninvertible comparison of complete primitive signatures. -/
def signature : Comparison.Signature.{0} where
  base := ⟨@Grpd.of (Discrete Bool × G) Groupoid.ofIsGroupoid,
    @Grpd.of G Groupoid.ofIsGroupoid, collapse⟩
  leftFiber := (CategoryTheory.Functor.const _).obj Bool
  rightFiber := (CategoryTheory.Functor.const _).obj PUnit
  fiberMap := { app := fun _ => ↾fun _ => PUnit.unit, naturality := fun {_ _} _ => rfl }

def basePoint : Comparison.Section (signature.baseFamily context) := chosenSection

example : ((signature.fiber basePoint).map.app (Discrete.mk PUnit.unit)).obj
    (Discrete.mk false) = Discrete.mk PUnit.unit := rfl
example : ((signature.fiber basePoint).map.app (Discrete.mk PUnit.unit)).obj
    (Discrete.mk true) = Discrete.mk PUnit.unit := rfl

example (g : p ⟶ p) :
    ((family.identity chosenSection chosenSection).map.app (Discrete.mk PUnit.unit)).obj
      (Discrete.mk (selected false g)) = Discrete.mk g := rfl

/-- Both projections preserve the independently supplied primitive fibers. -/
example : (Comparison.leftProjection signature).family (signature.fiber basePoint) =
    primitiveFiber signature.leftFiber basePoint.left := Comparison.left_fiber signature basePoint
example : (Comparison.rightProjection signature).family (signature.fiber basePoint) =
    primitiveFiber signature.rightFiber basePoint.right := Comparison.right_fiber signature basePoint

/-- Source-family conversion commutes with both projections through actual casts. -/
example {Γ : Comparison.Context.{0}} {A B : Comparison.Family Γ}
    (h : A = B) (s : Comparison.Section A) :
    HEq (cast (congrArg Comparison.Section h) s).left s.left := Comparison.Section.cast_left h s
example {Γ : Comparison.Context.{0}} {A B : Comparison.Family Γ}
    (h : A = B) (s : Comparison.Section A) :
    HEq (cast (congrArg Comparison.Section h) s).right s.right := Comparison.Section.cast_right h s

end Examples.GroupoidComparison
