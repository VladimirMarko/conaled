import SquareKit.Internal.PathTransport.FamilyMapElimination
import Examples.GroupoidTransport
import Mathlib.CategoryTheory.Products.Basic

/-! Noninvertible family maps, retained isotropy arrows and nonempty dependent
tails for the shared elimination comparison. -/
noncomputable section
namespace Examples.FamilyMapElimination
open CategoryTheory SquareKit.Internal.PathTransport.GroupoidModel
open ContextualElimination CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev G := Examples.GroupoidTransport.C4
local instance : Groupoid G := Groupoid.ofIsGroupoid
local instance : Groupoid (Discrete Bool × G) := Groupoid.ofIsGroupoid
abbrev p : G := Examples.GroupoidTransport.point

/-- Forget a Boolean component while retaining the entire C4 groupoid. -/
def collapse : Grpd.of (Discrete Bool × G) ⟶ Grpd.of G := CategoryTheory.Prod.snd _ _

theorem collapse_not_injective : ¬ Function.Injective collapse.obj := by
  intro h
  have he := h (show collapse.obj (Discrete.mk false,p) =
    collapse.obj (Discrete.mk true,p) from rfl)
  have hb := congrArg (fun x => x.1.as) he
  cases hb

theorem collapse_not_full : ¬ collapse.Full := by
  intro h
  let := h
  have f : (Discrete.mk false,p) ⟶ (Discrete.mk true,p) := collapse.preimage (𝟙 p)
  have hb := f.1.eq
  cases hb

/-- Every chosen isotropy arrow is retained, although objects collapse. -/
def selected (b : Bool) (g : p ⟶ p) :
    (Discrete.mk b,p) ⟶ (Discrete.mk b,p) := (𝟙 _,g)

example (b : Bool) (g : p ⟶ p) : collapse.map (selected b g) = g := rfl
example (b : Bool) : Function.Injective (fun g : p ⟶ p => collapse.map (selected b g)) :=
  fun _ _ h => h

/-- These families change by a map with no inverse on objects. -/
def before (C : Cat.{0,0}) : C ⥤ Grpd.{0,0} := constant (Discrete Bool × G)
def after (C : Cat.{0,0}) : C ⥤ Grpd.{0,0} := constant G
def familyMap (C : Cat.{0,0}) : before C ⟶ after C where
  app _ := collapse
  naturality {_ _} _ := rfl

/-- The source family is inhabited over every context. -/
def inhabitBefore (C : Cat.{0,0}) : Section (before C) :=
  constantSection ((CategoryTheory.Functor.const C).obj (Discrete.mk false,p))

/-- The comparison changes the motive after an arbitrary nonempty dependent
extension; the declaration S can depend on its whole context. -/
example {E F : Cat.{0,0}} (e : NormalizedEquivalence E F) (S : F ⥤ Cat.{0,0})
    (d : Section ((e.extend S).equiv.functor ⋙ before (Cat.of (Grothendieck S)))) :
    (eliminateSection (e.extend S) (before _) d).mapFamily (familyMap _) =
      eliminateSection (e.extend S) (after _)
        (d.mapFamily (whiskerLeft (e.extend S).equiv.functor (familyMap _))) :=
  eliminateSection_mapFamily (e.extend S) (familyMap _) d

/-- Any finite dependent telescope is allowed; the family map is the same
noninvertible map retaining all C4 labels. -/
example {E F K : Cat.{0,0}} (e : NormalizedEquivalence E F) (T : Telescope F K)
    (d : Section ((T.reindex e).2.2.equiv.functor ⋙ before K)) :
    (eliminateSection (T.reindex e).2.2 (before K) d).mapFamily (familyMap K) =
      eliminateSection (T.reindex e).2.2 (after K)
        (d.mapFamily (whiskerLeft (T.reindex e).2.2.equiv.functor (familyMap K))) :=
  eliminateSection_mapFamily (T.reindex e).2.2 (familyMap K) d

end Examples.FamilyMapElimination
