import SquareKit.Internal.PathTransport.CechMatchingComprehensionPull
import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberMap
import SquareKit.Internal.PathTransport.GrothendieckPreFiber

/-! Reindexing retains all vertical matching arrows. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension.Pull
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D E : StrictDiagram.{u,u}} (S : StrictMap D E) (A : FamilyData E)
variable (h : A.Coherence) (hp : (data S A).Coherence) (d : Datum D.toDiagram)

def raw : Fiber (data S A) hp d ⥤ Datum (A.total h).toDiagram :=
  Fiber.forget ⋙ (totalMap S A h hp).functor

instance : (raw S A h hp d).Faithful where
  map_injective {x y} f g hh := by
    apply Fiber.Hom.ext
    apply Datum.Hom.ext
    exact GrothendieckPreFiber.map_injective_of_base
      (A.localFamily ⋙ Grpd.forgetToCat) S.localMap
      f.matchingArrow.localArrow g.matchingArrow.localArrow
      (f.vertical.trans g.vertical.symm) (congrArg Datum.Hom.localArrow hh)

def toFiber := fiberMap S (totalMap S A h hp) (projection S A h hp) d

instance : (toFiber S A h hp d).Faithful :=
  Functor.Faithful.of_comp_iso
    (fixedBaseComparison A h (raw S A h hp d) (S.functor.obj d)
      (fiberMap_projection S (totalMap S A h hp) (projection S A h hp) d))

end SquareKit.Internal.PathTransport.CechMatching.Comprehension.Pull
