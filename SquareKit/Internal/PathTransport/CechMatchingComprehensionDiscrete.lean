import SquareKit.Internal.PathTransport.CechMatchingComprehensionSets

/-! Set matching identifies the whole relative fiber groupoid with a discrete set. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension.SetData
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D : StrictDiagram.{u,u}} (S : SetData D)
variable (hs : S.toFamilyData.Coherence) (d : Datum D.toDiagram)

def toDiscrete : Fiber S.toFamilyData hs d ⥤ Discrete (S.MatchingSet d) where
  obj x := Discrete.mk (S.setEquiv hs d x)
  map f := eqToHom (congrArg Discrete.mk ((S.arrow_iff hs d _ _).mp ⟨f⟩))

def fromDiscrete : Discrete (S.MatchingSet d) ⥤ Fiber S.toFamilyData hs d :=
  Discrete.functor (S.fromSet hs d)

/-- Objects and all vertical arrows are recovered; discreteness is a consequence
of the set-valued fibers, not an assumption on the base groupoids. -/
def discreteEquivalence : Fiber S.toFamilyData hs d ≌ Discrete (S.MatchingSet d) where
  functor := S.toDiscrete hs d
  inverse := S.fromDiscrete hs d
  unitIso := NatIso.ofComponents (fun x => eqToIso (S.fromSet_toSet hs d x).symm)
    (by intros; apply Subsingleton.elim)
  counitIso := NatIso.ofComponents
    (fun x => eqToIso (Discrete.ext (S.toSet_fromSet hs d x.as)))
    (by intros; apply Subsingleton.elim)

@[simp] theorem discreteEquivalence_value (x : Fiber S.toFamilyData hs d) :
    ((S.discreteEquivalence hs d).functor.obj x).as.val = x.localFiber.as := rfl

end SquareKit.Internal.PathTransport.CechMatching.Comprehension.SetData
