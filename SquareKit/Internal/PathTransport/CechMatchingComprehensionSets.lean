import SquareKit.Internal.PathTransport.CechMatchingComprehensionEquivalence
import SquareKit.Internal.PathTransport.CechMatchingSetFamily

/-! In discrete fibers the selected overlap is an equality. The total matching
laws follow from the base laws because vertical arrows are unique. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory CategoryTheory.Functor
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

private theorem totalArrow_ext {C : Grpd.{u,u}} (F : C ⥤ Grpd.{u,u})
    [∀ c, Quiver.IsThin (F.obj c)] {x y : Extend F} (f g : x ⟶ y)
    (hb : f.base = g.base) : f = g :=
  Grothendieck.ext f g hb (Subsingleton.elim _ _)

variable {D : StrictDiagram.{u,u}} {A : FamilyData D} {h : A.Coherence}
variable [∀ c, Quiver.IsThin (A.localFamily.obj c)]
  [∀ c, Quiver.IsThin (A.tripleFamily.obj c)]

/-- With thin local and triple fibers, every overlap over the supplied base
satisfies the diagonal and triple laws. -/
def Fiber.ofOverlap (d : Datum D.toDiagram) (x : A.localFamily.obj d.localObject)
    (i : A.firstMap.obj (liftLocal A d x) ≅ A.secondMap.obj (liftLocal A d x))
    (hb : i.hom.base = d.overlap.hom) : Fiber A h d where
  localFiber := x
  overlap := i
  base_overlap := hb
  diagonal := by
    apply totalArrow_ext A.localFamily
    change D.diagonal.map i.hom.base = _
    rw [hb]
    change D.diagonal.map d.overlap.hom =
      ((eqToHom h.diagonalFirst).app (liftLocal A d x) ≫
        (eqToHom h.diagonalSecond.symm).app (liftLocal A d x)).base
    simp only [eqToHom_app]
    change D.diagonal.map d.overlap.hom =
      (Grothendieck.comp (eqToHom (CategoryTheory.Functor.congr_obj h.diagonalFirst (liftLocal A d x)))
        (eqToHom (CategoryTheory.Functor.congr_obj h.diagonalSecond.symm (liftLocal A d x)))).base
    dsimp only [Grothendieck.comp]
    rw [Grothendieck.base_eqToHom, Grothendieck.base_eqToHom]
    simpa only [StrictDiagram.toDiagram, eqToIso.hom, eqToIso.inv, eqToHom_app] using d.diagonal
  cocycle := by
    apply totalArrow_ext A.tripleFamily
    change D.firstSecond.map i.hom.base ≫
      ((eqToHom h.tripleMiddle).app (liftLocal A d x)).base ≫
        D.secondThird.map i.hom.base =
      ((eqToHom h.tripleFirst).app (liftLocal A d x)).base ≫
        D.firstThird.map i.hom.base ≫ ((eqToHom h.tripleLast).app (liftLocal A d x)).base
    rw [hb]
    simp only [eqToHom_app]
    rw [Grothendieck.base_eqToHom, Grothendieck.base_eqToHom, Grothendieck.base_eqToHom]
    simpa only [StrictDiagram.toDiagram, eqToIso.hom, eqToHom_app] using d.cocycle

/-- Set-valued restrictions, prior to imposing total diagram coherence. -/
structure SetData (D : StrictDiagram.{u,u}) where
  localFamily : D.localCategory ⥤ Type u
  doubleFamily : D.doubleCategory ⥤ Type u
  tripleFamily : D.tripleCategory ⥤ Type u
  first : localFamily ⟶ D.first ⋙ doubleFamily
  second : localFamily ⟶ D.second ⋙ doubleFamily
  diagonal : doubleFamily ⟶ D.diagonal ⋙ localFamily
  firstSecond : doubleFamily ⟶ D.firstSecond ⋙ tripleFamily
  firstThird : doubleFamily ⟶ D.firstThird ⋙ tripleFamily
  secondThird : doubleFamily ⟶ D.secondThird ⋙ tripleFamily

namespace SetData
variable (S : SetData D)

def toFamilyData : FamilyData D where
  localFamily := setFamily S.localFamily
  doubleFamily := setFamily S.doubleFamily
  tripleFamily := setFamily S.tripleFamily
  first := whiskerRight S.first discrete
  second := whiskerRight S.second discrete
  diagonal := whiskerRight S.diagonal discrete
  firstSecond := whiskerRight S.firstSecond discrete
  firstThird := whiskerRight S.firstThird discrete
  secondThird := whiskerRight S.secondThird discrete

instance (c : D.localCategory) : Quiver.IsThin (S.toFamilyData.localFamily.obj c) :=
  inferInstanceAs (Quiver.IsThin (Discrete (S.localFamily.obj c)))
instance (c : D.doubleCategory) : Quiver.IsThin (S.toFamilyData.doubleFamily.obj c) :=
  inferInstanceAs (Quiver.IsThin (Discrete (S.doubleFamily.obj c)))
instance (c : D.tripleCategory) : Quiver.IsThin (S.toFamilyData.tripleFamily.obj c) :=
  inferInstanceAs (Quiver.IsThin (Discrete (S.tripleFamily.obj c)))

variable (hs : S.toFamilyData.Coherence) (d : Datum D.toDiagram)

abbrev MatchingSet := SetFamily.Fiber S.localFamily S.doubleFamily S.first S.second d

def toSet (x : Fiber S.toFamilyData hs d) : S.MatchingSet d := by
  refine ⟨x.localFiber.as, ?_⟩
  have he := Discrete.eq_of_hom x.overlap.hom.fiber
  change S.doubleFamily.map x.overlap.hom.base
    (S.first.app d.localObject x.localFiber.as) = S.second.app d.localObject x.localFiber.as at he
  rw [x.base_overlap] at he
  exact he

def fromSet (x : S.MatchingSet d) : Fiber S.toFamilyData hs d :=
  Fiber.ofOverlap d (Discrete.mk x.val)
    (Grothendieck.isoMk d.overlap (eqToIso (Discrete.ext x.property))) rfl

@[simp] theorem toSet_fromSet (x : S.MatchingSet d) :
    S.toSet hs d (S.fromSet hs d x) = x := Subtype.ext rfl

@[simp] theorem fromSet_toSet (x : Fiber S.toFamilyData hs d) :
    S.fromSet hs d (S.toSet hs d x) = x := by
  apply Fiber.datum_injective
  refine Datum.ext (d := (S.fromSet hs d (S.toSet hs d x)).datum) (e := x.datum) rfl ?_
  apply heq_of_eq
  apply Iso.ext
  apply totalArrow_ext S.toFamilyData.doubleFamily
  exact x.base_overlap.symm

/-- The general relative fiber is exactly the local values satisfying the
selected overlap equation, with no additional global-extension hypothesis. -/
def setEquiv : Fiber S.toFamilyData hs d ≃ S.MatchingSet d where
  toFun := S.toSet hs d
  invFun := S.fromSet hs d
  left_inv := S.fromSet_toSet hs d
  right_inv := S.toSet_fromSet hs d

@[simp] theorem setEquiv_transport {d e : Datum D.toDiagram} (f : d ⟶ e)
    (x : Fiber S.toFamilyData hs d) :
    S.setEquiv hs e (Fiber.transport f x) =
      SetFamily.map S.localFamily S.doubleFamily S.first S.second f (S.setEquiv hs d x) := by
  apply Subtype.ext
  exact congrArg Discrete.as (Fiber.transport_localFiber f x)

instance (x y : Fiber S.toFamilyData hs d) : Subsingleton (x ⟶ y) where
  allEq f g := by
    apply Fiber.Hom.ext
    apply Datum.Hom.ext
    exact totalArrow_ext S.toFamilyData.localFamily _ _ (f.vertical.trans g.vertical.symm)

/-- A vertical arrow of set matching exists precisely when the matching values
are equal; there are no additional path witnesses in these fibers. -/
theorem arrow_iff (x y : Fiber S.toFamilyData hs d) :
    Nonempty (x ⟶ y) ↔ S.setEquiv hs d x = S.setEquiv hs d y := by
  constructor
  · rintro ⟨f⟩
    apply Subtype.ext
    have he := Discrete.eq_of_hom f.matchingArrow.localArrow.fiber
    change S.localFamily.map f.matchingArrow.localArrow.base x.localFiber.as = y.localFiber.as at he
    rw [f.vertical] at he
    exact (ConcreteCategory.congr_hom (S.localFamily.map_id d.localObject)
      x.localFiber.as).symm.trans he
  · intro he
    have hh := (S.setEquiv hs d).injective he
    exact ⟨eqToHom hh⟩

end SetData

end SquareKit.Internal.PathTransport.CechMatching.Comprehension
