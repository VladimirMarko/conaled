import Mathlib.CategoryTheory.Whiskering
import SquareKit.Internal.PathTransport.CechMatching
import SquareKit.Internal.PathTransport.GroupoidSoundness

/-! Universe lifting preserves independently specified matching objects,
selected overlaps and all local arrows. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.UniverseLift
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable (D : Diagram.{u,v})

def diagram : Diagram.{max u v w, max u v w} where
  localCategory := Grpd.of (AsSmall.{w} D.localCategory)
  doubleCategory := Grpd.of (AsSmall.{w} D.doubleCategory)
  tripleCategory := Grpd.of (AsSmall.{w} D.tripleCategory)
  first := AsSmall.down ⋙ D.first ⋙ AsSmall.up
  second := AsSmall.down ⋙ D.second ⋙ AsSmall.up
  diagonal := AsSmall.down ⋙ D.diagonal ⋙ AsSmall.up
  firstSecond := AsSmall.down ⋙ D.firstSecond ⋙ AsSmall.up
  firstThird := AsSmall.down ⋙ D.firstThird ⋙ AsSmall.up
  secondThird := AsSmall.down ⋙ D.secondThird ⋙ AsSmall.up
  diagonalFirst := isoWhiskerLeft AsSmall.down (isoWhiskerRight D.diagonalFirst AsSmall.up)
  diagonalSecond := isoWhiskerLeft AsSmall.down (isoWhiskerRight D.diagonalSecond AsSmall.up)
  tripleFirst := isoWhiskerLeft AsSmall.down (isoWhiskerRight D.tripleFirst AsSmall.up)
  tripleMiddle := isoWhiskerLeft AsSmall.down (isoWhiskerRight D.tripleMiddle AsSmall.up)
  tripleLast := isoWhiskerLeft AsSmall.down (isoWhiskerRight D.tripleLast AsSmall.up)

def upDatum (d : Datum D) : Datum (diagram.{u,v,w} D) where
  localObject := AsSmall.up.obj d.localObject
  overlap := AsSmall.up.mapIso d.overlap
  diagonal := by
    apply ULift.ext
    exact d.diagonal
  cocycle := by
    apply ULift.ext
    exact d.cocycle

def downDatum (d : Datum (diagram.{u,v,w} D)) : Datum D where
  localObject := AsSmall.down.obj d.localObject
  overlap := AsSmall.down.mapIso d.overlap
  diagonal := congrArg ULift.down d.diagonal
  cocycle := congrArg ULift.down d.cocycle

def up : Datum D ⥤ Datum (diagram.{u,v,w} D) where
  obj := upDatum D
  map f := ⟨AsSmall.up.map f.localArrow, by
    apply ULift.ext
    exact f.commutes⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def down : Datum (diagram.{u,v,w} D) ⥤ Datum D where
  obj := downDatum D
  map f := ⟨AsSmall.down.map f.localArrow, congrArg ULift.down f.commutes⟩
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem down_up : up.{u,v,w} D ⋙ down D = 𝟭 (Datum D) := rfl
@[simp] theorem up_down : down D ⋙ up D = 𝟭 (Datum (diagram.{u,v,w} D)) := rfl

def equivalence : Datum D ≌ Datum (diagram.{u,v,w} D) where
  functor := up D
  inverse := down D
  unitIso := eqToIso (down_up D).symm
  counitIso := eqToIso (up_down D)

/-- The small matching groupoid agrees with matching in the small diagram. -/
def asSmallEquivalence : AsSmall.{w} (Datum D) ≌ Datum (diagram.{u,v,w} D) :=
  (AsSmall.equiv (C := Datum D)).symm.trans (equivalence D)

@[simp] theorem up_localArrow {d e : Datum D} (f : d ⟶ e) :
    ((up.{u,v,w} D).map f).localArrow = AsSmall.up.map f.localArrow := rfl

/-- The projection is the original local-object functor with only universe wrappers. -/
theorem asSmall_local : (asSmallEquivalence.{u,v,w} D).functor ⋙ Datum.localFunctor =
    AsSmall.down ⋙ Datum.localFunctor ⋙ AsSmall.up := rfl

@[simp] theorem asSmall_overlap (d : AsSmall.{w} (Datum D)) :
    ((asSmallEquivalence D).functor.obj d).overlap =
      AsSmall.up.mapIso (AsSmall.down.obj d).overlap := rfl

@[simp] theorem asSmall_localArrow {d e : AsSmall.{w} (Datum D)} (f : d ⟶ e) :
    ((asSmallEquivalence D).functor.map f).localArrow.down = f.down.localArrow := rfl

end SquareKit.Internal.PathTransport.CechMatching.UniverseLift
