import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberFunctor
import SquareKit.Internal.PathTransport.CechMatchingMapComposition
import SquareKit.Internal.PathTransport.GrothendieckPreComparison

/-! Pullback of relative matching diagrams retains the actual restriction maps. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension.Pull
open CategoryTheory CategoryTheory.Functor
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D E : StrictDiagram.{u,u}} (S : StrictMap D E) (A : FamilyData E)

def data : FamilyData D where
  localFamily := S.localMap ⋙ A.localFamily
  doubleFamily := S.doubleMap ⋙ A.doubleFamily
  tripleFamily := S.tripleMap ⋙ A.tripleFamily
  first := whiskerLeft S.localMap A.first ≫ eqToHom (congrArg (· ⋙ A.doubleFamily) S.first)
  second := whiskerLeft S.localMap A.second ≫ eqToHom (congrArg (· ⋙ A.doubleFamily) S.second)
  diagonal := whiskerLeft S.doubleMap A.diagonal ≫ eqToHom (congrArg (· ⋙ A.localFamily) S.diagonal)
  firstSecond := whiskerLeft S.doubleMap A.firstSecond ≫ eqToHom (congrArg (· ⋙ A.tripleFamily) S.firstSecond)
  firstThird := whiskerLeft S.doubleMap A.firstThird ≫ eqToHom (congrArg (· ⋙ A.tripleFamily) S.firstThird)
  secondThird := whiskerLeft S.doubleMap A.secondThird ≫ eqToHom (congrArg (· ⋙ A.tripleFamily) S.secondThird)

variable (h : A.Coherence) (hp : (data S A).Coherence)

def totalMap : StrictMap ((data S A).total hp) (A.total h) where
  localMap := Grothendieck.pre (A.localFamily ⋙ Grpd.forgetToCat) S.localMap
  doubleMap := Grothendieck.pre (A.doubleFamily ⋙ Grpd.forgetToCat) S.doubleMap
  tripleMap := Grothendieck.pre (A.tripleFamily ⋙ Grpd.forgetToCat) S.tripleMap
  first := Comparison.pre_totalMap _ _ _ _ _ S.first
  second := Comparison.pre_totalMap _ _ _ _ _ S.second
  diagonal := Comparison.pre_totalMap _ _ _ _ _ S.diagonal
  firstSecond := Comparison.pre_totalMap _ _ _ _ _ S.firstSecond
  firstThird := Comparison.pre_totalMap _ _ _ _ _ S.firstThird
  secondThird := Comparison.pre_totalMap _ _ _ _ _ S.secondThird

theorem projection : (totalMap S A h hp).comp (A.projection h) =
    ((data S A).projection hp).comp S := StrictMap.ext _ _ rfl rfl rfl

end SquareKit.Internal.PathTransport.CechMatching.Comprehension.Pull
