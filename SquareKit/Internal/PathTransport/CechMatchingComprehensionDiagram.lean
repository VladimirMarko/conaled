import SquareKit.Internal.PathTransport.CechMatchingMap
import SquareKit.Internal.PathTransport.ComparisonComposition

/-! A displayed truncated diagram builds its total diagram from actual
Grothendieck maps. Only restriction coherence, not matching effectiveness, is input. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (D : StrictDiagram.{u,u})

structure FamilyData where
  localFamily : D.localCategory ⥤ Grpd.{u,u}
  doubleFamily : D.doubleCategory ⥤ Grpd.{u,u}
  tripleFamily : D.tripleCategory ⥤ Grpd.{u,u}
  first : localFamily ⟶ D.first ⋙ doubleFamily
  second : localFamily ⟶ D.second ⋙ doubleFamily
  diagonal : doubleFamily ⟶ D.diagonal ⋙ localFamily
  firstSecond : doubleFamily ⟶ D.firstSecond ⋙ tripleFamily
  firstThird : doubleFamily ⟶ D.firstThird ⋙ tripleFamily
  secondThird : doubleFamily ⟶ D.secondThird ⋙ tripleFamily

namespace FamilyData
variable {D} (A : FamilyData D)

abbrev localTotal := @Grpd.of (Extend A.localFamily) Groupoid.ofIsGroupoid
abbrev doubleTotal := @Grpd.of (Extend A.doubleFamily) Groupoid.ofIsGroupoid
abbrev tripleTotal := @Grpd.of (Extend A.tripleFamily) Groupoid.ofIsGroupoid

abbrev firstMap := Comparison.totalMap D.first A.first
abbrev secondMap := Comparison.totalMap D.second A.second
abbrev diagonalMap := Comparison.totalMap D.diagonal A.diagonal
abbrev firstSecondMap := Comparison.totalMap D.firstSecond A.firstSecond
abbrev firstThirdMap := Comparison.totalMap D.firstThird A.firstThird
abbrev secondThirdMap := Comparison.totalMap D.secondThird A.secondThird

structure Coherence : Prop where
  diagonalFirst : A.firstMap ⋙ A.diagonalMap = 𝟭 A.localTotal
  diagonalSecond : A.secondMap ⋙ A.diagonalMap = 𝟭 A.localTotal
  tripleFirst : A.firstMap ⋙ A.firstSecondMap = A.firstMap ⋙ A.firstThirdMap
  tripleMiddle : A.secondMap ⋙ A.firstSecondMap = A.firstMap ⋙ A.secondThirdMap
  tripleLast : A.secondMap ⋙ A.firstThirdMap = A.secondMap ⋙ A.secondThirdMap

def total (h : A.Coherence) : StrictDiagram.{u,u} where
  localCategory := A.localTotal
  doubleCategory := A.doubleTotal
  tripleCategory := A.tripleTotal
  first := A.firstMap
  second := A.secondMap
  diagonal := A.diagonalMap
  firstSecond := A.firstSecondMap
  firstThird := A.firstThirdMap
  secondThird := A.secondThirdMap
  diagonalFirst := h.diagonalFirst
  diagonalSecond := h.diagonalSecond
  tripleFirst := h.tripleFirst
  tripleMiddle := h.tripleMiddle
  tripleLast := h.tripleLast

def projection (h : A.Coherence) : StrictMap (A.total h) D where
  localMap := Grothendieck.forget _
  doubleMap := Grothendieck.forget _
  tripleMap := Grothendieck.forget _
  first := rfl
  second := rfl
  diagonal := rfl
  firstSecond := rfl
  firstThird := rfl
  secondThird := rfl

end FamilyData
end SquareKit.Internal.PathTransport.CechMatching.Comprehension
