import SquareKit.Internal.DependentJudgments.LeftTransportCompositionInputs

/-! First-path elimination for transport composition. The dependent tail is
z, q : y = z, u : B(x). The family B may depend on the generic first path.
The resulting certificate can be reindexed along any typed source map. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory LeftConcatFrame
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)} {Γ A x B Δ σ : Expression V}
namespace LeftTransportComposition
namespace Frame
variable (hx : Tm (Ω := Ω) Γ A x)
  (hB : Ty (Ω := Ω) (Contextual.extend (path A x) (pathType Γ A x)) B)
def firstQ := ((SourcePath.generic hx).substitute (pathTypeTyped hx).weaken).substitute (qTypeTyped hx).weaken
def familyZ := hB.substitute ((pathTypeTyped hx).weaken.lift (pathTypeTyped hx))
def familyQ := (familyZ hx hB).substitute ((qTypeTyped hx).weaken.lift (zTyped hx).family)
abbrev elementType := subTy (subTy (subTy B
  (liftSyntax (withZ Γ A x) (pathType Γ A x) (zProjection Γ A x)))
  (liftSyntax (withQ Γ A x) (zType Γ A x) (qProjection Γ A x)))
  (sectionSub (withQ Γ A x) (finalType Γ A x) (finalFixed Γ A x))
def elementTypeTyped : Ty (Ω := Ω) (withQ Γ A x) (elementType (Γ := Γ) (A := A) (x := x) (B := B)) :=
  (familyQ hx hB).substitute (finalFixedTyped hx).section
abbrev withU := Contextual.extend (withQ Γ A x) (elementType (Γ := Γ) (A := A) (x := x) (B := B))
abbrev uProjection := Contextual.weaken (withQ Γ A x) (elementType (Γ := Γ) (A := A) (x := x) (B := B))
def firstU := (firstQ hx).substitute (elementTypeTyped hx hB).weaken
def familyU := (familyQ hx hB).substitute ((elementTypeTyped hx hB).weaken.lift (finalFixedTyped hx).family)
def thirdU := (finalZTyped hx).substitute (elementTypeTyped hx hB).weaken
def secondPathU := ((qTyped hx).substitute (elementTypeTyped hx hB).weaken).convert
  ((finalMovingTyped hx).identitySub (finalZTyped hx) (elementTypeTyped hx hB).weaken)
def elementU := (elementTypeTyped hx hB).generic.convert
  ((familyQ hx hB).sectionLift (elementTypeTyped hx hB).weaken (finalFixedTyped hx)).symmetric

def inputs : Inputs Ω (withU (Γ := Γ) (A := A) (x := x) (B := B)) where
  first := firstU hx hB
  B := _
  z := _
  q := _
  u := _
  family := familyU hx hB
  third := thirdU hx hB
  secondPath := secondPathU hx hB
  element := elementU hx hB

abbrev tail : Reference.Tail V := .cons (pathType Γ A x)
  (.cons (qType Γ A x) (.cons (elementType (Γ := Γ) (A := A) (x := x) (B := B)) .nil))
def tailTyped : Reference.Presented Ω (path A x) (tail (Γ := Γ) (A := A) (x := x) (B := B)) :=
  .cons (pathTypeTyped hx) (.cons (qTypeTyped hx)
    (.cons (elementTypeTyped hx hB) (.nil (elementTypeTyped hx hB).extend)))
def rootU := (rootLiftQ hx).lift (elementTypeTyped hx hB)
def rootEvidence : ReflexiveRoot (inputs hx hB).first (rootU hx hB) :=
  (((ReflexiveRoot.generic hx).under (pathTypeTyped hx)).under (qTypeTyped hx)).under
    (elementTypeTyped hx hB)
def branch := (inputs hx hB).rootBranch (rootU hx hB) (rootEvidence hx hB)
abbrev certificate : Expression V := j A x ((tail (Γ := Γ) (A := A) (x := x) (B := B)).code (path A x))
  (inputs hx hB).motive
  (Contextual.reflexivity ((inputs hx hB).substitute (rootU hx hB)).resultType
    ((inputs hx hB).substitute (rootU hx hB)).left)
def derivation : Tm (Ω := Ω) (withU (Γ := Γ) (A := A) (x := x) (B := B))
    (inputs hx hB).motive (certificate hx hB) :=
  Presented.eliminate hx (tailTyped hx hB) (inputs hx hB).motiveTyped (branch hx hB)

def beta : Equal (Ω := Ω)
    (subTm (certificate hx hB) ((tail (Γ := Γ) (A := A) (x := x) (B := B)).map Γ (root A x)))
    (Contextual.reflexivity ((inputs hx hB).substitute (rootU hx hB)).resultType
      ((inputs hx hB).substitute (rootU hx hB)).left) :=
  Presented.beta hx (tailTyped hx hB) (inputs hx hB).motiveTyped (branch hx hB)

/-- Reindexing retains the explicit freshly substituted transport statement. -/
def reindex (hs : Sub (Ω := Ω) Δ (withU (Γ := Γ) (A := A) (x := x) (B := B)) σ) :
    Tm (Ω := Ω) Δ ((inputs hx hB).substitute hs).motive (subTm (certificate hx hB) σ) :=
  ((derivation hx hB).substitute hs).convert ((inputs hx hB).motiveSub hs)
end Frame
end LeftTransportComposition
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
