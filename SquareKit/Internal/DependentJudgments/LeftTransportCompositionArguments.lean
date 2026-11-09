import SquareKit.Internal.DependentJudgments.LeftTransportComposition
import SquareKit.Internal.DependentJudgments.SourcePathArguments

/-! The ordinary transport-composition caller: all family and element
conversions are generated from typed inputs and comprehension equations. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory LeftConcatFrame
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)} {Γ Δ A B E σ t : Expression V}
namespace LeftTransportComposition
private def displayWeakenPair (hA : Ty (Ω := Ω) Γ A)
    (hB : Ty (Ω := Ω) (Contextual.extend Γ A) B) (hE : Ty (Ω := Ω) Γ E)
    (hs : Sub (Ω := Ω) Δ Γ σ) (ht : Tm (Ω := Ω) Δ (subTy E σ) t) :
    Equal (Ω := Ω)
      (subTy (subTy B (liftSyntax (Contextual.extend Γ E) A (Contextual.weaken Γ E)))
        (liftSyntax Δ (subTy A (Contextual.weaken Γ E)) (Contextual.pair E σ t)))
      (subTy B (liftSyntax Δ A σ)) :=
  (hB.liftSubComp hA hE.weaken (Sub.pair hE hs ht)).transitive
    (Equal.subTy (.reflexive _) (Equal.liftSyntax (.reflexive _) (.reflexive _)
      (hE.weakenPair hs ht)))
namespace Arguments
variable (C : Inputs Ω Γ)
abbrev pathFamily : Expression V := subTy
  (subTy C.B (liftSyntax (Contextual.extend Γ C.first.A) C.first.A (Contextual.weaken Γ C.first.A)))
  (liftSyntax (path C.first.A C.first.x) (subTy C.first.A (Contextual.weaken Γ C.first.A))
    (pathProjection Γ C.first.A C.first.x))
abbrev zFamily : Expression V := subTy (pathFamily C)
  (liftSyntax (withZ Γ C.first.A C.first.x) (pathType Γ C.first.A C.first.x)
    (zProjection Γ C.first.A C.first.x))
abbrev qFamily : Expression V := subTy (zFamily C)
  (liftSyntax (withQ Γ C.first.A C.first.x) (zType Γ C.first.A C.first.x)
    (qProjection Γ C.first.A C.first.x))
def familyExtended := C.family.substitute (C.first.first.family.weaken.lift C.first.first.family)
def familyPath := (familyExtended C).substitute
  (C.first.first.pathProjection.lift (C.first.first.family.substitute C.first.first.family.weaken))
def atPathTyped := C.first.first.endpoint C.first.second C.first.proof
def familyAtPath : Equal (Ω := Ω)
    (subTy (pathFamily C) (liftSyntax Γ (pathType Γ C.first.A C.first.x)
      (Contextual.endpoint Γ C.first.A C.first.x C.first.y C.first.p))) C.B :=
  ((familyExtended C).liftSubComp (C.first.first.family.substitute C.first.first.family.weaken)
    C.first.first.pathProjection (atPathTyped C)).transitive
    ((Equal.subTy (.reflexive _) (Equal.liftSyntax (.reflexive _) (.reflexive _)
      (C.first.first.endpointProjection C.first.second C.first.proof))).transitive
      ((C.family.liftSubComp C.first.first.family C.first.first.family.weaken C.first.second.section).transitive
        ((Equal.subTy (.reflexive _) (Equal.liftSyntax (.reflexive _) (.reflexive _)
          C.first.second.sectionWeaken)).transitive
          ((Equal.subTy (.reflexive _) C.first.first.family.liftId).transitive C.family.subId))))
abbrev atQ := LeftConcatArguments.atQ Γ C.first.A C.first.x C.first.y C.z C.first.p C.q
def atQTyped := LeftConcatArguments.atQTyped C.first.first C.first.second C.third C.first.proof C.secondPath
def pathAtQ := ((PathArguments.generic C.first).under (pathTypeTyped C.first.first)
  (LeftConcatArguments.zArgument C.first.first C.first.second C.third C.first.proof)).under
  (qTypeTyped C.first.first)
  (LeftConcatArguments.qArgument C.first.first C.first.second C.third C.first.proof C.secondPath)
def familyAtZ : Equal (Ω := Ω)
    (subTy (zFamily C) (liftSyntax Γ (zType Γ C.first.A C.first.x)
      (LeftConcatArguments.atZ Γ C.first.A C.first.x C.first.y C.z C.first.p))) C.B :=
  (displayWeakenPair (pathTypeTyped C.first.first) (familyPath C) (pathTypeTyped C.first.first)
    (atPathTyped C) (LeftConcatArguments.zArgument C.first.first C.first.second C.third C.first.proof)).transitive
    (familyAtPath C)
def familyAtQ : Equal (Ω := Ω)
    (subTy (qFamily C) (liftSyntax Γ (finalType Γ C.first.A C.first.x) (atQ C))) C.B :=
  (displayWeakenPair (zTyped C.first.first).family (Frame.familyZ C.first.first (familyPath C))
    (qTypeTyped C.first.first)
    (LeftConcatArguments.atZTyped C.first.first C.first.second C.third C.first.proof)
    (LeftConcatArguments.qArgument C.first.first C.first.second C.third C.first.proof C.secondPath)).transitive
    (familyAtZ C)
def elementTypeAt : Equal (Ω := Ω)
    (subTy (Frame.elementType (Γ := Γ) (A := C.first.A) (x := C.first.x) (B := pathFamily C)) (atQ C))
      (subTy C.B (sectionSub Γ C.first.A C.first.x)) :=
  ((Frame.familyQ C.first.first (familyPath C)).sectionLift (atQTyped C)
    (finalFixedTyped C.first.first)).symmetric.transitive
      (Equal.subTy (familyAtQ C) (Equal.pair (pathAtQ C).carrier (.reflexive _) (pathAtQ C).first))
def elementArgument := C.element.convert (elementTypeAt C).symmetric
abbrev atU := Contextual.pair (Frame.elementType (Γ := Γ) (A := C.first.A) (x := C.first.x) (B := pathFamily C)) (atQ C) C.u
def atUTyped := Sub.pair (Frame.elementTypeTyped C.first.first (familyPath C)) (atQTyped C) (elementArgument C)
def pathAtU := (pathAtQ C).under (Frame.elementTypeTyped C.first.first (familyPath C)) (elementArgument C)
def familyAtU : Equal (Ω := Ω)
    (subTy (Frame.inputs C.first.first (familyPath C)).B
      (liftSyntax Γ (Frame.inputs C.first.first (familyPath C)).first.A (atU C))) C.B :=
  (displayWeakenPair (finalFixedTyped C.first.first).family (Frame.familyQ C.first.first (familyPath C))
    (Frame.elementTypeTyped C.first.first (familyPath C)) (atQTyped C) (elementArgument C)).transitive
    (familyAtQ C)
def zAt : Equal (Ω := Ω) (subTm (Frame.inputs C.first.first (familyPath C)).z (atU C)) C.z :=
  ((finalZTyped C.first.first).weakenPair (Frame.elementTypeTyped C.first.first (familyPath C))
    (atQTyped C) (elementArgument C)).transitive
    (LeftConcatArguments.finalZAt C.first.first C.first.second C.third C.first.proof C.secondPath)
def qAt : Equal (Ω := Ω) (subTm (Frame.inputs C.first.first (familyPath C)).q (atU C)) C.q :=
  ((qTyped C.first.first).weakenPair (Frame.elementTypeTyped C.first.first (familyPath C))
    (atQTyped C) (elementArgument C)).transitive
    ((qTypeTyped C.first.first).variablePair
      (LeftConcatArguments.atZTyped C.first.first C.first.second C.third C.first.proof)
      (LeftConcatArguments.qArgument C.first.first C.first.second C.third C.first.proof C.secondPath))
def uAt : Equal (Ω := Ω) (subTm (Frame.inputs C.first.first (familyPath C)).u (atU C)) C.u :=
  (Frame.elementTypeTyped C.first.first (familyPath C)).variablePair (atQTyped C) (elementArgument C)
def motiveAt : Equal (Ω := Ω)
    (subTy (Frame.inputs C.first.first (familyPath C)).motive (atU C)) C.motive :=
  ((Frame.inputs C.first.first (familyPath C)).motiveSub (atUTyped C)).transitive
    (((Frame.inputs C.first.first (familyPath C)).substitute (atUTyped C)).motiveCongr
      (pathAtU C).carrier (familyAtU C) (pathAtU C).first (pathAtU C).second
      (zAt C) (pathAtU C).proof (qAt C) (uAt C))
end Arguments
namespace Inputs
variable (C : Inputs Ω Γ)
abbrev certificate : Expression V :=
  subTm (Frame.certificate C.first.first (Arguments.familyPath C)) (Arguments.atU C)
/-- First-path J proves transport along concatenation for arbitrary typed
paths, dependent family, and element. No presentation equations are inputs. -/
def composition : Tm (Ω := Ω) Γ C.motive C.certificate :=
  ((Frame.derivation C.first.first (Arguments.familyPath C)).substitute (Arguments.atUTyped C)).convert
    (Arguments.motiveAt C)
end Inputs
end LeftTransportComposition
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
