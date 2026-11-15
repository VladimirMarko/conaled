import SquareKit.Internal.Cubical.Judgments.FillingSyntax

/-! Face restrictions and selected providers are preserved by typed
substitution. Primitive substitution rules retain those selected providers. -/
namespace SquareKit.Cubical.Source.Fillings
open GuardedTheory

abbrev contextSchema (out : Judgment (Fin 1)) : Rule signature where
  parameterCount := 1
  hypotheses := 1
  premise := ![context (.var 0)]
  conclusion := out
abbrev faceTopRule := contextSchema (face (.var 0) (faceTop (.var 0)))
abbrev faceBotRule := contextSchema (face (.var 0) (faceBot (.var 0)))
abbrev faceSchema (out : Judgment (Fin 2)) : Rule signature where
  parameterCount := 2
  hypotheses := 1
  premise := ![face (.var 0) (.var 1)]
  conclusion := out
abbrev restrictionRule := faceSchema (context (restriction (.var 0) (.var 1)))
abbrev inclusionRule := faceSchema
  (substitution (restriction (.var 0) (.var 1)) (.var 0) (inclusion (.var 0) (.var 1)))
abbrev faceJoinRule : Rule signature where
  parameterCount := 3
  hypotheses := 2
  premise := ![face (.var 0) (.var 1),face (.var 0) (.var 2)]
  conclusion := face (.var 0) (faceJoin (.var 0) (.var 1) (.var 2))
abbrev faceEndpointRule (b : Bool) : Rule signature where
  parameterCount := 2
  hypotheses := 1
  premise := ![term (.var 0) (interval (.var 0)) (.var 1)]
  conclusion := face (.var 0) (faceEndpoint (.var 0) (.var 1) b)
abbrev faceSubSchema (out : Judgment (Fin 4)) : Rule signature where
  parameterCount := 4
  hypotheses := 2
  premise := ![face (.var 1) (.var 2),substitution (.var 0) (.var 1) (.var 3)]
  conclusion := out
abbrev faceSubRule := faceSubSchema (face (.var 0) (subFace (.var 0) (.var 1) (.var 2) (.var 3)))
abbrev restrictedSubRule := faceSubSchema
  (substitution (restriction (.var 0) (subFace (.var 0) (.var 1) (.var 2) (.var 3)))
    (restriction (.var 1) (.var 2)) (restrictedSub (.var 0) (.var 1) (.var 2) (.var 3)))
abbrev providerSubRule : Rule signature where
  parameterCount := 5
  hypotheses := 2
  premise := ![provider (.var 1) (.var 2) (.var 3),substitution (.var 0) (.var 1) (.var 4)]
  conclusion := provider (.var 0) (subTy (.var 2) (.var 4)) (subProvider (.var 0) (.var 1) (.var 3) (.var 4))

abbrev hcompSubSchema (out : Judgment (Fin 8)) : Rule signature where
  parameterCount := 8
  hypotheses := 6
  premise i := if h : i.val < 5 then
    (hcompRule.premise ⟨i.val,h⟩).subst (fun j => .var (![0,2,3,4,5,6] j))
    else substitution (.var 1) (.var 0) (.var 7)
  conclusion := out
abbrev hcompSubRule := hcompSubSchema
  (.eq (subTm (hcomp (.var 0) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6)) (.var 7))
    (hcomp (.var 1) (subTy (.var 2) (.var 7)) (subProvider (.var 1) (.var 0) (.var 3) (.var 7))
      (subFace (.var 1) (.var 0) (.var 4) (.var 7))
      (subTm (.var 5) (restrictedSub (intervalContext (.var 1)) (intervalContext (.var 0))
        (intervalFace (.var 0) (.var 4)) (lift (.var 1) (.var 0) (.var 7))))
      (subTm (.var 6) (.var 7))))

abbrev transpSubSchema (out : Judgment (Fin 7)) : Rule signature where
  parameterCount := 7
  hypotheses := 5
  premise i := if h : i.val < 4 then
    (transpRule.premise ⟨i.val,h⟩).subst (fun j => .var (![0,2,3,4,5] j))
    else substitution (.var 1) (.var 0) (.var 6)
  conclusion := out
abbrev transpSubRule := transpSubSchema
  (.eq (subTm (transp (.var 0) (.var 2) (.var 3) (.var 4) (.var 5)) (.var 6))
    (transp (.var 1) (subTy (.var 2) (lift (.var 1) (.var 0) (.var 6)))
      (subProvider (intervalContext (.var 1)) (intervalContext (.var 0)) (.var 3) (lift (.var 1) (.var 0) (.var 6)))
      (subFace (.var 1) (.var 0) (.var 4) (.var 6)) (subTm (.var 5) (.var 6))))

end SquareKit.Cubical.Source.Fillings
