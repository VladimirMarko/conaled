import SquareKit.Internal.DependentJudgments.DerivedCertificates

/-! Comprehension lift and its section square, derived in the source theory.
These are object-context substitutions, distinct from substitution for raw
metavariables in a recipe. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A B σ x : Expression V}

abbrev lift (Δ A σ : Expression V) : Expression V :=
  liftSyntax Δ A σ

def Sub.lift (hσ : Sub (Ω := Ω) Δ Γ σ) (hA : Ty (Ω := Ω) Γ A) :
    Sub (Ω := Ω) (Contextual.extend Δ (Contextual.subTy A σ)) (Contextual.extend Γ A) (Contextual.lift Δ A σ) :=
  Sub.pair hA (hσ.comp (hA.substitute hσ).weaken)
    ((hA.substitute hσ).generic.convert (hA.subComp hσ (hA.substitute hσ).weaken))

def Sub.liftSection (hσ : Sub (Ω := Ω) Δ Γ σ) (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (Contextual.comp (Contextual.lift Δ A σ) (Contextual.sectionSub Δ (Contextual.subTy A σ) (Contextual.subTm x σ)))
      (Contextual.comp (Contextual.sectionSub Γ A x) σ) := by
  have hxs := hx.substitute hσ
  have hAs := hx.family.substitute hσ
  have first := hx.family.pairComp (hσ.comp hAs.weaken)
    (hAs.generic.convert (hx.family.subComp hσ hAs.weaken)) hxs.section
  have base := ((hσ.assoc hAs.weaken hxs.section).transitive
    (Equal.comp (.reflexive σ) hxs.sectionWeaken)).transitive hσ.idRight
  have left : Equal (Ω := Ω) (Contextual.comp (Contextual.lift Δ A σ) (Contextual.sectionSub Δ (Contextual.subTy A σ) (Contextual.subTm x σ)))
      (Contextual.pair A σ (Contextual.subTm x σ)) := first.transitive
        (Equal.pair (.reflexive A) base hxs.sectionGeneric)
  have right := (hx.family.pairComp hx.family.context.identity
    (hx.convert hx.family.subId.symmetric) hσ).transitive
      (Equal.pair (.reflexive A) hσ.idLeft (.reflexive _))
  exact left.transitive right.symmetric

def Ty.sectionLift (hB : Ty (Ω := Ω) (Contextual.extend Γ A) B) (hσ : Sub (Ω := Ω) Δ Γ σ)
    (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (Contextual.subTy (Contextual.subTy B (Contextual.lift Δ A σ)) (Contextual.sectionSub Δ (Contextual.subTy A σ) (Contextual.subTm x σ)))
      (Contextual.subTy (Contextual.subTy B (Contextual.sectionSub Γ A x)) σ) :=
  ((hB.subComp (hσ.lift hx.family) (hx.substitute hσ).section).transitive
    (Equal.subTy (.reflexive B) (hσ.liftSection hx))).transitive (hB.subComp hx.section hσ).symmetric

def Equal.j {A A' x x' T T' D D' d d' : Expression V}
    (hA : Equal (Ω := Ω) A A') (hx : Equal (Ω := Ω) x x') (hT : Equal (Ω := Ω) T T')
    (hD : Equal (Ω := Ω) D D') (hd : Equal (Ω := Ω) d d') :
    Equal (Ω := Ω) (Contextual.j A x T D d) (Contextual.j A' x' T' D' d') :=
  Derivation.congruence (T := theory) (Sum.inr Operation.j)
    (Fin.cases hA (Fin.cases hx (Fin.cases hT (Fin.cases hD (Fin.cases hd (fun i => nomatch i))))))

def Tm.basedJSub {D d : Expression V} (hx : Tm (Ω := Ω) Γ A x)
    (hD : Ty (Ω := Ω) (Contextual.path A x) D)
    (hd : Tm (Ω := Ω) Γ (Contextual.subTy D (Contextual.root A x)) d)
    (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (Contextual.subTm (Contextual.basedJ A x D d) (Contextual.pathSub A x σ))
      (Contextual.basedJ (Contextual.subTy A σ) (Contextual.subTm x σ)
        (Contextual.subTy D (Contextual.pathSub A x σ)) (Contextual.subTm d σ)) := by
  have eT := hx.pathTailNil hx.path.nil hσ
  have eS := hx.pathTailMapNil hx.path.nil hσ
  have eD := hD.recontext hx.path.totalNil.symmetric
  have ed := hx.basedJBranch hd
  exact (Equal.subTm (.reflexive _) eS.symmetric).transitive
    ((hx.jSub hx.path.nil eD ed hσ).transitive
      (Equal.j (.reflexive _) (.reflexive _) eT (Equal.subTy (.reflexive D) eS)
        (hx.reindexBranchNil hx.path.nil eD ed hσ)))

end SquareKit.Internal.DependentJudgments.Contextual
