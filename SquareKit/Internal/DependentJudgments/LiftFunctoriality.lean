import SquareKit.Internal.DependentJudgments.DependentActionReindexing
import SquareKit.Internal.DependentJudgments.SourceCongruence

/-! Lift composition and split-section normalization follow from comprehension
beta/eta. These equations are source derivations over the unchanged model laws. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ Θ A B P σ τ x p : Expression V}

def Equal.extend {a a' : Expression V} {b b' : Expression V}
    (h0 : Equal (Ω := Ω) a a') (h1 : Equal (Ω := Ω) b b') :
    Equal (Ω := Ω) (Contextual.extend a b) (Contextual.extend a' b') := by
  have e := Equal.recipe (Ω := Ω) (Contextual.extend (.var 0) (.var 1) : Expression (Fin 2))
    ![a, b] ![a', b'] (Fin.cases h0 (Fin.cases h1 (fun i => nomatch i)))
  simpa [Contextual.sectionSub, Contextual.lift, liftSyntax, Contextual.transport, transportMotive, basedJ, endpoint, pathFamily, Contextual.concat,
    Contextual.eta, etaMotive, etaLeft, etaRight, etaBranch, transportGeneric, concatMap, concatGeneric] using e

def Equal.weaken {a a' : Expression V} {b b' : Expression V}
    (h0 : Equal (Ω := Ω) a a') (h1 : Equal (Ω := Ω) b b') :
    Equal (Ω := Ω) (Contextual.weaken a b) (Contextual.weaken a' b') := by
  have e := Equal.recipe (Ω := Ω) (Contextual.weaken (.var 0) (.var 1) : Expression (Fin 2))
    ![a, b] ![a', b'] (Fin.cases h0 (Fin.cases h1 (fun i => nomatch i)))
  simpa [Contextual.sectionSub, Contextual.lift, liftSyntax, Contextual.transport, transportMotive, basedJ, endpoint, pathFamily, Contextual.concat,
    Contextual.eta, etaMotive, etaLeft, etaRight, etaBranch, transportGeneric, concatMap, concatGeneric] using e

def Equal.generic {a a' : Expression V} {b b' : Expression V}
    (h0 : Equal (Ω := Ω) a a') (h1 : Equal (Ω := Ω) b b') :
    Equal (Ω := Ω) (Contextual.generic a b) (Contextual.generic a' b') := by
  have e := Equal.recipe (Ω := Ω) (Contextual.generic (.var 0) (.var 1) : Expression (Fin 2))
    ![a, b] ![a', b'] (Fin.cases h0 (Fin.cases h1 (fun i => nomatch i)))
  simpa [Contextual.sectionSub, Contextual.lift, liftSyntax, Contextual.transport, transportMotive, basedJ, endpoint, pathFamily, Contextual.concat,
    Contextual.eta, etaMotive, etaLeft, etaRight, etaBranch, transportGeneric, concatMap, concatGeneric] using e

def Equal.sectionSub {a a' : Expression V} {b b' : Expression V} {c c' : Expression V}
    (h0 : Equal (Ω := Ω) a a') (h1 : Equal (Ω := Ω) b b') (h2 : Equal (Ω := Ω) c c') :
    Equal (Ω := Ω) (Contextual.sectionSub a b c) (Contextual.sectionSub a' b' c') := by
  have e := Equal.recipe (Ω := Ω) (Contextual.sectionSub (.var 0) (.var 1) (.var 2) : Expression (Fin 3))
    ![a, b, c] ![a', b', c'] (Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (fun i => nomatch i))))
  simpa [Contextual.sectionSub, Contextual.lift, liftSyntax, Contextual.transport, transportMotive, basedJ, endpoint, pathFamily, Contextual.concat,
    Contextual.eta, etaMotive, etaLeft, etaRight, etaBranch, transportGeneric, concatMap, concatGeneric] using e

def Equal.lift {a a' : Expression V} {b b' : Expression V} {c c' : Expression V}
    (h0 : Equal (Ω := Ω) a a') (h1 : Equal (Ω := Ω) b b') (h2 : Equal (Ω := Ω) c c') :
    Equal (Ω := Ω) (Contextual.lift a b c) (Contextual.lift a' b' c') := by
  have e := Equal.recipe (Ω := Ω) (Contextual.lift (.var 0) (.var 1) (.var 2) : Expression (Fin 3))
    ![a, b, c] ![a', b', c'] (Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (fun i => nomatch i))))
  simpa [Contextual.sectionSub, Contextual.lift, liftSyntax, Contextual.transport, transportMotive, basedJ, endpoint, pathFamily, Contextual.concat,
    Contextual.eta, etaMotive, etaLeft, etaRight, etaBranch, transportGeneric, concatMap, concatGeneric] using e

def Equal.transport {a a' : Expression V} {b b' : Expression V} {c c' : Expression V} {d d' : Expression V} {e e' : Expression V} {f f' : Expression V} {g g' : Expression V}
    (h0 : Equal (Ω := Ω) a a') (h1 : Equal (Ω := Ω) b b') (h2 : Equal (Ω := Ω) c c') (h3 : Equal (Ω := Ω) d d') (h4 : Equal (Ω := Ω) e e') (h5 : Equal (Ω := Ω) f f') (h6 : Equal (Ω := Ω) g g') :
    Equal (Ω := Ω) (Contextual.transport a b c d e f g) (Contextual.transport a' b' c' d' e' f' g') := by
  have e := Equal.recipe (Ω := Ω) (Contextual.transport (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6) : Expression (Fin 7))
    ![a, b, c, d, e, f, g] ![a', b', c', d', e', f', g'] (Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (Fin.cases h4 (Fin.cases h5 (Fin.cases h6 (fun i => nomatch i))))))))
  simpa [Contextual.sectionSub, Contextual.lift, liftSyntax, Contextual.transport, transportMotive, basedJ, endpoint, pathFamily, Contextual.concat,
    Contextual.eta, etaMotive, etaLeft, etaRight, etaBranch, transportGeneric, concatMap, concatGeneric] using e

def Equal.concat {a a' : Expression V} {b b' : Expression V} {c c' : Expression V} {d d' : Expression V} {e e' : Expression V} {f f' : Expression V} {g g' : Expression V}
    (h0 : Equal (Ω := Ω) a a') (h1 : Equal (Ω := Ω) b b') (h2 : Equal (Ω := Ω) c c') (h3 : Equal (Ω := Ω) d d') (h4 : Equal (Ω := Ω) e e') (h5 : Equal (Ω := Ω) f f') (h6 : Equal (Ω := Ω) g g') :
    Equal (Ω := Ω) (Contextual.concat a b c d e f g) (Contextual.concat a' b' c' d' e' f' g') := by
  have e := Equal.recipe (Ω := Ω) (Contextual.concat (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6) : Expression (Fin 7))
    ![a, b, c, d, e, f, g] ![a', b', c', d', e', f', g'] (Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (Fin.cases h4 (Fin.cases h5 (Fin.cases h6 (fun i => nomatch i))))))))
  simpa [Contextual.sectionSub, Contextual.lift, liftSyntax, Contextual.transport, transportMotive, basedJ, endpoint, pathFamily, Contextual.concat,
    Contextual.eta, etaMotive, etaLeft, etaRight, etaBranch, transportGeneric, concatMap, concatGeneric] using e

def Equal.eta {a a' : Expression V} {b b' : Expression V} {c c' : Expression V} {d d' : Expression V} {e e' : Expression V} {f f' : Expression V} {g g' : Expression V} {h h' : Expression V} {i i' : Expression V}
    (h0 : Equal (Ω := Ω) a a') (h1 : Equal (Ω := Ω) b b') (h2 : Equal (Ω := Ω) c c') (h3 : Equal (Ω := Ω) d d') (h4 : Equal (Ω := Ω) e e') (h5 : Equal (Ω := Ω) f f') (h6 : Equal (Ω := Ω) g g') (h7 : Equal (Ω := Ω) h h') (h8 : Equal (Ω := Ω) i i') :
    Equal (Ω := Ω) (Contextual.eta a b c d e f g h i) (Contextual.eta a' b' c' d' e' f' g' h' i') := by
  have e := Equal.recipe (Ω := Ω) (Contextual.eta (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6) (.var 7) (.var 8) : Expression (Fin 9))
    ![a, b, c, d, e, f, g, h, i] ![a', b', c', d', e', f', g', h', i'] (Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (Fin.cases h4 (Fin.cases h5 (Fin.cases h6 (Fin.cases h7 (Fin.cases h8 (fun i => nomatch i))))))))))
  simpa [Contextual.sectionSub, Contextual.lift, liftSyntax, Contextual.transport, transportMotive, basedJ, endpoint, pathFamily, Contextual.concat,
    Contextual.eta, etaMotive, etaLeft, etaRight, etaBranch, transportGeneric, concatMap, concatGeneric] using e

def Ty.pairExt (hA : Ty (Ω := Ω) Γ A) (hσ : Sub (Ω := Ω) Δ (Contextual.extend Γ A) σ)
    (hτ : Sub (Ω := Ω) Δ (Contextual.extend Γ A) τ)
    (hp : Equal (Ω := Ω) (Contextual.comp (Contextual.weaken Γ A) σ) (Contextual.comp (Contextual.weaken Γ A) τ))
    (ht : Equal (Ω := Ω) (Contextual.subTm (Contextual.generic Γ A) σ) (Contextual.subTm (Contextual.generic Γ A) τ)) : Equal (Ω := Ω) σ τ :=
  ((hA.pairEta hσ).symmetric.transitive (Equal.pair (.reflexive A) hp ht)).transitive (hA.pairEta hτ)

def Sub.liftComp (hσ : Sub (Ω := Ω) Δ Γ σ) (hτ : Sub (Ω := Ω) Θ Δ τ) (hA : Ty (Ω := Ω) Γ A) :
    Equal (Ω := Ω) (Contextual.comp (Contextual.lift Δ A σ) (Contextual.lift Θ (Contextual.subTy A σ) τ)) (Contextual.lift Θ A (Contextual.comp σ τ)) := by
  have hστ := hσ.comp hτ
  have hF := hσ.lift hA
  have hG := hτ.lift (hA.substitute hσ)
  have eA := hA.subComp hσ hτ
  have left := hF.comp hG
  have right := (hστ.lift hA).resource (Equal.extend (.reflexive Θ) eA.symmetric)
  apply hA.pairExt left right
  · exact ((((((hA.weaken.assoc hF hG).symmetric.transitive
      (Equal.comp (hσ.liftWeaken hA) (.reflexive _))).transitive
        (hσ.assoc (hA.substitute hσ).weaken hG)).transitive
          (Equal.comp (.reflexive σ) (hτ.liftWeaken (hA.substitute hσ)))).transitive
            (hσ.assoc hτ ((hA.substitute hσ).substitute hτ).weaken).symmetric).transitive
              (Equal.comp (.reflexive _) (Equal.weaken (.reflexive Θ) eA))).transitive
                (hστ.liftWeaken hA).symmetric
  · exact ((((hA.generic.subComp hF hG).symmetric.transitive
      (Equal.subTm (hσ.liftGeneric hA) (.reflexive _))).transitive
        (hτ.liftGeneric (hA.substitute hσ))).transitive
          (Equal.generic (.reflexive Θ) eA)).transitive (hστ.liftGeneric hA).symmetric

def Ty.liftId (hA : Ty (Ω := Ω) Γ A) : Equal (Ω := Ω) (Contextual.lift Γ A (Contextual.identitySub Γ)) (Contextual.identitySub (Contextual.extend Γ A)) := by
  have hI := hA.context.identity
  have left := hI.lift hA
  have right := hA.extend.identity.resource (Equal.extend (.reflexive Γ) hA.subId.symmetric)
  apply hA.pairExt left right
  · exact (((hI.liftWeaken hA).transitive (hA.substitute hI).weaken.idLeft).transitive
      (Equal.weaken (.reflexive Γ) hA.subId)).transitive hA.weaken.idRight.symmetric
  · exact ((hI.liftGeneric hA).transitive (Equal.generic (.reflexive Γ) hA.subId)).transitive hA.generic.subId.symmetric

def Tm.liftWeakenSection (hp : Tm (Ω := Ω) Γ P p) (hA : Ty (Ω := Ω) Γ A) :
    Equal (Ω := Ω)
      (Contextual.comp (Contextual.lift (Contextual.extend Γ P) A (Contextual.weaken Γ P)) (Contextual.lift Γ (Contextual.subTy A (Contextual.weaken Γ P)) (Contextual.sectionSub Γ P p)))
      (Contextual.identitySub (Contextual.extend Γ A)) :=
  ((hp.family.weaken.liftComp hp.section hA).transitive
    (Equal.lift (.reflexive Γ) (.reflexive A) hp.sectionWeaken)).transitive hA.liftId

def Ty.displayWeakenSection (hB : Ty (Ω := Ω) (Contextual.extend Γ A) B) (hA : Ty (Ω := Ω) Γ A)
    (hp : Tm (Ω := Ω) Γ P p) :
    Equal (Ω := Ω)
      (Contextual.subTy (Contextual.subTy B (Contextual.lift (Contextual.extend Γ P) A (Contextual.weaken Γ P))) (Contextual.lift Γ (Contextual.subTy A (Contextual.weaken Γ P)) (Contextual.sectionSub Γ P p))) B :=
  ((hB.subComp (hp.family.weaken.lift hA) (hp.section.lift (hA.substitute hp.family.weaken))).transitive
    (Equal.subTy (.reflexive B) (hp.liftWeakenSection hA))).transitive hB.subId

end
end SquareKit.Internal.DependentJudgments.Contextual
