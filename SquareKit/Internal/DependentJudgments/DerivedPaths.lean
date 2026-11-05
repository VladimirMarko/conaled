import SquareKit.Internal.DependentJudgments.Authoring

/-! Source recipes built from contextual J and comprehension. All conversions
below are derivations in the generated theory, rather than equations assumed
of a model or of the recipe being constructed. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ Θ A B C σ τ x y z p q t u D d : Expression V}

def Equal.subTy {a a' : Expression V} {b b' : Expression V} (h0 : Equal (Ω := Ω) a a') (h1 : Equal (Ω := Ω) b b') :
    Equal (Ω := Ω) (Contextual.subTy a b) (Contextual.subTy a' b') :=
  Derivation.congruence (T := theory) (Sum.inl DependentJudgments.Operation.subTy) (Fin.cases h0 (Fin.cases h1 (fun i => nomatch i)))

def Equal.subTm {a a' : Expression V} {b b' : Expression V} (h0 : Equal (Ω := Ω) a a') (h1 : Equal (Ω := Ω) b b') :
    Equal (Ω := Ω) (Contextual.subTm a b) (Contextual.subTm a' b') :=
  Derivation.congruence (T := theory) (Sum.inl DependentJudgments.Operation.subTm) (Fin.cases h0 (Fin.cases h1 (fun i => nomatch i)))

def Equal.comp {a a' : Expression V} {b b' : Expression V} (h0 : Equal (Ω := Ω) a a') (h1 : Equal (Ω := Ω) b b') :
    Equal (Ω := Ω) (Contextual.comp a b) (Contextual.comp a' b') :=
  Derivation.congruence (T := theory) (Sum.inl DependentJudgments.Operation.comp) (Fin.cases h0 (Fin.cases h1 (fun i => nomatch i)))

def Equal.total {a a' : Expression V} (h0 : Equal (Ω := Ω) a a') :
    Equal (Ω := Ω) (Contextual.total a) (Contextual.total a') :=
  Derivation.congruence (T := theory) (Sum.inr Operation.total) (Fin.cases h0 (fun i => nomatch i))

def Equal.identity {a a' : Expression V} {b b' : Expression V} {c c' : Expression V} (h0 : Equal (Ω := Ω) a a') (h1 : Equal (Ω := Ω) b b') (h2 : Equal (Ω := Ω) c c') :
    Equal (Ω := Ω) (Contextual.identity a b c) (Contextual.identity a' b' c') :=
  Derivation.congruence (T := theory) (Sum.inr Operation.identity) (Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (fun i => nomatch i))))

def Ty.recontext (hA : Ty (Ω := Ω) Γ A) (e : Equal (Ω := Ω) Γ Δ) : Ty (Ω := Ω) Δ A :=
  Derivation.conversion (T := theory) (Sum.inl DependentJudgments.Predicate.family)
    (Fin.cases e (Fin.cases (.reflexive A) (fun i => nomatch i))) hA

def Tm.recontext (ht : Tm (Ω := Ω) Γ A t) (e : Equal (Ω := Ω) Γ Δ) : Tm (Ω := Ω) Δ A t :=
  Derivation.conversion (T := theory) (Sum.inl DependentJudgments.Predicate.term)
    (Fin.cases e (Fin.cases (.reflexive A) (Fin.cases (.reflexive t) (fun i => nomatch i)))) ht

def Tm.changeTerm (ht : Tm (Ω := Ω) Γ A t) (e : Equal (Ω := Ω) t u) : Tm (Ω := Ω) Γ A u :=
  Derivation.conversion (T := theory) (Sum.inl DependentJudgments.Predicate.term)
    (Fin.cases (.reflexive Γ) (Fin.cases (.reflexive A) (Fin.cases e (fun i => nomatch i)))) ht

def Sub.retarget (hσ : Sub (Ω := Ω) Δ Γ σ) (e : Equal (Ω := Ω) Γ Θ) : Sub (Ω := Ω) Δ Θ σ :=
  Derivation.conversion (T := theory) (Sum.inl DependentJudgments.Predicate.substitution)
    (Fin.cases (.reflexive Δ) (Fin.cases e (Fin.cases (.reflexive σ) (fun i => nomatch i)))) hσ

def Sub.resource (hσ : Sub (Ω := Ω) Δ Γ σ) (e : Equal (Ω := Ω) Δ Θ) : Sub (Ω := Ω) Θ Γ σ :=
  Derivation.conversion (T := theory) (Sum.inl DependentJudgments.Predicate.substitution)
    (Fin.cases e (Fin.cases (.reflexive Γ) (Fin.cases (.reflexive σ) (fun i => nomatch i)))) hσ

def Tm.section (hx : Tm (Ω := Ω) Γ A x) : Sub (Ω := Ω) Γ (Contextual.extend Γ A) (Contextual.sectionSub Γ A x) :=
  Sub.pair hx.family hx.family.context.identity (hx.convert hx.family.subId.symmetric)

def Tm.pathFamily (hx : Tm (Ω := Ω) Γ A x) : Ty (Ω := Ω) (Contextual.extend Γ A) (Contextual.pathFamily Γ A x) :=
  (hx.substitute hx.family.weaken).identity hx.family.generic

def Tm.pathProjection (hx : Tm (Ω := Ω) Γ A x) :
    Sub (Ω := Ω) (Contextual.path A x) (Contextual.extend Γ A) (Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x)) :=
  hx.pathFamily.weaken.resource hx.pathDef.symmetric

def Tm.sectionWeaken (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (Contextual.comp (Contextual.weaken Γ A) (Contextual.sectionSub Γ A x)) (Contextual.identitySub Γ) :=
  hx.family.weakenPair hx.family.context.identity (hx.convert hx.family.subId.symmetric)

def Tm.sectionGeneric (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (Contextual.subTm (Contextual.generic Γ A) (Contextual.sectionSub Γ A x)) x :=
  hx.family.variablePair hx.family.context.identity (hx.convert hx.family.subId.symmetric)

def Ty.weakenSection (hB : Ty (Ω := Ω) Γ B) (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (Contextual.subTy (Contextual.subTy B (Contextual.weaken Γ A)) (Contextual.sectionSub Γ A x)) B :=
  ((hB.subComp hx.family.weaken hx.section).transitive
    (Equal.subTy (.reflexive B) hx.sectionWeaken)).transitive hB.subId

def Tm.weakenSection (ht : Tm (Ω := Ω) Γ B t) (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (Contextual.subTm (Contextual.subTm t (Contextual.weaken Γ A)) (Contextual.sectionSub Γ A x)) t :=
  ((ht.subComp hx.family.weaken hx.section).transitive
    (Equal.subTm (.reflexive t) hx.sectionWeaken)).transitive ht.subId

def Tm.pathFamilySection (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y) :
    Equal (Ω := Ω) (Contextual.subTy (Contextual.pathFamily Γ A x) (Contextual.sectionSub Γ A y)) (Contextual.identity A x y) :=
  ((hx.substitute hx.family.weaken).identitySub hx.family.generic hy.section).transitive
    (Equal.identity (hx.family.weakenSection hy) (hx.weakenSection hy) hy.sectionGeneric)

abbrev endpoint (Γ A x y p : Expression V) : Expression V :=
  Contextual.pair (Contextual.pathFamily Γ A x) (Contextual.sectionSub Γ A y) p

def Tm.endpoint (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) : Sub (Ω := Ω) Γ (Contextual.path A x) (Contextual.endpoint Γ A x y p) :=
  (Sub.pair hx.pathFamily hy.section (hp.convert (hx.pathFamilySection hy).symmetric)).retarget hx.pathDef.symmetric

def Tm.endpointProjection (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) :
    Equal (Ω := Ω) (Contextual.comp (Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x)) (Contextual.endpoint Γ A x y p))
      (Contextual.sectionSub Γ A y) :=
  hx.pathFamily.weakenPair hy.section (hp.convert (hx.pathFamilySection hy).symmetric)

abbrev basedJ (A x D d : Expression V) : Expression V := Contextual.j A x (Contextual.telNil (Contextual.path A x)) D d

def Tm.basedJBranch (hx : Tm (Ω := Ω) Γ A x) (hd : Tm (Ω := Ω) Γ (Contextual.subTy D (Contextual.root A x)) d) :
    Tm (Ω := Ω) (Contextual.total (Contextual.pullback (Contextual.telNil (Contextual.path A x)) (Contextual.root A x)))
      (Contextual.subTy D (Contextual.rootTail A x (Contextual.telNil (Contextual.path A x)))) d :=
  (hd.convert (Equal.subTy (.reflexive D) hx.rootTailNil.symmetric)).recontext
    ((Equal.total hx.root.pullbackNil).transitive hx.family.context.totalNil).symmetric

def Tm.basedJ (hx : Tm (Ω := Ω) Γ A x) (hD : Ty (Ω := Ω) (Contextual.path A x) D)
    (hd : Tm (Ω := Ω) Γ (Contextual.subTy D (Contextual.root A x)) d) : Tm (Ω := Ω) (Contextual.path A x) D (Contextual.basedJ A x D d) :=
  (hx.j hx.path.nil (hD.recontext hx.path.totalNil.symmetric) (hx.basedJBranch hd)).recontext hx.path.totalNil

def Tm.basedJBeta (hx : Tm (Ω := Ω) Γ A x) (hD : Ty (Ω := Ω) (Contextual.path A x) D)
    (hd : Tm (Ω := Ω) Γ (Contextual.subTy D (Contextual.root A x)) d) :
    Equal (Ω := Ω) (Contextual.subTm (Contextual.basedJ A x D d) (Contextual.root A x)) d :=
  (Equal.subTm (.reflexive _) hx.rootTailNil.symmetric).transitive
    (hx.jBeta hx.path.nil (hD.recontext hx.path.totalNil.symmetric) (hx.basedJBranch hd))

abbrev transportMotive (Γ A B x : Expression V) : Expression V :=
  Contextual.subTy B (Contextual.weaken (Contextual.extend Γ A) (Contextual.pathFamily Γ A x))
abbrev transport (Γ A B x y p u : Expression V) : Expression V :=
  Contextual.subTm (Contextual.basedJ A x (Contextual.transportMotive Γ A B x) u) (Contextual.endpoint Γ A x y p)

def Ty.transportRoot (hB : Ty (Ω := Ω) (Contextual.extend Γ A) B) (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω) (Contextual.subTy (Contextual.transportMotive Γ A B x) (Contextual.root A x)) (Contextual.subTy B (Contextual.sectionSub Γ A x)) :=
  (hB.subComp hx.pathProjection hx.root).transitive (Equal.subTy (.reflexive B) hx.rootProjection)

def Ty.transportEndpoint (hB : Ty (Ω := Ω) (Contextual.extend Γ A) B) (hx : Tm (Ω := Ω) Γ A x)
    (hy : Tm (Ω := Ω) Γ A y) (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) :
    Equal (Ω := Ω) (Contextual.subTy (Contextual.transportMotive Γ A B x) (Contextual.endpoint Γ A x y p)) (Contextual.subTy B (Contextual.sectionSub Γ A y)) :=
  (hB.subComp hx.pathProjection (hx.endpoint hy hp)).transitive (Equal.subTy (.reflexive B) (hx.endpointProjection hy hp))

def Tm.transport (hB : Ty (Ω := Ω) (Contextual.extend Γ A) B) (hx : Tm (Ω := Ω) Γ A x)
    (hy : Tm (Ω := Ω) Γ A y) (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p)
    (hu : Tm (Ω := Ω) Γ (Contextual.subTy B (Contextual.sectionSub Γ A x)) u) :
    Tm (Ω := Ω) Γ (Contextual.subTy B (Contextual.sectionSub Γ A y)) (Contextual.transport Γ A B x y p u) :=
  ((hx.basedJ (hB.substitute hx.pathProjection) (hu.convert (hB.transportRoot hx).symmetric)).substitute
    (hx.endpoint hy hp)).convert (hB.transportEndpoint hx hy hp)

def Tm.transportRefl (hB : Ty (Ω := Ω) (Contextual.extend Γ A) B) (hx : Tm (Ω := Ω) Γ A x)
    (hu : Tm (Ω := Ω) Γ (Contextual.subTy B (Contextual.sectionSub Γ A x)) u) :
    Equal (Ω := Ω) (Contextual.transport Γ A B x x (Contextual.reflexivity A x) u) u :=
  (Equal.subTm (.reflexive _) hx.rootDef.symmetric).transitive
    (hx.basedJBeta (hB.substitute hx.pathProjection) (hu.convert (hB.transportRoot hx).symmetric))

abbrev concat (Γ A x y z p q : Expression V) : Expression V :=
  transport Γ A (Contextual.pathFamily Γ A x) y z q p

def Tm.concat (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hz : Tm (Ω := Ω) Γ A z) (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p)
    (hq : Tm (Ω := Ω) Γ (Contextual.identity A y z) q) :
    Tm (Ω := Ω) Γ (Contextual.identity A x z) (Contextual.concat Γ A x y z p q) :=
  (Tm.transport hx.pathFamily hy hz hq (hp.convert (hx.pathFamilySection hy).symmetric)).convert (hx.pathFamilySection hz)

def Tm.concatReflRight (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p) :
    Equal (Ω := Ω) (Contextual.concat Γ A x y y p (Contextual.reflexivity A y)) p :=
  Tm.transportRefl hx.pathFamily hy (hp.convert (hx.pathFamilySection hy).symmetric)

end SquareKit.Internal.DependentJudgments.Contextual
