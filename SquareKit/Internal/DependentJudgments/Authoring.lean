import SquareKit.Internal.DependentJudgments.SourceSubstitution

/-! Authoring uses source judgments only. The constructors discharge rule
instantiation and conversions; they never ask for a family indexed by models. -/
namespace SquareKit.Internal.DependentJudgments.Contextual
set_option backward.isDefEq.respectTransparency false
open GuardedTheory
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ Θ A B σ τ t x y T D d : Expression V}

private def extra (a : Axiom) (σ : Fin (rule a).parameterCount → Expression V)
    (h : ∀ i, Derivation theory Ω (((rule a).premise i).subst σ)) :
    Derivation theory Ω ((rule a).conclusion.subst σ) :=
  Derivation.rule (T := theory) (Sum.inr a) σ h

private def structural (a : ComprehensionAxiom)
    (σ : Fin (comprehensionTheory.rule a).parameterCount → Expression V)
    (h : ∀ i, Derivation theory Ω ((((comprehensionTheory.rule a).premise i).inl extraSignature).subst σ)) :
    Derivation theory Ω (((comprehensionTheory.rule a).conclusion.inl extraSignature).subst σ) :=
  Derivation.rule (T := theory) (Sum.inl a) σ h

def Ctx.empty : Ctx (Ω := Ω) empty := by
  have e := structural (Ω := Ω) .empty (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  simpa [comprehensionTheory] using e

def Ty.extend (hA : Ty (Ω := Ω) Γ A) : Ctx (Ω := Ω) (Contextual.extend Γ A) := by
  have e := structural (Ω := Ω) .extension ![Γ, A] (Fin.cases (by simpa [rule, comprehensionTheory] using hA) (fun i => nomatch i))
  simpa [rule, comprehensionTheory] using e

def Ctx.identity (hΓ : Ctx (Ω := Ω) Γ) : Sub (Ω := Ω) Γ Γ (identitySub Γ) := by
  have e := structural (Ω := Ω) .identity ![Γ] (Fin.cases (by simpa [rule, comprehensionTheory] using hΓ) (fun i => nomatch i))
  simpa [rule, comprehensionTheory] using e

def Ty.weaken (hA : Ty (Ω := Ω) Γ A) : Sub (Ω := Ω) (Contextual.extend Γ A) Γ (Contextual.weaken Γ A) := by
  have e := structural (Ω := Ω) .weakening ![Γ, A] (Fin.cases (by simpa [rule, comprehensionTheory] using hA) (fun i => nomatch i))
  simpa [rule, comprehensionTheory] using e

def Ty.generic (hA : Ty (Ω := Ω) Γ A) : Tm (Ω := Ω) (Contextual.extend Γ A) (subTy A (Contextual.weaken Γ A)) (Contextual.generic Γ A) := by
  have e := structural (Ω := Ω) .generic ![Γ, A] (Fin.cases (by simpa [rule, comprehensionTheory] using hA) (fun i => nomatch i))
  simpa [rule, comprehensionTheory] using e

def Ty.substitute (hA : Ty (Ω := Ω) Γ A) (hσ : Sub (Ω := Ω) Δ Γ σ) : Ty (Ω := Ω) Δ (subTy A σ) := by
  have e := extra (Ω := Ω) .subTy ![Γ, Δ, A, σ] (Fin.cases (by simpa [rule, comprehensionTheory] using hA) (Fin.cases (by simpa [rule, comprehensionTheory] using hσ) (fun i => nomatch i)))
  simpa [rule, comprehensionTheory] using e

def Tm.substitute (ht : Tm (Ω := Ω) Γ A t) (hσ : Sub (Ω := Ω) Δ Γ σ) : Tm (Ω := Ω) Δ (subTy A σ) (subTm t σ) := by
  have e := extra (Ω := Ω) .subTm ![Γ, Δ, A, t, σ] (Fin.cases (by simpa [rule, comprehensionTheory] using ht) (Fin.cases (by simpa [rule, comprehensionTheory] using hσ) (fun i => nomatch i)))
  simpa [rule, comprehensionTheory] using e

def Tm.family (ht : Tm (Ω := Ω) Γ A t) : Ty (Ω := Ω) Γ A := by
  have e := extra (Ω := Ω) .termFamily ![Γ, A, t] (Fin.cases (by simpa [rule, comprehensionTheory] using ht) (fun i => nomatch i))
  simpa [rule, comprehensionTheory] using e

def Ty.context (hA : Ty (Ω := Ω) Γ A) : Ctx (Ω := Ω) Γ := by
  have e := extra (Ω := Ω) .familyContext ![Γ, A] (Fin.cases (by simpa [rule, comprehensionTheory] using hA) (fun i => nomatch i))
  simpa [rule, comprehensionTheory] using e

def Sub.comp (hσ : Sub (Ω := Ω) Δ Γ σ) (hτ : Sub (Ω := Ω) Θ Δ τ) : Sub (Ω := Ω) Θ Γ (Contextual.comp σ τ) := by
  have e := extra (Ω := Ω) .comp ![Γ, Δ, Θ, σ, τ] (Fin.cases (by simpa [rule, comprehensionTheory] using hσ) (Fin.cases (by simpa [rule, comprehensionTheory] using hτ) (fun i => nomatch i)))
  simpa [rule, comprehensionTheory] using e

def Sub.pair (hA : Ty (Ω := Ω) Γ A) (hσ : Sub (Ω := Ω) Δ Γ σ) (ht : Tm (Ω := Ω) Δ (subTy A σ) t) :
    Sub (Ω := Ω) Δ (Contextual.extend Γ A) (Contextual.pair A σ t) := by
  have e := structural (Ω := Ω) .pairing ![Γ, Δ, A, σ, t]
    (Fin.cases (by simpa [rule, comprehensionTheory] using hA) (Fin.cases (by simpa [rule, comprehensionTheory] using hσ) (Fin.cases (by simpa [rule, comprehensionTheory] using ht) (fun i => nomatch i))))
  simpa [rule, comprehensionTheory] using e

/-- Conversion changes a source type along a derived judgmental equation.
Object identity is not accepted as such an equation. -/
def Tm.convert (ht : Tm (Ω := Ω) Γ A t) (e : Equal (Ω := Ω) A B) : Tm (Ω := Ω) Γ B t :=
  Derivation.conversion (T := theory) (Sum.inl Predicate.term)
    (Fin.cases (.reflexive Γ) (Fin.cases e (Fin.cases (.reflexive t) (fun i => nomatch i)))) ht

def Tm.identity (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y) : Ty (Ω := Ω) Γ (Contextual.identity A x y) := by
  have e := extra (Ω := Ω) .identity ![Γ, A, x, y] (Fin.cases (by simpa [rule, comprehensionTheory] using hx) (Fin.cases (by simpa [rule, comprehensionTheory] using hy) (fun i => nomatch i)))
  simpa [rule, comprehensionTheory] using e

def Tm.reflexivity (hx : Tm (Ω := Ω) Γ A x) : Tm (Ω := Ω) Γ (Contextual.identity A x x) (Contextual.reflexivity A x) := by
  have e := extra (Ω := Ω) .reflexivity ![Γ, A, x] (Fin.cases (by simpa [rule, comprehensionTheory] using hx) (fun i => nomatch i))
  simpa [rule, comprehensionTheory] using e

def Tm.path (hx : Tm (Ω := Ω) Γ A x) : Ctx (Ω := Ω) (Contextual.path A x) := by
  have e := extra (Ω := Ω) .path ![Γ, A, x] (Fin.cases (by simpa [rule, comprehensionTheory] using hx) (fun i => nomatch i))
  simpa [rule, comprehensionTheory] using e

def Tm.root (hx : Tm (Ω := Ω) Γ A x) : Sub (Ω := Ω) Γ (Contextual.path A x) (Contextual.root A x) := by
  have e := extra (Ω := Ω) .root ![Γ, A, x] (Fin.cases (by simpa [rule, comprehensionTheory] using hx) (fun i => nomatch i))
  simpa [rule, comprehensionTheory] using e

def Ctx.nil (hΓ : Ctx (Ω := Ω) Γ) : Tel (Ω := Ω) 0 Γ (telNil Γ) := by
  have e := extra (Ω := Ω) .telNil ![Γ] (Fin.cases (by simpa [rule, comprehensionTheory] using hΓ) (fun i => nomatch i))
  simpa [rule, comprehensionTheory] using e

def Ty.cons (hA : Ty (Ω := Ω) Γ A) (hT : Tel (Ω := Ω) n (Contextual.extend Γ A) T) : Tel (Ω := Ω) (n + 1) Γ (telCons A T) := by
  have e := extra (Ω := Ω) (.telCons n) ![Γ, A, T] (Fin.cases (by simpa [rule, comprehensionTheory] using hA) (Fin.cases (by simpa [rule, comprehensionTheory] using hT) (fun i => nomatch i)))
  simpa [rule, comprehensionTheory] using e

def Tel.total (hT : Tel (Ω := Ω) n Γ T) : Ctx (Ω := Ω) (Contextual.total T) := by
  have e := extra (Ω := Ω) (.total n) ![Γ, T] (Fin.cases (by simpa [rule, comprehensionTheory] using hT) (fun i => nomatch i))
  simpa [rule, comprehensionTheory] using e

def Tel.pullback (hT : Tel (Ω := Ω) n Γ T) (hσ : Sub (Ω := Ω) Δ Γ σ) : Tel (Ω := Ω) n Δ (Contextual.pullback T σ) := by
  have e := extra (Ω := Ω) (.pullback n) ![Γ, Δ, T, σ] (Fin.cases (by simpa [rule, comprehensionTheory] using hT) (Fin.cases (by simpa [rule, comprehensionTheory] using hσ) (fun i => nomatch i)))
  simpa [rule, comprehensionTheory] using e

def Tm.j (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (Contextual.path A x) T)
    (hD : Ty (Ω := Ω) (Contextual.total T) D) (hd : Tm (Ω := Ω) (total (Contextual.pullback T (Contextual.root A x))) (subTy D (rootTail A x T)) d) :
    Tm (Ω := Ω) (Contextual.total T) D (Contextual.j A x T D d) := by
  have e := extra (Ω := Ω) (.j n) ![Γ, A, x, T, D, d]
    (Fin.cases (by simpa [rule, comprehensionTheory] using hx) (Fin.cases (by simpa [rule, comprehensionTheory] using hT) (Fin.cases (by simpa [rule, comprehensionTheory] using hD) (Fin.cases (by simpa [rule, comprehensionTheory] using hd) (fun i => nomatch i)))))
  simpa [rule, comprehensionTheory] using e

def Tm.jBeta (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (Contextual.path A x) T)
    (hD : Ty (Ω := Ω) (Contextual.total T) D) (hd : Tm (Ω := Ω) (total (Contextual.pullback T (Contextual.root A x))) (subTy D (rootTail A x T)) d) :
    Equal (Ω := Ω) (subTm (Contextual.j A x T D d) (rootTail A x T)) d := by
  have e := extra (Ω := Ω) (.jBeta n) ![Γ, A, x, T, D, d]
    (Fin.cases (by simpa [rule, comprehensionTheory] using hx) (Fin.cases (by simpa [rule, comprehensionTheory] using hT) (Fin.cases (by simpa [rule, comprehensionTheory] using hD) (Fin.cases (by simpa [rule, comprehensionTheory] using hd) (fun i => nomatch i)))))
  simpa [rule, comprehensionTheory] using e

def Tm.jSub (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (Contextual.path A x) T)
    (hD : Ty (Ω := Ω) (Contextual.total T) D) (hd : Tm (Ω := Ω) (total (Contextual.pullback T (Contextual.root A x))) (subTy D (rootTail A x T)) d)
    (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (Contextual.j A x T D d) (pathTailMap A x T σ))
      (Contextual.j (subTy A σ) (subTm x σ) (Contextual.pathTail A x T σ) (subTy D (pathTailMap A x T σ))
        (reindexBranch A x T σ D d)) := by
  have e := extra (Ω := Ω) (.jSub n) ![Γ, A, x, T, D, d, Δ, σ]
    (Fin.cases (by simpa [rule, comprehensionTheory] using hx) (Fin.cases (by simpa [rule, comprehensionTheory] using hT) (Fin.cases (by simpa [rule, comprehensionTheory] using hD) (Fin.cases (by simpa [rule, comprehensionTheory] using hd) (Fin.cases (by simpa [rule, comprehensionTheory] using hσ) (fun i => nomatch i))))))
  simpa [rule, comprehensionTheory] using e


def Tm.pathTail (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (Contextual.path A x) T)
    (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Tel (Ω := Ω) n (Contextual.path (subTy A σ) (subTm x σ)) (Contextual.pathTail A x T σ) := by
  have e := extra (Ω := Ω) (.pathTail n) ![Γ, A, x, T, Δ, σ]
    (Fin.cases (by simpa [rule, comprehensionTheory] using hx) (Fin.cases (by simpa [rule, comprehensionTheory] using hT) (Fin.cases (by simpa [rule, comprehensionTheory] using hσ) (fun i => nomatch i))))
  simpa [rule, comprehensionTheory] using e

def Tm.pathTailMap (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (Contextual.path A x) T)
    (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Sub (Ω := Ω) (Contextual.total (Contextual.pathTail A x T σ)) (Contextual.total T) (pathTailMap A x T σ) := by
  have e := extra (Ω := Ω) (.pathTailMap n) ![Γ, A, x, T, Δ, σ]
    (Fin.cases (by simpa [rule, comprehensionTheory] using hx) (Fin.cases (by simpa [rule, comprehensionTheory] using hT) (Fin.cases (by simpa [rule, comprehensionTheory] using hσ) (fun i => nomatch i))))
  simpa [rule, comprehensionTheory] using e

def Tm.reindexBranch (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (Contextual.path A x) T)
    (hD : Ty (Ω := Ω) (Contextual.total T) D)
    (hd : Tm (Ω := Ω) (Contextual.total (Contextual.pullback T (Contextual.root A x)))
      (subTy D (rootTail A x T)) d) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Tm (Ω := Ω)
      (Contextual.total (Contextual.pullback (Contextual.pathTail A x T σ)
        (Contextual.root (subTy A σ) (subTm x σ))))
      (subTy (subTy D (Contextual.pathTailMap A x T σ))
        (rootTail (subTy A σ) (subTm x σ) (Contextual.pathTail A x T σ)))
      (Contextual.reindexBranch A x T σ D d) := by
  have e := extra (Ω := Ω) (.reindexBranch n) ![Γ, A, x, T, D, d, Δ, σ]
    (Fin.cases (by simpa [rule] using hx)
      (Fin.cases (by simpa [rule] using hT)
        (Fin.cases (by simpa [rule] using hD)
          (Fin.cases (by simpa [rule] using hd)
            (Fin.cases (by simpa [rule] using hσ) (fun i => nomatch i))))))
  simpa [rule] using e

end SquareKit.Internal.DependentJudgments.Contextual
