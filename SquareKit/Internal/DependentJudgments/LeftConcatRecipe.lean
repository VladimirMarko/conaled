import SquareKit.Internal.DependentJudgments.LeftConcatenation

/-! Schematic instantiation of the left-path recipe and its generated
congruence. These are syntax operations, distinct from object substitution. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
namespace LeftConcatRecipe
variable {V W : Type}
theorem subTm_subst (σ : V → Expression W) (a b : Expression V) :
    (subTm a b).subst σ = subTm (a.subst σ) (b.subst σ) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inl .subTm))
  funext i
  fin_cases i <;> rfl

theorem subTy_subst (σ : V → Expression W) (a b : Expression V) :
    (subTy a b).subst σ = subTy (a.subst σ) (b.subst σ) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inl .subTy))
  funext i
  fin_cases i <;> rfl

theorem path_subst (σ : V → Expression W) (a b : Expression V) :
    (path a b).subst σ = path (a.subst σ) (b.subst σ) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inr .path))
  funext i
  fin_cases i <;> rfl

theorem root_subst (σ : V → Expression W) (a b : Expression V) :
    (root a b).subst σ = root (a.subst σ) (b.subst σ) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inr .root))
  funext i
  fin_cases i <;> rfl

theorem telCons_subst (σ : V → Expression W) (a b : Expression V) :
    (telCons a b).subst σ = telCons (a.subst σ) (b.subst σ) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inr .telCons))
  funext i
  fin_cases i <;> rfl

theorem telNil_subst (σ : V → Expression W) (a : Expression V) :
    (telNil a).subst σ = telNil (a.subst σ) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inr .telNil))
  funext i
  fin_cases i
  rfl

theorem pair_subst (σ : V → Expression W) (a b c : Expression V) :
    (Contextual.pair a b c).subst σ = Contextual.pair (a.subst σ) (b.subst σ) (c.subst σ) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inl .pair))
  funext i
  fin_cases i <;> rfl

theorem comp_subst (σ : V → Expression W) (a b : Expression V) :
    (comp a b).subst σ = comp (a.subst σ) (b.subst σ) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inl .comp))
  funext i
  fin_cases i <;> rfl

theorem extend_subst (σ : V → Expression W) (a b : Expression V) :
    (extend a b).subst σ = extend (a.subst σ) (b.subst σ) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inl .extend))
  funext i
  fin_cases i <;> rfl

theorem weaken_subst (σ : V → Expression W) (a b : Expression V) :
    (weaken a b).subst σ = weaken (a.subst σ) (b.subst σ) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inl .weaken))
  funext i
  fin_cases i <;> rfl

theorem generic_subst (σ : V → Expression W) (a b : Expression V) :
    (generic a b).subst σ = generic (a.subst σ) (b.subst σ) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inl .generic))
  funext i
  fin_cases i <;> rfl

theorem identity_subst (σ : V → Expression W) (a b c : Expression V) :
    (Contextual.identity a b c).subst σ = Contextual.identity (a.subst σ) (b.subst σ) (c.subst σ) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inr .identity))
  funext i
  fin_cases i <;> rfl

theorem identitySub_subst (σ : V → Expression W) (a : Expression V) :
    (identitySub a).subst σ = identitySub (a.subst σ) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inl .id))
  funext i
  fin_cases i
  rfl

theorem j_subst (σ : V → Expression W) (a b c d e : Expression V) :
    (Contextual.j a b c d e).subst σ = Contextual.j (a.subst σ) (b.subst σ) (c.subst σ) (d.subst σ) (e.subst σ) := by
  apply congrArg (@FinitaryTerm.node signature.Operation signature.arity W (.inr .j))
  funext i
  fin_cases i <;> rfl

theorem leftConcat_subst (σ : V → Expression W) (g a x y z p q : Expression V) :
    (leftConcat g a x y z p q).subst σ =
      leftConcat (g.subst σ) (a.subst σ) (x.subst σ) (y.subst σ) (z.subst σ)
        (p.subst σ) (q.subst σ) := by
  simp only [leftConcat, Reference.Tail.code, Reference.Tail.map,
    LeftConcatFrame.motive, LeftConcatFrame.q, LeftConcatFrame.finalType,
    LeftConcatFrame.finalFixed, LeftConcatFrame.finalZ, LeftConcatFrame.qProjection,
    LeftConcatFrame.withZ, LeftConcatFrame.pathType, LeftConcatFrame.pathProjection,
    LeftConcatFrame.qType, LeftConcatFrame.zType, LeftConcatFrame.zProjection,
    LeftConcatFrame.movingZ, LeftConcatFrame.moving, LeftConcatFrame.z,
    LeftConcatFrame.fixedZ, LeftConcatFrame.fixed, LeftConcatArguments.atQ,
    LeftConcatArguments.atZ, LeftConcatArguments.atPath, Contextual.endpoint,
    Contextual.pathFamily, Contextual.sectionSub, liftSyntax,
    subTm_subst, subTy_subst, path_subst, root_subst, telCons_subst, telNil_subst, pair_subst, comp_subst, extend_subst, weaken_subst, generic_subst, identity_subst, identitySub_subst, j_subst]
end LeftConcatRecipe
namespace Equal
variable {V : Type} {Ω : List (Judgment V)}
def leftConcat {g g' a a' x x' y y' z z' p p' q q' : Expression V}
    (hg : Equal (Ω := Ω) g g') (ha : Equal (Ω := Ω) a a') (hx : Equal (Ω := Ω) x x')
    (hy : Equal (Ω := Ω) y y') (hz : Equal (Ω := Ω) z z')
    (hp : Equal (Ω := Ω) p p') (hq : Equal (Ω := Ω) q q') :
    Equal (Ω := Ω) (TelescopePresentation.leftConcat g a x y z p q)
      (TelescopePresentation.leftConcat g' a' x' y' z' p' q') := by
  have e := recipe (TelescopePresentation.leftConcat (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6) : Expression (Fin 7))
    ![g,a,x,y,z,p,q] ![g',a',x',y',z',p',q']
    (Fin.cases hg (Fin.cases ha (Fin.cases hx (Fin.cases hy (Fin.cases hz (Fin.cases hp (Fin.cases hq (fun i => nomatch i))))))))
  rw [LeftConcatRecipe.leftConcat_subst, LeftConcatRecipe.leftConcat_subst] at e
  simpa [Term.subst, Term.var, FinitaryTerm.bind] using e
end Equal
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
