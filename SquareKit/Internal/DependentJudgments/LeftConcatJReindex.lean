import SquareKit.Internal.DependentJudgments.LeftConcatReindex

/-! Stability of the selected left-J branch under object substitution. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory LeftConcatFrame
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A x σ : Expression V}
namespace LeftConcatReindex
variable (hx : Tm (Ω := Ω) Γ A x) (hs : Sub (Ω := Ω) Δ Γ σ)

def rootSquare : Equal (Ω := Ω)
    (comp (rootTail A x ((LeftConcatFrame.tail Γ A x).code (path A x)))
      (branchMap A x ((LeftConcatFrame.tail Γ A x).code (path A x)) σ))
    (comp (atQ (Γ := Γ) (Δ := Δ) (A := A) (x := x) (σ := σ))
      ((LeftConcatFrame.tail Δ (subTy A σ) (subTm x σ)).map Δ (root (subTy A σ) (subTm x σ)))) := by
  have e := Derivation.rule (T := theory) (Sum.inr (.branchSquare 2))
    ![Γ, A, x, (LeftConcatFrame.tail Γ A x).code (path A x), Δ, σ]
    (Fin.cases (by simpa [Tm, theory, extraRule] using hx)
      (Fin.cases (by simpa [Reference.Target, theory, extraRule, LeftConcatFrame.tail, Reference.Tail.length] using (tailTyped hx).typing)
        (Fin.cases (by simpa [Sub, theory, extraRule] using hs) (fun i => nomatch i))))
  have h : Equal (Ω := Ω)
      (comp (pathTailMap A x ((LeftConcatFrame.tail Γ A x).code (path A x)) σ)
        (rootTail (subTy A σ) (subTm x σ) (pathTail A x ((LeftConcatFrame.tail Γ A x).code (path A x)) σ)))
      (comp (rootTail A x ((LeftConcatFrame.tail Γ A x).code (path A x)))
        (branchMap A x ((LeftConcatFrame.tail Γ A x).code (path A x)) σ)) := by
    simpa [Equal, theory, extraRule, Atom.subst] using e
  exact h.symmetric.transitive (Equal.comp (pathTailMapEq hx hs)
    ((Equal.rootTail (.reflexive _) (.reflexive _) (pathTailEq hx hs)).transitive
      (Presented.rootMap (hx.substitute hs) (tailTyped (hx.substitute hs)))))

def branchSub : Equal (Ω := Ω)
    (reindexBranch A x ((LeftConcatFrame.tail Γ A x).code (path A x)) σ (motive Γ A x)
      (subTm (q Γ A x) ((LeftConcatFrame.tail Γ A x).map Γ (root A x))))
    (subTm (q Δ (subTy A σ) (subTm x σ))
      ((LeftConcatFrame.tail Δ (subTy A σ) (subTm x σ)).map Δ (root (subTy A σ) (subTm x σ)))) := by
  have hD := (motiveTyped hx).recontext (tailTyped hx).total_eq.symmetric
  have hd := Presented.branch hx (tailTyped hx) (branch hx)
  have e := Derivation.rule (T := theory) (Sum.inr (.reindexBranchDef 2))
    ![Γ,A,x,(LeftConcatFrame.tail Γ A x).code (path A x),motive Γ A x,
      subTm (q Γ A x) ((LeftConcatFrame.tail Γ A x).map Γ (root A x)),Δ,σ]
    (Fin.cases (by simpa [Tm, theory, extraRule] using hx)
      (Fin.cases (by simpa [Reference.Target, theory, extraRule, LeftConcatFrame.tail, Reference.Tail.length] using (tailTyped hx).typing)
        (Fin.cases (by simpa [Ty, theory, extraRule] using hD)
          (Fin.cases (by simpa [Tm, theory, extraRule] using hd)
            (Fin.cases (by simpa [Sub, theory, extraRule] using hs) (fun i => nomatch i))))))
  have h : Equal (Ω := Ω)
      (reindexBranch A x ((LeftConcatFrame.tail Γ A x).code (path A x)) σ (motive Γ A x)
        (subTm (q Γ A x) ((LeftConcatFrame.tail Γ A x).map Γ (root A x))))
      (subTm (subTm (q Γ A x) ((LeftConcatFrame.tail Γ A x).map Γ (root A x)))
        (branchMap A x ((LeftConcatFrame.tail Γ A x).code (path A x)) σ)) := by
    simpa [Equal, theory, extraRule, Atom.subst] using e
  have hq := (qTyped hx).recontext (tailTyped hx).total_eq.symmetric
  exact h.transitive ((Equal.subTm
    (Equal.subTm (.reflexive _) (Presented.rootMap hx (tailTyped hx)).symmetric) (.reflexive _)).transitive
      ((hq.subComp (hx.rootTail (tailTyped hx).typing) (hx.branchMap (tailTyped hx).typing hs)).transitive
        ((Equal.subTm (.reflexive _) (rootSquare hx hs)).transitive
          (((qTyped hx).subComp (atQTyped hx hs) (rootLiftQ (hx.substitute hs))).symmetric.transitive
            (Equal.subTm (qSub hx hs) (.reflexive _))))))

def genericSub : Equal (Ω := Ω)
    (subTm (j A x ((LeftConcatFrame.tail Γ A x).code (path A x)) (motive Γ A x)
      (subTm (q Γ A x) ((LeftConcatFrame.tail Γ A x).map Γ (root A x))))
      (atQ (Γ := Γ) (Δ := Δ) (A := A) (x := x) (σ := σ)))
    (j (subTy A σ) (subTm x σ)
      ((LeftConcatFrame.tail Δ (subTy A σ) (subTm x σ)).code (path (subTy A σ) (subTm x σ)))
      (motive Δ (subTy A σ) (subTm x σ))
      (subTm (q Δ (subTy A σ) (subTm x σ))
        ((LeftConcatFrame.tail Δ (subTy A σ) (subTm x σ)).map Δ (root (subTy A σ) (subTm x σ))))) :=
  (Equal.subTm (.reflexive _) (pathTailMapEq hx hs).symmetric).transitive
    ((hx.jSub (tailTyped hx).typing ((motiveTyped hx).recontext (tailTyped hx).total_eq.symmetric)
      (Presented.branch hx (tailTyped hx) (branch hx)) hs).transitive
      (Equal.j (.reflexive _) (.reflexive _) (pathTailEq hx hs)
        ((Equal.subTy (.reflexive _) (pathTailMapEq hx hs)).transitive (motiveSub hx hs))
        (branchSub hx hs)))
end LeftConcatReindex
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
