import SquareKit.Internal.DependentJudgments.TelescopeAuthoring

/-! Contextual J on an explicitly presented dependent tail. Expansion of the
root context and its substitution is derived in the existing named theory. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory Reference
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ A x D d : Expression V} {T : Reference.Tail V}

namespace Presented
variable (hx : Tm (Ω := Ω) Γ A x) (hT : Reference.Presented Ω (path A x) T)

def rootDomain : Equal (Ω := Ω)
    (total (pullback (T.code (path A x)) (root A x))) (T.rootDomain Γ A x) :=
  (unary (Contextual.Equal.total (.hypothesis List.mem_cons_self))
    (hT.pullback_eq hx.family.context hx.root)).transitive
      (hT.reindex hx.family.context hx.root).total_eq

def rootMap : Equal (Ω := Ω) (rootTail A x (T.code (path A x))) (T.map Γ (root A x)) := by
  have e := Derivation.rule (T := theory) (Sum.inr (.rootTailDef T.length))
    ![Γ, A, x, T.code (path A x)]
    (Fin.cases (by simpa [Tm, theory, extraRule] using hx)
      (Fin.cases (by simpa [Reference.Target, theory, extraRule] using hT.typing) (fun i => nomatch i)))
  have h : Equal (Ω := Ω) (rootTail A x (T.code (path A x)))
      (tailMap (T.code (path A x)) (root A x)) := by
    simpa [Equal, theory, extraRule, Atom.subst] using e
  exact h.transitive (hT.map_eq hx.family.context hx.root)

variable (hD : Ty (Ω := Ω) (T.total (path A x)) D)
variable (hd : Tm (Ω := Ω) (T.rootDomain Γ A x) (subTy D (T.map Γ (root A x))) d)

/-- Only the mathematical motive and branch are supplied. Converting the
explicit root presentation to the primitive J presentation is internal. -/
def branch : Tm (Ω := Ω) (total (pullback (T.code (path A x)) (root A x)))
    (subTy D (rootTail A x (T.code (path A x)))) d :=
  (hd.convert (Equal.subTy (.reflexive D) (rootMap hx hT).symmetric)).recontext
    (rootDomain hx hT).symmetric

def eliminate : Tm (Ω := Ω) (T.total (path A x)) D
    (j A x (T.code (path A x)) D d) :=
  (hx.j hT.typing (hD.recontext hT.total_eq.symmetric) (branch hx hT hd)).recontext hT.total_eq

/-- The computation equation refers to the explicit root substitution and
retains the selected branch term, rather than only existence of a branch. -/
def beta : Equal (Ω := Ω)
    (subTm (j A x (T.code (path A x)) D d) (T.map Γ (root A x))) d :=
  (Equal.subTm (.reflexive _) (rootMap hx hT).symmetric).transitive
    (hx.jBeta hT.typing (hD.recontext hT.total_eq.symmetric) (branch hx hT hd))
end Presented
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
