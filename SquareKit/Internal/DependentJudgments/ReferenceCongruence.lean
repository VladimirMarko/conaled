import SquareKit.Internal.DependentJudgments.ReferenceDerived

/-! Typed congruence includes finite telescope codes. Each changing argument has
an equality at a common boundary; both results must also be formed at their
common boundary. Context and family conversion supply these premises when the
dependent data changes. No untyped equation is admitted into the source. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory
variable {V : Type} {Ξ : List (Declaration V)}
namespace Derives
noncomputable section

/-- Equal context expressions give equal empty telescope codes, after converting
both codes to the same telescope boundary. -/
def nilCongruence {Γ Δ : Expression V} (e : Derives Ξ (.eq .ctx Γ Δ)) :
    Derives Ξ (.eq (.tel 0 Γ) (Contextual.telNil Γ) (Contextual.telNil Δ)) :=
  .congruence (.inr .telNil) ![.ctx]
    (.tailCode (.nil e.eqOperands.1))
    (.contextConvertTel (.tailCode (.nil e.eqOperands.2)) (.eqSymm e))
    (Fin.cases e (fun i => nomatch i))

/-- Congruence under a dependent telescope binder. The remainder equality is
at the original extended context, so a changed binder requires conversion of
the right remainder to that context before the premise can be supplied. -/
def consCongruence {Γ A A' : Expression V} {T T' : Tail V}
    (eA : Derives Ξ (.eq (.ty Γ) A A'))
    (hT : Derives Ξ (.tail (Contextual.extend Γ A) T))
    (hT' : Derives Ξ (.tail (Contextual.extend Γ A') T'))
    (hn : T'.length = T.length)
    (eT : Derives Ξ (.eq (.tel T.length (Contextual.extend Γ A))
      (T.code (Contextual.extend Γ A)) (T'.code (Contextual.extend Γ A')))) :
    Derives Ξ (.eq (.tel (T.length + 1) Γ)
      ((Tail.cons A T).code Γ) ((Tail.cons A' T').code Γ)) := by
  have hr : Derives Ξ (.has (.tel (T.length + 1) Γ) ((Tail.cons A' T').code Γ)) := by
    simpa [Tail.length, hn] using Derives.tailCode (.cons eA.eqOperands.2 hT')
  exact .congruence (.inr .telCons) ![.ty Γ, .tel T.length (Contextual.extend Γ A)]
    (.tailCode (.cons eA.eqOperands.1 hT)) hr
    (Fin.cases eA (Fin.cases eT (fun i => nomatch i)))

/-- Congruence of J in all five arguments. The boundaries of the arguments and
of the result are independent: conversion is checked before this rule applies. -/
def jCongruence {A A' x x' T T' D D' d d' : Expression V}
    {b bA bx bT bD bd : Boundary V}
    (hl : Derives Ξ (.has b (Contextual.j A x T D d)))
    (hr : Derives Ξ (.has b (Contextual.j A' x' T' D' d')))
    (eA : Derives Ξ (.eq bA A A')) (ex : Derives Ξ (.eq bx x x'))
    (eT : Derives Ξ (.eq bT T T')) (eD : Derives Ξ (.eq bD D D'))
    (ed : Derives Ξ (.eq bd d d')) :
    Derives Ξ (.eq b (Contextual.j A x T D d) (Contextual.j A' x' T' D' d')) :=
  .congruence (.inr .j) ![bA, bx, bT, bD, bd] hl hr
    (Fin.cases eA (Fin.cases ex (Fin.cases eT (Fin.cases eD (Fin.cases ed (fun i => nomatch i))))))

/-- The telescope argument of branch mapping has the same typed congruence
coverage as J, including changed tails and parameters. -/
def branchMapCongruence {A A' x x' T T' σ σ' : Expression V}
    {b bA bx bT bσ : Boundary V}
    (hl : Derives Ξ (.has b (Contextual.branchMap A x T σ)))
    (hr : Derives Ξ (.has b (Contextual.branchMap A' x' T' σ')))
    (eA : Derives Ξ (.eq bA A A')) (ex : Derives Ξ (.eq bx x x'))
    (eT : Derives Ξ (.eq bT T T')) (eσ : Derives Ξ (.eq bσ σ σ')) :
    Derives Ξ (.eq b (Contextual.branchMap A x T σ) (Contextual.branchMap A' x' T' σ')) :=
  .congruence (.inr .branchMap) ![bA, bx, bT, bσ] hl hr
    (Fin.cases eA (Fin.cases ex (Fin.cases eT (Fin.cases eσ (fun i => nomatch i)))))

/-- The fixed-tail branch equality from the adequacy review, with result
formation derived rather than assumed separately. -/
def jBranchCongruence {Γ A x D d d' : Expression V} {T : Tail V}
    (hx : Derives Ξ (.has (.tm Γ A) x)) (hT : Derives Ξ (.tail (Contextual.path A x) T))
    (hD : Derives Ξ (.has (.ty (T.total (Contextual.path A x))) D))
    (ed : Derives Ξ (.eq (.tm (T.rootDomain Γ A x)
      (Contextual.subTy D (T.map Γ (Contextual.root A x)))) d d')) :
    Derives Ξ (.eq (.tm (T.total (Contextual.path A x)) D)
      (Contextual.j A x (T.code (Contextual.path A x)) D d)
      (Contextual.j A x (T.code (Contextual.path A x)) D d')) :=
  jCongruence (.j hx hT hD ed.eqOperands.1) (.j hx hT hD ed.eqOperands.2)
    (.eqRefl (.termFamily hx)) (.eqRefl hx) (.eqRefl (.tailCode hT)) (.eqRefl hD) ed

/-- Changing the motive changes its restriction along the root map as well.
The branch and the left result are converted using the supplied family equality. -/
def jMotiveCongruence {Γ A x D D' d : Expression V} {T : Tail V}
    (hx : Derives Ξ (.has (.tm Γ A) x)) (hT : Derives Ξ (.tail (Contextual.path A x) T))
    (eD : Derives Ξ (.eq (.ty (T.total (Contextual.path A x))) D D'))
    (hd : Derives Ξ (.has (.tm (T.rootDomain Γ A x)
      (Contextual.subTy D (T.map Γ (Contextual.root A x)))) d)) :
    Derives Ξ (.eq (.tm (T.total (Contextual.path A x)) D')
      (Contextual.j A x (T.code (Contextual.path A x)) D d)
      (Contextual.j A x (T.code (Contextual.path A x)) D' d)) := by
  have hm := tailMap hT (.root hx)
  have er : Derives Ξ (.eq (.ty (T.rootDomain Γ A x))
      (Contextual.subTy D (T.map Γ (Contextual.root A x)))
      (Contextual.subTy D' (T.map Γ (Contextual.root A x)))) :=
    .congruence (.inl .subTy) ![.ty (T.total (Contextual.path A x)),
      .sub (T.rootDomain Γ A x) (T.total (Contextual.path A x))]
      (.subTy eD.eqOperands.1 hm) (.subTy eD.eqOperands.2 hm)
      (Fin.cases eD (Fin.cases (.eqRefl hm) (fun i => nomatch i)))
  exact jCongruence (.convert (.j hx hT eD.eqOperands.1 hd) eD)
    (.j hx hT eD.eqOperands.2 (.convert hd er))
    (.eqRefl (.termFamily hx)) (.eqRefl hx) (.eqRefl (.tailCode hT)) eD (.eqRefl hd)

end
end Derives
end SquareKit.Internal.DependentJudgments.Contextual.Reference
