import Examples.ReferenceDependentCalculus
import SquareKit.Internal.DependentJudgments.ReferenceCongruence

/-! Congruence on the existing satisfiable two-entry dependent example. The
branches, motives and tail codes compared below are syntactically different;
reflexivity alone cannot establish the claimed source equations. -/
namespace Examples.ReferenceDependentCalculus.Congruence
open SquareKit.GuardedTheory
open SquareKit.Internal.DependentJudgments.Contextual
open Reference

abbrev R := tail.rootDomain empty A x
abbrev branch' := subTm branch (identitySub R)

theorem branches_differ : branch' ≠ branch := by
  intro h
  cases h

noncomputable def branchEquality : Derives declarations
    (.eq (.tm R (subTy D rootMap)) branch' branch) := .subTmId hBranch

noncomputable def branchCongruence : Derives declarations
    (.eq (.tm ΓC D) (j A x (tail.code P) D branch') (j A x (tail.code P) D branch)) :=
  Derives.jBranchCongruence hx hTail hD branchEquality

noncomputable def guardedBranchCongruence : Target (Ω := declarations.map Declaration.encode)
    (.eq (j A x (tail.code P) D branch') (j A x (tail.code P) D branch)) :=
  translate branchCongruence

theorem interpretedBranchCongruence : (Claim.eq (.tm ΓC D)
    (j A x (tail.code P) D branch') (j A x (tail.code P) D branch)).Valid Native.M Native.environment :=
  sound Native.M Native.environment Native.declarations_valid branchCongruence

abbrev D' := subTy D (identitySub ΓC)
theorem motives_differ : D ≠ D' := by
  intro h
  cases h

noncomputable def motiveCongruence : Derives declarations
    (.eq (.tm ΓC D') (j A x (tail.code P) D branch) (j A x (tail.code P) D' branch)) :=
  Derives.jMotiveCongruence hx hTail (.eqSymm (.subTyId hD)) hBranch

noncomputable def guardedMotiveCongruence : Target (Ω := declarations.map Declaration.encode)
    (.eq (j A x (tail.code P) D branch) (j A x (tail.code P) D' branch)) :=
  translate motiveCongruence

theorem interpretedMotiveCongruence : (Claim.eq (.tm ΓC D')
    (j A x (tail.code P) D branch) (j A x (tail.code P) D' branch)).Valid Native.M Native.environment :=
  sound Native.M Native.environment Native.declarations_valid motiveCongruence

/-- Change the last dependent family, whose concrete fiber is Fin (b + 1).
The empty remainder is now based at a different context expression. -/
abbrev C' := subTy C (identitySub ΓB)
abbrev ΓC' := extend ΓB C'
abbrev tail' : Reference.Tail (Fin 4) := .cons B (.cons C' .nil)
noncomputable def eC : Derives declarations (.eq (.ty ΓB) C C') := .eqSymm (.subTyId hC)
noncomputable def hC' : Derives declarations (.has (.ty ΓB) C') := eC.eqOperands.2
noncomputable def eΓC : Derives declarations (.eq .ctx ΓC ΓC') :=
  .congruence (.inl .extend) ![.ctx, .ty ΓB] (.extend hC) (.extend hC')
    (Fin.cases (.eqRefl (.typeContext hC)) (Fin.cases eC (fun i => nomatch i)))
noncomputable def tailCongruence : Derives declarations
    (.eq (.tel 2 P) (tail.code P) (tail'.code P)) :=
  Derives.consCongruence (.eqRefl hB)
    (.cons hC (.nil (.extend hC))) (.cons hC' (.nil (.extend hC'))) rfl
    (Derives.consCongruence eC (.nil (.extend hC)) (.nil (.extend hC')) rfl
      (Derives.nilCongruence eΓC))

noncomputable def guardedTailCongruence : Target (Ω := declarations.map Declaration.encode)
    (.eq (tail.code P) (tail'.code P)) := translate tailCongruence

theorem interpretedTailCongruence : (Claim.eq (.tel 2 P)
    (tail.code P) (tail'.code P)).Valid Native.M Native.environment :=
  sound Native.M Native.environment Native.declarations_valid tailCongruence

/-- Schematic instantiation preserves the new telescope judgment and the actual
congruence proof; it does not silently replace it by target reflexivity. -/
noncomputable def instantiatedTailCongruence {W : Type} (θ : Fin 4 → Expression W) :=
  tailCongruence.instantiate θ

end Examples.ReferenceDependentCalculus.Congruence
