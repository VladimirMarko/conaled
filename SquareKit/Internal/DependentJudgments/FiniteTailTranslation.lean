import SquareKit.Internal.DependentJudgments.FiniteTail

/-! Target-side expansion proofs for explicitly presented finite tails. These
are comparison lemmas, not a definition of reference derivability. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory TelescopePresentation
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)} {Γ Δ A σ : Expression V}

abbrev Target (a : Judgment V) := Derivation TelescopePresentation.theory Ω a

namespace Target
noncomputable def extend (h : Target (Ω := Ω) (family Γ A)) :
    Target (Ω := Ω) (context (Contextual.extend Γ A)) :=
  unary (Ty.extend (.hypothesis (by simp))) h

noncomputable def substitute (hA : Target (Ω := Ω) (family Γ A))
    (hs : Target (Ω := Ω) (substitution Δ Γ σ)) :
    Target (Ω := Ω) (family Δ (subTy A σ)) :=
  binary (Ty.substitute (Γ := Γ) (Δ := Δ) (A := A) (σ := σ) (.hypothesis (by simp)) (.hypothesis (by simp))) hA hs

noncomputable def lift (hA : Target (Ω := Ω) (family Γ A))
    (hs : Target (Ω := Ω) (substitution Δ Γ σ)) :
    Target (Ω := Ω) (substitution (Contextual.extend Δ (subTy A σ))
      (Contextual.extend Γ A) (liftSyntax Δ A σ)) := by
  have hB := substitute hA hs
  have hw := unary (Ty.weaken (Γ := Δ) (A := subTy A σ) (.hypothesis (by simp))) hB
  have hv := unary (Ty.generic (Γ := Δ) (A := subTy A σ) (.hypothesis (by simp))) hB
  have hσw := binary (Sub.comp (Γ := Γ) (Δ := Δ) (Θ := Contextual.extend Δ (subTy A σ))
    (σ := σ) (τ := weaken Δ (subTy A σ)) (.hypothesis (by simp)) (.hypothesis (by simp))) hs hw
  have e := ternary (Ty.subComp (Γ := Γ) (Δ := Δ) (Θ := Contextual.extend Δ (subTy A σ))
    (A := A) (σ := σ) (τ := weaken Δ (subTy A σ)) (.hypothesis (by simp)) (.hypothesis (by simp))
    (.hypothesis (by simp))) hA hs hw
  have ht := binary (Tm.convert (Γ := Contextual.extend Δ (subTy A σ))
    (A := subTy (subTy A σ) (weaken Δ (subTy A σ)))
    (B := subTy A (comp σ (weaken Δ (subTy A σ))))
    (t := generic Δ (subTy A σ)) (.hypothesis (by simp)) (.hypothesis (by simp))) hv e
  exact ternary (Sub.pair (Γ := Γ) (Δ := Contextual.extend Δ (subTy A σ))
    (A := A) (σ := comp σ (weaken Δ (subTy A σ)))
    (t := generic Δ (subTy A σ)) (.hypothesis (by simp)) (.hypothesis (by simp))
    (.hypothesis (by simp))) hA hσw ht
end Target

inductive Presented {V : Type} (Ω : List (Judgment V)) : Expression V → Tail V → Type where
  | nil {Γ : Expression V} : Target (Ω := Ω) (context Γ) → Presented Ω Γ .nil
  | cons {Γ A : Expression V} {T : Tail V} : Target (Ω := Ω) (family Γ A) →
      Presented Ω (extend Γ A) T → Presented Ω Γ (.cons A T)

namespace Presented
noncomputable def typing {T : Tail V} (h : Presented Ω Γ T) :
    Target (Ω := Ω) (telescope T.length Γ (T.code Γ)) := by
  induction h with
  | nil hΓ => exact unary (Ctx.nil (.hypothesis (by simp))) hΓ
  | cons hA hT ih => exact binary (Ty.cons (.hypothesis (by simp)) (.hypothesis (by simp))) hA ih

noncomputable def total_eq {T : Tail V} (h : Presented Ω Γ T) :
    Target (Ω := Ω) (.eq (Contextual.total (T.code Γ)) (T.total Γ)) := by
  induction h with
  | nil hΓ => exact unary (Ctx.totalNil (.hypothesis (by simp))) hΓ
  | @cons Γ A T hA hT ih =>
    have e : Target (Ω := Ω)
        (.eq (Contextual.total (telCons A (T.code (extend Γ A))))
          (Contextual.total (T.code (extend Γ A)))) := by
      have r := Derivation.rule (T := TelescopePresentation.theory)
        (Sum.inr (.totalCons T.length)) ![Γ, A, T.code (extend Γ A)]
        (Fin.cases (by simpa [Target, TelescopePresentation.theory, extraRule] using hA)
          (Fin.cases (by simpa [Target, TelescopePresentation.theory, extraRule] using hT.typing)
            (fun i => nomatch i)))
      simpa [Target, TelescopePresentation.theory, extraRule, Atom.subst, Tail.code, Tail.map] using r
    exact .transitive e ih

noncomputable def reindex {T : Tail V} (h : Presented Ω Γ T)
    (hΔ : Target (Ω := Ω) (context Δ))
    (hs : Target (Ω := Ω) (substitution Δ Γ σ)) : Presented Ω Δ (T.reindex Δ σ) := by
  induction h generalizing Δ σ with
  | nil => exact .nil hΔ
  | cons hA hT ih =>
    have hB := Target.substitute hA hs
    exact .cons hB (ih (Target.extend hB) (Target.lift hA hs))

noncomputable def pullback_eq {T : Tail V} (h : Presented Ω Γ T)
    (hΔ : Target (Ω := Ω) (context Δ))
    (hs : Target (Ω := Ω) (substitution Δ Γ σ)) :
    Target (Ω := Ω) (.eq (pullback (T.code Γ) σ) ((T.reindex Δ σ).code Δ)) := by
  induction h generalizing Δ σ with
  | nil => exact unary (Sub.pullbackNil (Γ := _) (Δ := Δ) (σ := σ) (.hypothesis (by simp))) hs
  | @cons Γ A T hA hT ih =>
    have hB := Target.substitute hA hs
    have e : Target (Ω := Ω) (.eq (pullback (telCons A (T.code (extend Γ A))) σ)
        (telCons (subTy A σ) (pullback (T.code (extend Γ A)) (liftSyntax Δ A σ)))) := by
      have r := Derivation.rule (T := TelescopePresentation.theory)
        (Sum.inr (.pullbackCons T.length)) ![Γ, Δ, A, T.code (extend Γ A), σ]
        (Fin.cases (by simpa [Target, TelescopePresentation.theory, extraRule] using hA)
          (Fin.cases (by simpa [Target, TelescopePresentation.theory, extraRule] using hT.typing)
            (Fin.cases (by simpa [Target, TelescopePresentation.theory, extraRule] using hs)
              (fun i => nomatch i))))
      simpa [Target, TelescopePresentation.theory, extraRule, Atom.subst, liftSyntax] using r
    apply Derivation.transitive e
    exact Derivation.congruence (T := TelescopePresentation.theory) (Sum.inr Operation.telCons)
      (Fin.cases (.reflexive _) (Fin.cases
        (ih (Target.extend hB) (Target.lift hA hs)) (fun i => nomatch i)))

noncomputable def map_eq {T : Tail V} (h : Presented Ω Γ T)
    (hΔ : Target (Ω := Ω) (context Δ))
    (hs : Target (Ω := Ω) (substitution Δ Γ σ)) :
    Target (Ω := Ω) (.eq (tailMap (T.code Γ) σ) (T.map Δ σ)) := by
  induction h generalizing Δ σ with
  | nil =>
    have r := Derivation.rule (T := TelescopePresentation.theory)
      (Sum.inr .tailMapNil) ![_, Δ, σ]
      (Fin.cases (by simpa [Target, TelescopePresentation.theory, extraRule] using hs)
        (fun i => nomatch i))
    simpa [Target, TelescopePresentation.theory, extraRule, Atom.subst, Tail.code, Tail.map] using r
  | @cons Γ A T hA hT ih =>
    have hB := Target.substitute hA hs
    have e : Target (Ω := Ω) (.eq (tailMap (telCons A (T.code (extend Γ A))) σ)
        (tailMap (T.code (extend Γ A)) (liftSyntax Δ A σ))) := by
      have r := Derivation.rule (T := TelescopePresentation.theory)
        (Sum.inr (.tailMapCons T.length)) ![Γ, Δ, A, T.code (extend Γ A), σ]
        (Fin.cases (by simpa [Target, TelescopePresentation.theory, extraRule] using hA)
          (Fin.cases (by simpa [Target, TelescopePresentation.theory, extraRule] using hT.typing)
            (Fin.cases (by simpa [Target, TelescopePresentation.theory, extraRule] using hs)
              (fun i => nomatch i))))
      simpa [Target, TelescopePresentation.theory, extraRule, Atom.subst, liftSyntax] using r
    exact .transitive e (ih (Target.extend hB) (Target.lift hA hs))

end Presented
end SquareKit.Internal.DependentJudgments.Contextual.Reference
