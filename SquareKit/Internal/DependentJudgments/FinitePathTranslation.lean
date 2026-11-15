import SquareKit.Internal.DependentJudgments.FiniteTailTranslation

/-! The path substitution of a presented finite tail is its recursively
reindexed source tail. The extra equations are explicit target rules. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory TelescopePresentation
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)} {Γ Δ A x σ : Expression V}

private def extension (a : Extra) (θ : Fin (extraRule a).parameterCount → Expression V)
    (h : ∀ i, Target (Ω := Ω) (((extraRule a).premise i).subst θ)) :
    Target (Ω := Ω) ((extraRule a).conclusion.subst θ) :=
  Derivation.rule (T := TelescopePresentation.theory) (Sum.inr a) θ h

namespace Presented
noncomputable def root_context_eq {T : Tail V} (hT : Presented Ω (path A x) T)
    (hx : Target (Ω := Ω) (term Γ A x)) :
    Target (Ω := Ω) (.eq (total (pullback (T.code (path A x)) (root A x)))
      (T.rootDomain Γ A x)) := by
  have hA := unary (Tm.family (Γ := Γ) (A := A) (t := x) (.hypothesis (by simp))) hx
  have hΓ := unary (Ty.context (Γ := Γ) (A := A) (.hypothesis (by simp))) hA
  have hr := unary (Tm.root (Γ := Γ) (A := A) (x := x) (.hypothesis (by simp))) hx
  apply Derivation.transitive _ ((hT.reindex hΓ hr).total_eq)
  exact Derivation.congruence (T := TelescopePresentation.theory) (.inr .total)
    (Fin.cases (hT.pullback_eq hΓ hr) (fun i => nomatch i))

noncomputable def root_map_eq {T : Tail V} (hT : Presented Ω (path A x) T)
    (hx : Target (Ω := Ω) (term Γ A x)) :
    Target (Ω := Ω) (.eq (rootTail A x (T.code (path A x))) (T.map Γ (root A x))) := by
  have hA := unary (Tm.family (Γ := Γ) (A := A) (t := x) (.hypothesis (by simp))) hx
  have hΓ := unary (Ty.context (Γ := Γ) (A := A) (.hypothesis (by simp))) hA
  have hr := unary (Tm.root (Γ := Γ) (A := A) (x := x) (.hypothesis (by simp))) hx
  have e := extension (Ω := Ω) (.rootTailDef T.length) ![Γ, A, x, T.code (path A x)]
    (Fin.cases (by simpa [extraRule] using hx)
      (Fin.cases (by simpa [extraRule] using hT.typing) (fun i => nomatch i)))
  have er : Target (Ω := Ω) (.eq (rootTail A x (T.code (path A x)))
      (tailMap (T.code (path A x)) (root A x))) := by simpa [extraRule] using e
  exact .transitive er (hT.map_eq hΓ hr)

noncomputable def alongPath {T : Tail V} (hT : Presented Ω (path A x) T)
    (hx : Target (Ω := Ω) (term Γ A x)) (hs : Target (Ω := Ω) (substitution Δ Γ σ)) :
    Presented Ω (path (subTy A σ) (subTm x σ)) (T.alongPath A x σ) := by
  have hp := binary (Tm.pathSub (Γ := Γ) (Δ := Δ) (A := A) (x := x) (σ := σ)
    (.hypothesis (by simp)) (.hypothesis (by simp))) hx hs
  have hxs := binary (Tm.substitute (Γ := Γ) (Δ := Δ) (A := A) (t := x) (σ := σ)
    (.hypothesis (by simp)) (.hypothesis (by simp))) hx hs
  have hc := unary (Tm.path (Γ := Δ) (A := subTy A σ) (x := subTm x σ) (.hypothesis (by simp))) hxs
  exact hT.reindex hc hp

noncomputable def path_code_eq {T : Tail V} (hT : Presented Ω (path A x) T)
    (hx : Target (Ω := Ω) (term Γ A x)) (hs : Target (Ω := Ω) (substitution Δ Γ σ)) :
    Target (Ω := Ω) (.eq (pathTail A x (T.code (path A x)) σ)
      ((T.alongPath A x σ).code (path (subTy A σ) (subTm x σ)))) := by
  have e := extension (Ω := Ω) (.pathTailDef T.length) ![Γ, A, x, T.code (path A x), Δ, σ]
    (Fin.cases (by simpa [extraRule] using hx)
      (Fin.cases (by simpa [extraRule] using hT.typing)
        (Fin.cases (by simpa [extraRule] using hs) (fun i => nomatch i))))
  have e' : Target (Ω := Ω) (.eq (pathTail A x (T.code (path A x)) σ)
      (pullback (T.code (path A x)) (pathSub A x σ))) := by simpa [extraRule] using e
  have hp := binary (Tm.pathSub (Γ := Γ) (Δ := Δ) (A := A) (x := x) (σ := σ)
    (.hypothesis (by simp)) (.hypothesis (by simp))) hx hs
  have hxs := binary (Tm.substitute (Γ := Γ) (Δ := Δ) (A := A) (t := x) (σ := σ)
    (.hypothesis (by simp)) (.hypothesis (by simp))) hx hs
  have hc := unary (Tm.path (Γ := Δ) (A := subTy A σ) (x := subTm x σ) (.hypothesis (by simp))) hxs
  exact .transitive e' (hT.pullback_eq hc hp)

noncomputable def path_map_eq {T : Tail V} (hT : Presented Ω (path A x) T)
    (hx : Target (Ω := Ω) (term Γ A x)) (hs : Target (Ω := Ω) (substitution Δ Γ σ)) :
    Target (Ω := Ω) (.eq (pathTailMap A x (T.code (path A x)) σ) (T.alongPathMap A x σ)) := by
  have e := extension (Ω := Ω) (.pathTailMapDef T.length) ![Γ, A, x, T.code (path A x), Δ, σ]
    (Fin.cases (by simpa [extraRule] using hx)
      (Fin.cases (by simpa [extraRule] using hT.typing)
        (Fin.cases (by simpa [extraRule] using hs) (fun i => nomatch i))))
  have e' : Target (Ω := Ω) (.eq (pathTailMap A x (T.code (path A x)) σ)
      (tailMap (T.code (path A x)) (pathSub A x σ))) := by simpa [extraRule] using e
  have hp := binary (Tm.pathSub (Γ := Γ) (Δ := Δ) (A := A) (x := x) (σ := σ)
    (.hypothesis (by simp)) (.hypothesis (by simp))) hx hs
  have hxs := binary (Tm.substitute (Γ := Γ) (Δ := Δ) (A := A) (t := x) (σ := σ)
    (.hypothesis (by simp)) (.hypothesis (by simp))) hx hs
  have hc := unary (Tm.path (Γ := Δ) (A := subTy A σ) (x := subTm x σ) (.hypothesis (by simp))) hxs
  exact .transitive e' (hT.map_eq hc hp)

end Presented
end SquareKit.Internal.DependentJudgments.Contextual.Reference
