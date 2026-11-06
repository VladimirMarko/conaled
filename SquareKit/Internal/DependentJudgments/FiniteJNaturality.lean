import SquareKit.Internal.DependentJudgments.FiniteJTranslation

/-! J substitution with an actual recursively reindexed source tail. The
branch is explicitly substituted along the typed telescope-square map. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory TelescopePresentation
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}

private def original (a : Contextual.Axiom)
    (θ : Fin (Contextual.rule a).parameterCount → Expression V)
    (h : ∀ i, Target (Ω := Ω) (((Contextual.rule a).premise i).subst θ)) :
    Target (Ω := Ω) ((Contextual.rule a).conclusion.subst θ) :=
  Derivation.rule (T := TelescopePresentation.theory) (.inl (.inr a)) θ h

private def extension (a : Extra) (θ : Fin (extraRule a).parameterCount → Expression V)
    (h : ∀ i, Target (Ω := Ω) (((extraRule a).premise i).subst θ)) :
    Target (Ω := Ω) ((extraRule a).conclusion.subst θ) :=
  Derivation.rule (T := TelescopePresentation.theory) (.inr a) θ h

noncomputable def branchContextEq {Γ Δ A x σ : Expression V} {T : Tail V}
    (hx : Target (Ω := Ω) (term Γ A x)) (hT : Presented Ω (path A x) T)
    (hs : Target (Ω := Ω) (substitution Δ Γ σ)) :
    Target (Ω := Ω) (.eq
      (total (pullback (pathTail A x (T.code (path A x)) σ)
        (root (subTy A σ) (subTm x σ))))
      ((T.alongPath A x σ).rootDomain Δ (subTy A σ) (subTm x σ))) := by
  have hxs := binary (Tm.substitute (Γ := Γ) (Δ := Δ) (A := A) (t := x) (σ := σ)
    (.hypothesis (by simp)) (.hypothesis (by simp))) hx hs
  apply Derivation.transitive _ ((hT.alongPath hx hs).root_context_eq hxs)
  exact Derivation.congruence (T := TelescopePresentation.theory) (.inr .total)
    (Fin.cases (Derivation.congruence (T := TelescopePresentation.theory) (.inr .pullback)
      (Fin.cases (hT.path_code_eq hx hs) (Fin.cases (.reflexive _) (fun i => nomatch i))))
      (fun i => nomatch i))

noncomputable def translateBranchMap {Γ Δ A x σ : Expression V} {T : Tail V}
    (hx : Target (Ω := Ω) (term Γ A x)) (hT : Presented Ω (path A x) T)
    (hs : Target (Ω := Ω) (substitution Δ Γ σ)) :
    Target (Ω := Ω) (substitution
      ((T.alongPath A x σ).rootDomain Δ (subTy A σ) (subTm x σ))
      (T.rootDomain Γ A x) (branchMap A x (T.code (path A x)) σ)) := by
  have r := original (Ω := Ω) (.branchMap T.length) ![Γ, A, x, T.code (path A x), Δ, σ]
    (Fin.cases (by simpa [Contextual.rule] using hx)
      (Fin.cases (by simpa [Contextual.rule] using hT.typing)
        (Fin.cases (by simpa [Contextual.rule] using hs) (fun i => nomatch i))))
  have hb : Target (Ω := Ω) (substitution
      (total (pullback (pathTail A x (T.code (path A x)) σ) (root (subTy A σ) (subTm x σ))))
      (total (pullback (T.code (path A x)) (root A x)))
      (branchMap A x (T.code (path A x)) σ)) := by simpa [Contextual.rule] using r
  exact Derivation.conversion (T := TelescopePresentation.theory) (.inl .substitution)
    (Fin.cases (branchContextEq hx hT hs) (Fin.cases (hT.root_context_eq hx)
      (Fin.cases (.reflexive _) (fun i => nomatch i)))) hb

noncomputable def translateBranchSquare {Γ Δ A x σ : Expression V} {T : Tail V}
    (hx : Target (Ω := Ω) (term Γ A x)) (hT : Presented Ω (path A x) T)
    (hs : Target (Ω := Ω) (substitution Δ Γ σ)) :
    Target (Ω := Ω) (.eq
      (comp (T.alongPathMap A x σ)
        ((T.alongPath A x σ).map Δ (root (subTy A σ) (subTm x σ))))
      (comp (T.map Γ (root A x)) (branchMap A x (T.code (path A x)) σ))) := by
  have hxs := binary (Tm.substitute (Γ := Γ) (Δ := Δ) (A := A) (t := x) (σ := σ)
    (.hypothesis (by simp)) (.hypothesis (by simp))) hx hs
  have r := extension (Ω := Ω) (.branchSquare T.length) ![Γ, A, x, T.code (path A x), Δ, σ]
    (Fin.cases (by simpa [extraRule] using hx)
      (Fin.cases (by simpa [extraRule] using hT.typing)
        (Fin.cases (by simpa [extraRule] using hs) (fun i => nomatch i))))
  have e : Target (Ω := Ω) (.eq
      (comp (pathTailMap A x (T.code (path A x)) σ)
        (rootTail (subTy A σ) (subTm x σ) (pathTail A x (T.code (path A x)) σ)))
      (comp (rootTail A x (T.code (path A x))) (branchMap A x (T.code (path A x)) σ))) := by
    simpa [extraRule] using r
  have er : Target (Ω := Ω) (.eq
      (rootTail (subTy A σ) (subTm x σ) (pathTail A x (T.code (path A x)) σ))
      ((T.alongPath A x σ).map Δ (root (subTy A σ) (subTm x σ)))) := by
    apply Derivation.transitive _ ((hT.alongPath hx hs).root_map_eq hxs)
    exact Derivation.congruence (T := TelescopePresentation.theory) (.inr .rootTail)
      (Fin.cases (.reflexive _) (Fin.cases (.reflexive _)
        (Fin.cases (hT.path_code_eq hx hs) (fun i => nomatch i))))
  apply Derivation.transitive _ (Derivation.transitive e _)
  · exact Derivation.congruence (T := TelescopePresentation.theory) (.inl .comp)
      (Fin.cases (.symmetric (hT.path_map_eq hx hs)) (Fin.cases (.symmetric er) (fun i => nomatch i)))
  · exact Derivation.congruence (T := TelescopePresentation.theory) (.inl .comp)
      (Fin.cases (hT.root_map_eq hx) (Fin.cases (.reflexive _) (fun i => nomatch i)))

noncomputable def translateJSub {Γ Δ A x D d σ : Expression V} {T : Tail V}
    (hx : Target (Ω := Ω) (term Γ A x)) (hT : Presented Ω (path A x) T)
    (hD : Target (Ω := Ω) (family (T.total (path A x)) D))
    (hd : Target (Ω := Ω) (term (T.rootDomain Γ A x) (subTy D (T.map Γ (root A x))) d))
    (hs : Target (Ω := Ω) (substitution Δ Γ σ)) :
    Target (Ω := Ω) (.eq
      (subTm (j A x (T.code (path A x)) D d) (T.alongPathMap A x σ))
      (j (subTy A σ) (subTm x σ)
        ((T.alongPath A x σ).code (path (subTy A σ) (subTm x σ)))
        (subTy D (T.alongPathMap A x σ))
        (subTm d (branchMap A x (T.code (path A x)) σ)))) := by
  let inputs := prepareJ hx hT hD hd
  have e := original (Ω := Ω) (.jSub T.length) ![Γ, A, x, T.code (path A x), D, d, Δ, σ]
    (Fin.cases (by simpa [Contextual.rule] using hx)
      (Fin.cases (by simpa [Contextual.rule] using hT.typing)
        (Fin.cases (by simpa [Contextual.rule] using inputs.motive)
          (Fin.cases (by simpa [Contextual.rule] using inputs.branch)
            (Fin.cases (by simpa [Contextual.rule] using hs) (fun i => nomatch i))))))
  have ej : Target (Ω := Ω) (.eq
      (subTm (j A x (T.code (path A x)) D d) (pathTailMap A x (T.code (path A x)) σ))
      (j (subTy A σ) (subTm x σ) (pathTail A x (T.code (path A x)) σ)
        (subTy D (pathTailMap A x (T.code (path A x)) σ))
        (reindexBranch A x (T.code (path A x)) σ D d))) := by
    simpa [Contextual.rule] using e
  have er := extension (Ω := Ω) (.reindexBranchDef T.length)
    ![Γ, A, x, T.code (path A x), D, d, Δ, σ]
    (Fin.cases (by simpa [extraRule] using hx)
      (Fin.cases (by simpa [extraRule] using hT.typing)
        (Fin.cases (by simpa [extraRule] using inputs.motive)
          (Fin.cases (by simpa [extraRule] using inputs.branch)
            (Fin.cases (by simpa [extraRule] using hs) (fun i => nomatch i))))))
  have ed : Target (Ω := Ω) (.eq (reindexBranch A x (T.code (path A x)) σ D d)
      (subTm d (branchMap A x (T.code (path A x)) σ))) := by simpa [extraRule] using er
  have ec := hT.path_code_eq hx hs
  have em := hT.path_map_eq hx hs
  have eD : Target (Ω := Ω) (.eq (subTy D (pathTailMap A x (T.code (path A x)) σ))
      (subTy D (T.alongPathMap A x σ))) :=
    Derivation.congruence (T := TelescopePresentation.theory) (.inl .subTy) (Fin.cases (.reflexive D) (Fin.cases em (fun i => nomatch i)))
  apply Derivation.transitive _ (Derivation.transitive ej _)
  · exact Derivation.congruence (T := TelescopePresentation.theory) (.inl .subTm)
      (Fin.cases (.reflexive _) (Fin.cases (.symmetric em) (fun i => nomatch i)))
  · exact Derivation.congruence (T := TelescopePresentation.theory) (.inr .j)
      (Fin.cases (.reflexive _) (Fin.cases (.reflexive _) (Fin.cases ec
        (Fin.cases eD (Fin.cases ed (fun i => nomatch i))))))

end SquareKit.Internal.DependentJudgments.Contextual.Reference
