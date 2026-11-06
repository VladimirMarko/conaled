import SquareKit.Internal.DependentJudgments.FinitePathTranslation

/-! Boundary conversions shared by finite-tail J, its computation rule and
its substitution rule. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory TelescopePresentation
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}

structure PreparedJ {V : Type} (Ω : List (Judgment V)) (Γ A x D d : Expression V) (T : Tail V) where
  motive : Target (Ω := Ω) (family (total (T.code (path A x))) D)
  branch : Target (Ω := Ω) (term (total (pullback (T.code (path A x)) (root A x)))
    (subTy D (rootTail A x (T.code (path A x)))) d)
  totalEq : Target (Ω := Ω) (.eq (total (T.code (path A x))) (T.total (path A x)))
  rootEq : Target (Ω := Ω) (.eq (rootTail A x (T.code (path A x))) (T.map Γ (root A x)))
  branchContextEq : Target (Ω := Ω) (.eq (total (pullback (T.code (path A x)) (root A x)))
    (T.rootDomain Γ A x))

noncomputable def prepareJ {Γ A x D d : Expression V} {T : Tail V}
    (hx : Target (Ω := Ω) (term Γ A x)) (hT : Presented Ω (path A x) T)
    (hD : Target (Ω := Ω) (family (T.total (path A x)) D))
    (hd : Target (Ω := Ω) (term ((T.reindex Γ (root A x)).total Γ)
      (subTy D (T.map Γ (root A x))) d)) :
    PreparedJ Ω Γ A x D d T := by
  classical
  have hA := unary (Tm.family (Γ := Γ) (A := A) (t := x) (.hypothesis (by simp))) hx
  have hΓ := unary (Ty.context (Γ := Γ) (A := A) (.hypothesis (by simp))) hA
  have hr := unary (Tm.root (Γ := Γ) (A := A) (x := x) (.hypothesis (by simp))) hx
  have eT := hT.total_eq
  have hD' : Target (Ω := Ω) (family (total (T.code (path A x))) D) :=
    Derivation.conversion (T := TelescopePresentation.theory) (Sum.inl Predicate.family)
      (Fin.cases (.symmetric eT) (Fin.cases (.reflexive D) (fun i => nomatch i))) hD
  have ep := hT.pullback_eq hΓ hr
  have eb : Target (Ω := Ω) (.eq (total (pullback (T.code (path A x)) (root A x)))
      ((T.reindex Γ (root A x)).total Γ)) := by
    apply Derivation.transitive _ ((hT.reindex hΓ hr).total_eq)
    exact Derivation.congruence (T := TelescopePresentation.theory) (Sum.inr Operation.total)
      (Fin.cases ep (fun i => nomatch i))
  have er : Target (Ω := Ω) (.eq (rootTail A x (T.code (path A x)))
      (tailMap (T.code (path A x)) (root A x))) := by
    have r := Derivation.rule (T := TelescopePresentation.theory)
      (Sum.inr (.rootTailDef T.length)) ![Γ, A, x, T.code (path A x)]
      (Fin.cases (by simpa [Target, TelescopePresentation.theory, extraRule] using hx)
        (Fin.cases (by simpa [Target, TelescopePresentation.theory, extraRule] using hT.typing)
          (fun i => nomatch i)))
    simpa [Target, TelescopePresentation.theory, extraRule, Atom.subst] using r
  have em := Derivation.transitive er (hT.map_eq hΓ hr)
  have ed : Target (Ω := Ω) (.eq (subTy D (rootTail A x (T.code (path A x))))
      (subTy D (T.map Γ (root A x)))) :=
    Derivation.congruence (T := TelescopePresentation.theory) (Sum.inl .subTy)
      (Fin.cases (.reflexive D) (Fin.cases em (fun i => nomatch i)))
  have hd' : Target (Ω := Ω) (term (total (pullback (T.code (path A x)) (root A x)))
      (subTy D (rootTail A x (T.code (path A x)))) d) :=
    Derivation.conversion (T := TelescopePresentation.theory) (Sum.inl Predicate.term)
      (Fin.cases (.symmetric eb) (Fin.cases (.symmetric ed)
        (Fin.cases (.reflexive d) (fun i => nomatch i)))) hd
  exact ⟨hD', hd', eT, em, eb⟩

noncomputable def translateJ {Γ A x D d : Expression V} {T : Tail V}
    (hx : Target (Ω := Ω) (term Γ A x)) (hT : Presented Ω (path A x) T)
    (hD : Target (Ω := Ω) (family (T.total (path A x)) D))
    (hd : Target (Ω := Ω) (term ((T.reindex Γ (root A x)).total Γ)
      (subTy D (T.map Γ (root A x))) d)) :
    Target (Ω := Ω) (term (T.total (path A x)) D (j A x (T.code (path A x)) D d)) := by
  classical
  let data := prepareJ hx hT hD hd
  have hD' := data.motive
  have hd' := data.branch
  have eT := data.totalEq
  have hj : Target (Ω := Ω) (term (total (T.code (path A x))) D
      (j A x (T.code (path A x)) D d)) := by
    apply importProof (Tm.j (Ω := [term Γ A x,
      telescope T.length (path A x) (T.code (path A x)),
      family (total (T.code (path A x))) D,
      term (total (pullback (T.code (path A x)) (root A x)))
        (subTy D (rootTail A x (T.code (path A x)))) d]) (Γ := Γ) (A := A) (x := x)
      (n := T.length) (T := T.code (path A x)) (D := D) (d := d)
      (.hypothesis (by simp)) (.hypothesis (by simp))
      (.hypothesis (by simp)) (.hypothesis (by simp)))
    intro a ha
    simp at ha
    by_cases e : a = term Γ A x
    · subst a; exact hx
    · by_cases e' : a = telescope T.length (path A x) (T.code (path A x))
      · subst a; exact hT.typing
      · by_cases e'' : a = family (total (T.code (path A x))) D
        · subst a; exact hD'
        · have e''' := ((ha.resolve_left e).resolve_left e').resolve_left e''
          subst a; exact hd'
  exact Derivation.conversion (T := TelescopePresentation.theory) (Sum.inl Predicate.term)
    (Fin.cases eT (Fin.cases (.reflexive D) (Fin.cases (.reflexive _) (fun i => nomatch i)))) hj

noncomputable def translateJBeta {Γ A x D d : Expression V} {T : Tail V}
    (hx : Target (Ω := Ω) (term Γ A x)) (hT : Presented Ω (path A x) T)
    (hD : Target (Ω := Ω) (family (T.total (path A x)) D))
    (hd : Target (Ω := Ω) (term ((T.reindex Γ (root A x)).total Γ)
      (subTy D (T.map Γ (root A x))) d)) :
    Target (Ω := Ω) (.eq (subTm (j A x (T.code (path A x)) D d) (T.map Γ (root A x))) d) := by
  classical
  let data := prepareJ hx hT hD hd
  have hD' := data.motive
  have hd' := data.branch
  have em := data.rootEq
  have hj : Target (Ω := Ω) (.eq
      (subTm (j A x (T.code (path A x)) D d) (rootTail A x (T.code (path A x)))) d) := by
    apply importProof (Tm.jBeta (Ω := [term Γ A x,
      telescope T.length (path A x) (T.code (path A x)),
      family (total (T.code (path A x))) D,
      term (total (pullback (T.code (path A x)) (root A x)))
        (subTy D (rootTail A x (T.code (path A x)))) d]) (Γ := Γ) (A := A) (x := x)
      (n := T.length) (T := T.code (path A x)) (D := D) (d := d)
      (.hypothesis (by simp)) (.hypothesis (by simp))
      (.hypothesis (by simp)) (.hypothesis (by simp)))
    intro a ha
    simp at ha
    by_cases e : a = term Γ A x
    · subst a; exact hx
    · by_cases e' : a = telescope T.length (path A x) (T.code (path A x))
      · subst a; exact hT.typing
      · by_cases e'' : a = family (total (T.code (path A x))) D
        · subst a; exact hD'
        · have e''' := ((ha.resolve_left e).resolve_left e').resolve_left e''
          subst a; exact hd'
  apply Derivation.transitive _ hj
  exact Derivation.congruence (T := TelescopePresentation.theory) (Sum.inl .subTm)
    (Fin.cases (.reflexive _) (Fin.cases (.symmetric em) (fun i => nomatch i)))

end SquareKit.Internal.DependentJudgments.Contextual.Reference
