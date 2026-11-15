import SquareKit.Internal.DependentJudgments.PrimitiveSigma.Rules

/-! Introduction into the new object sum is constructed from comprehension and
packing. Its typing and computation use the over-base equation. -/
namespace SquareKit.Internal.DependentJudgments.PrimitiveSigma
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
universe u

namespace Capability
variable {M : StructuralModel.{u}} (S : Capability M)
variable {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
variable (a : M.Section Γ A) (b : M.Section Γ (M.subTy B (M.sectionSub A a)))

def pairSubstitution : M.Substitution Γ (M.extend Γ (S.sigma A B)) :=
  M.compSub (S.pack A B) (M.pairSub B (M.sectionSub A a) b)

theorem pair_over :
    M.compSub (M.weaken Γ (S.sigma A B)) (S.pairSubstitution A B a b) = M.idSub Γ := by
  unfold pairSubstitution
  rw [← M.comp_assoc, S.pack_over, M.comp_assoc, M.weaken_pair, M.weaken_section]

theorem pair_type :
    M.subTy (M.subTy (S.sigma A B) (M.weaken Γ (S.sigma A B))) (S.pairSubstitution A B a b) =
      S.sigma A B := by
  rw [M.subTy_comp, S.pair_over, M.subTy_id]

def pair : M.Section Γ (S.sigma A B) :=
  cast (congrArg (M.Section Γ) (S.pair_type A B a b))
    (M.subTm (M.genericVariable Γ (S.sigma A B)) (S.pairSubstitution A B a b))

theorem pair_heq : HEq (S.pair A B a b)
    (M.subTm (M.genericVariable Γ (S.sigma A B)) (S.pairSubstitution A B a b)) := cast_heq _ _

/-- The section obtained by object introduction is exactly the packed dependent pair. -/
theorem section_pair : M.sectionSub (S.sigma A B) (S.pair A B a b) = S.pairSubstitution A B a b := by
  apply M.pair_ext (S.sigma A B)
  · rw [M.weaken_section, S.pair_over]
  · exact (M.variable_section _ _).trans (S.pair_heq A B a b)

/-- The ordinary elimination-at-a-pair computation retains the dependent result type. -/
theorem split_pair (C : M.Family (M.extend Γ (S.sigma A B)))
    (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B))) :
    HEq (M.subTm (S.split A B C d) (M.sectionSub (S.sigma A B) (S.pair A B a b)))
      (M.subTm d (M.pairSub B (M.sectionSub A a) b)) := by
  rw [S.section_pair]
  apply (M.subTm_comp _ _ _).symm.trans
  exact M.subTm_congr rfl (S.split_beta A B C d)
    (M.pairSub B (M.sectionSub A a) b)

end Capability

variable (M : PathTransport.Typed.Model.{u}) (S : Capability M.toStructuralModel)

/-- Source section construction keeps the chosen section through the inherited
identity-substitution type conversion. -/
theorem sectionSub_eval {V : Type} (ρ : V → Value M.toStructuralModel)
    (g a t : Expression V) (Γ : M.Context) (A : M.Family Γ) (x : M.Section Γ A)
    (hg : g.eval (algebra M S) ρ = .context Γ)
    (ha : a.eval (algebra M S) ρ = .family Γ A)
    (ht : t.eval (algebra M S) ρ = .term Γ A x) :
    (pairSub a (identitySub g) t).eval (algebra M S) ρ =
      .substitution Γ (M.extend Γ A) (M.toStructuralModel.sectionSub A x) := by
  simp only [Term.eval, algebra, Contextual.algebra] at hg ha ht
  simp only [Term.eval, FinitaryTerm.fold, algebra, Contextual.algebra,
    DependentJudgments.operation, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, hg, ha, ht, Value.substitutionAt_substitution]
  have hx : Value.term Γ A x = .term Γ (M.subTy A (M.idSub Γ))
      (cast (congrArg (M.Section Γ) (M.subTy_id A).symm) x) :=
    Value.term_eq (M.subTy_id A).symm (cast_heq _ _).symm
  rw [hx, Value.termAt_term]
  rfl

theorem pair_eval {V : Type} (ρ : V → Value M.toStructuralModel)
    (g a b x y : Expression V) (Γ : M.Context) (A : M.Family Γ)
    (B : M.Family (M.extend Γ A)) (t : M.Section Γ A)
    (s : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A t)))
    (hg : g.eval (algebra M S) ρ = .context Γ)
    (ha : a.eval (algebra M S) ρ = .family Γ A)
    (hb : b.eval (algebra M S) ρ = .family (M.extend Γ A) B)
    (hx : x.eval (algebra M S) ρ = .term Γ A t)
    (hy : y.eval (algebra M S) ρ = .term Γ (M.subTy B (M.toStructuralModel.sectionSub A t)) s) :
    (pair g a b x y).eval (algebra M S) ρ = .term Γ (S.sigma A B) (S.pair A B t s) := by
  have hs := sectionSub_eval M S ρ g a x Γ A t hg ha hx
  change (subTm (generic g (sigma a b)) (comp (pack a b) (pairSub b (pairSub a (identitySub g) x) y))).eval _ _ = _
  simp only [Term.eval, algebra, Contextual.algebra] at hg ha hb hx hy hs
  simp only [Term.eval, FinitaryTerm.fold, algebra, Contextual.algebra,
    DependentJudgments.operation, operation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hg, ha, hb, hy, hs,
    inputs_values, Value.familyAt_family, Value.termAt_term, Value.substitutionAt_substitution,
    Value.termIn_term]
  exact Value.term_eq (S.pair_type A B t s) (S.pair_heq A B t s).symm


theorem pair_valid : Satisfies (algebra M S) pairRule := by
  intro ρ h
  let ρ₀ : Fin 3 → Value M.toStructuralModel := fun i => ρ (i.castAdd 2)
  have h₀ : ∀ i, (formationRule.premise i).eval (algebra M S) ρ₀ := by
    intro i
    fin_cases i <;> first | exact h 0 | exact h 1
  rcases formationSchema_inputs M S _ ρ₀ h₀ with ⟨Γ, A, B, e⟩
  have hΓ := congrFun e 0
  have hA := congrFun e 1
  have hB := congrFun e 2
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .family Γ A at hA
  change ρ 2 = .family (M.extend Γ A) B at hB
  rcases h 2 with ⟨Γ', A', a, eΓ, eA, ha⟩
  change ρ 0 = .context Γ' at eΓ
  change ρ 1 = .family Γ' A' at eA
  change ρ 3 = .term Γ' A' a at ha
  have eΓ' := Value.context.inj (eΓ.symm.trans hΓ)
  subst Γ'
  have eA' := eq_of_heq (Value.family.inj (eA.symm.trans hA)).2
  subst A'
  have hs := sectionSub_eval M S ρ (.var 0) (.var 1) (.var 3) Γ A a hΓ hA ha
  have ht : (subTy (.var 2) (pairSub (.var 1) (identitySub (.var 0)) (.var 3))).eval
      (algebra M S) ρ = .family Γ (M.subTy B (M.toStructuralModel.sectionSub A a)) := by
    change DependentJudgments.operation M.toStructuralModel .subTy
      ![ρ 2, (pairSub (.var 1) (identitySub (.var 0)) (.var 3)).eval (algebra M S) ρ] = _
    simp [hB, hs, DependentJudgments.operation]
  have hb := h 3
  change ∃ Γ' B' b, ρ 0 = .context Γ' ∧
    (subTy (.var 2) (pairSub (.var 1) (identitySub (.var 0)) (.var 3))).eval (algebra M S) ρ =
      .family Γ' B' ∧ ρ 4 = .term Γ' B' b at hb
  rw [ht] at hb
  rcases hb with ⟨Γ', B', b, eΓ, eB, hb⟩
  have eΓ' := Value.context.inj (eΓ.symm.trans hΓ)
  subst Γ'
  have eB' := eq_of_heq (Value.family.inj eB).2
  subst B'
  refine ⟨Γ, S.sigma A B, S.pair A B a b, hΓ, ?_, ?_⟩
  · simp [Term.eval, algebra, operation, hA, hB]
  · exact pair_eval M S ρ (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) Γ A B a b hΓ hA hB ha hb

end SquareKit.Internal.DependentJudgments.PrimitiveSigma
