import SquareKit.Internal.DependentJudgments.Sigma.Authoring
import SquareKit.Internal.DependentJudgments.Sigma.PairStability

/-! Reindexing over the unchanged Sigma signature. Formation and pack naturality
are stability laws over existing operations. Inverse and eliminator naturality
are consequences of those laws and the selected comprehension isomorphism. -/
namespace SquareKit.Internal.DependentJudgments.Sigma
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
universe u

abbrev lift {V : Type} (Δ A σ : Expression V) : Expression V :=
  pairSub A (comp σ (weaken Δ (subTy A σ))) (generic Δ (subTy A σ))

namespace Reindexing
variable (M : PathTransport.Typed.Model.{u}) (S : Stable M.toStructuralModel)

private theorem lift_eval {V : Type}
    (ρ : V → Value M.toStructuralModel) (g a s : Expression V)
    (Γ Δ : M.Context) (A : M.Family Γ) (σ : M.Substitution Δ Γ)
    (hg : g.eval (algebra M S.toCapability) ρ = .context Δ)
    (ha : a.eval (algebra M S.toCapability) ρ = .family Γ A)
    (hs : s.eval (algebra M S.toCapability) ρ = .substitution Δ Γ σ) :
    (lift g a s).eval (algebra M S.toCapability) ρ =
      .substitution (M.extend Δ (M.subTy A σ)) (M.extend Γ A) (M.toStructuralModel.lift A σ) := by
  simp only [Term.eval, algebra, Contextual.algebra] at hg ha hs
  simp only [Term.eval, FinitaryTerm.fold, algebra, Contextual.algebra,
    DependentJudgments.operation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    hg, ha, hs, Value.familyAt_family, Value.substitutionAt_substitution]
  have ht : Value.term (M := M.toStructuralModel) (M.extend Δ (M.subTy A σ))
      (M.subTy (M.subTy A σ) (M.weaken Δ (M.subTy A σ))) (M.genericVariable Δ (M.subTy A σ)) =
      .term (M.extend Δ (M.subTy A σ))
        (M.subTy A (M.compSub σ (M.weaken Δ (M.subTy A σ))))
        (cast (congrArg (M.Section _) (M.subTy_comp A σ (M.weaken Δ (M.subTy A σ))))
          (M.genericVariable Δ (M.subTy A σ))) :=
    Value.term_eq (M.subTy_comp A σ (M.weaken Δ (M.subTy A σ))) (cast_heq _ _).symm
  rw [ht, Value.termAt_term]
  rfl

abbrev schema (out : Judgment (Fin 5)) : Rule signature where
  parameterCount := 5
  hypotheses := 3
  premise := ![family (.var 0) (.var 1), family (extend (.var 0) (.var 1)) (.var 2),
    substitution (.var 3) (.var 0) (.var 4)]
  conclusion := out

abbrev first : Expression (Fin 5) := subTy (.var 1) (.var 4)
abbrev firstLift : Expression (Fin 5) := lift (.var 3) (.var 1) (.var 4)
abbrev second : Expression (Fin 5) := subTy (.var 2) firstLift
abbrev sumLift : Expression (Fin 5) := lift (.var 3) (sigma (.var 1) (.var 2)) (.var 4)
abbrev branchLift : Expression (Fin 5) := lift (extend (.var 3) first) (.var 2) firstLift

abbrev sigmaSubRule := schema (.eq (subTy (sigma (.var 1) (.var 2)) (.var 4)) (sigma first second))
abbrev packSubRule := schema (.eq (comp sumLift (pack first second))
  (comp (pack (.var 1) (.var 2)) branchLift))
abbrev unpackSubRule := schema (.eq (comp (unpack (.var 1) (.var 2)) sumLift)
  (comp branchLift (unpack first second)))

theorem schema_valid (out : Judgment (Fin 5))
    (valid : ∀ (Γ : M.Context) (A : M.Family Γ) (B : M.Family (M.extend Γ A))
      (Δ : M.Context) (σ : M.Substitution Δ Γ),
      out.eval (algebra M S.toCapability)
        ![.context Γ, .family Γ A, .family (M.extend Γ A) B, .context Δ, .substitution Δ Γ σ]) :
    Satisfies (algebra M S.toCapability) (schema out) := by
  intro ρ h
  let ρ₀ : Fin 3 → Value M.toStructuralModel := fun i => ρ (i.castAdd 2)
  have h₀ : ∀ i, (formationRule.premise i).eval (algebra M S.toCapability) ρ₀ := by
    intro i
    fin_cases i <;> first | exact h 0 | exact h 1
  rcases formationSchema_inputs M S.toCapability _ ρ₀ h₀ with ⟨Γ, A, B, e⟩
  have hΓ := congrFun e 0
  have hA := congrFun e 1
  have hB := congrFun e 2
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .family Γ A at hA
  change ρ 2 = .family (M.extend Γ A) B at hB
  rcases h 2 with ⟨Δ, Γ', σ, hΔ, hΓ', hσ⟩
  change ρ 0 = .context Γ' at hΓ'
  have eΓ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have eρ : ρ = ![.context Γ, .family Γ A, .family (M.extend Γ A) B,
      .context Δ, .substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hA | exact hB | exact hΔ | exact hσ
  subst ρ
  exact valid Γ A B Δ σ

private theorem comparison_value {Γ Δ : M.Context} {A B : M.Family Δ} (h : A = B)
    (s : M.Substitution (M.extend Δ B) Γ) :
    Value.substitution (M.extend Δ A) Γ (M.compSub s (M.toStructuralModel.familyComparison h)) =
      Value.substitution (M.extend Δ B) Γ s := by
  cases h
  simp [M.comp_id_right]

private theorem sumMap_value (Γ Δ : M.Context) (A : M.Family Γ)
    (B : M.Family (M.extend Γ A)) (σ : M.Substitution Δ Γ) :
    Value.substitution _ _ (S.sumMap A B σ) =
      Value.substitution _ _ (M.toStructuralModel.lift (S.sigma A B) σ) :=
  comparison_value M (S.sigma_sub A B σ).symm _

private theorem formation_eval {V : Type} (ρ : V → Value M.toStructuralModel)
    (a b : Expression V) (Γ : M.Context) (A : M.Family Γ)
    (B : M.Family (M.extend Γ A))
    (ha : a.eval (algebra M S.toCapability) ρ = .family Γ A)
    (hb : b.eval (algebra M S.toCapability) ρ = .family (M.extend Γ A) B) :
    (sigma a b).eval (algebra M S.toCapability) ρ = .family Γ (S.sigma A B) := by
  change operation _ _ .sigma ![a.eval (algebra M S.toCapability) ρ, b.eval (algebra M S.toCapability) ρ] = _
  simp [ha, hb, operation]

private theorem subTy_eval {V : Type} (ρ : V → Value M.toStructuralModel)
    (a s : Expression V) (Γ Δ : M.Context) (A : M.Family Γ) (σ : M.Substitution Δ Γ)
    (ha : a.eval (algebra M S.toCapability) ρ = .family Γ A)
    (hs : s.eval (algebra M S.toCapability) ρ = .substitution Δ Γ σ) :
    (subTy a s).eval (algebra M S.toCapability) ρ = .family Δ (M.subTy A σ) := by
  change DependentJudgments.operation _ .subTy ![a.eval (algebra M S.toCapability) ρ, s.eval (algebra M S.toCapability) ρ] = _
  simp [ha, hs, DependentJudgments.operation]

private theorem comp_eval {V : Type} (ρ : V → Value M.toStructuralModel)
    (s t : Expression V) (Γ Δ Θ : M.Context) (σ : M.Substitution Δ Γ) (τ : M.Substitution Θ Δ)
    (hs : s.eval (algebra M S.toCapability) ρ = .substitution Δ Γ σ)
    (ht : t.eval (algebra M S.toCapability) ρ = .substitution Θ Δ τ) :
    (comp s t).eval (algebra M S.toCapability) ρ = .substitution Θ Γ (M.compSub σ τ) := by
  change DependentJudgments.operation _ .comp ![s.eval (algebra M S.toCapability) ρ, t.eval (algebra M S.toCapability) ρ] = _
  simp [hs, ht, DependentJudgments.operation]

theorem sigmaSub_valid : Satisfies (algebra M S.toCapability) sigmaSubRule := by
  apply schema_valid
  intro Γ A B Δ σ
  let ρ : Fin 5 → Value M.toStructuralModel :=
    ![.context Γ, .family Γ A, .family (M.extend Γ A) B, .context Δ, .substitution Δ Γ σ]
  have hl := lift_eval M S ρ (.var 3) (.var 1) (.var 4) Γ Δ A σ rfl rfl rfl
  have hA := subTy_eval M S ρ (.var 1) (.var 4) Γ Δ A σ rfl rfl
  have hB := subTy_eval M S ρ (.var 2) firstLift _ _ B _ rfl hl
  have hSum := formation_eval M S ρ (.var 1) (.var 2) Γ A B rfl rfl
  change (subTy (sigma (.var 1) (.var 2)) (.var 4) : Expression (Fin 5)).eval (algebra M S.toCapability) ρ = _
  rw [subTy_eval M S ρ _ _ _ _ _ _ hSum rfl, formation_eval M S ρ _ _ _ _ _ hA hB]
  exact congrArg (Value.family Δ) (S.sigma_sub A B σ)

private theorem pack_eval {V : Type} (ρ : V → Value M.toStructuralModel)
    (a b : Expression V) (Γ : M.Context) (A : M.Family Γ)
    (B : M.Family (M.extend Γ A))
    (ha : a.eval (algebra M S.toCapability) ρ = .family Γ A)
    (hb : b.eval (algebra M S.toCapability) ρ = .family (M.extend Γ A) B) :
    (pack a b).eval (algebra M S.toCapability) ρ = .substitution _ _ (S.pack A B) := by
  change operation _ _ .pack ![a.eval (algebra M S.toCapability) ρ, b.eval (algebra M S.toCapability) ρ] = _
  simp [ha, hb, operation]

private theorem unpack_eval {V : Type} (ρ : V → Value M.toStructuralModel)
    (a b : Expression V) (Γ : M.Context) (A : M.Family Γ)
    (B : M.Family (M.extend Γ A))
    (ha : a.eval (algebra M S.toCapability) ρ = .family Γ A)
    (hb : b.eval (algebra M S.toCapability) ρ = .family (M.extend Γ A) B) :
    (unpack a b).eval (algebra M S.toCapability) ρ = .substitution _ _ (S.unpack A B) := by
  change operation _ _ .unpack ![a.eval (algebra M S.toCapability) ρ, b.eval (algebra M S.toCapability) ρ] = _
  simp [ha, hb, operation]

private theorem extend_eval {V : Type} (ρ : V → Value M.toStructuralModel)
    (g a : Expression V) (Γ : M.Context) (A : M.Family Γ)
    (hg : g.eval (algebra M S.toCapability) ρ = .context Γ)
    (ha : a.eval (algebra M S.toCapability) ρ = .family Γ A) :
    (extend g a).eval (algebra M S.toCapability) ρ = .context (M.extend Γ A) := by
  change DependentJudgments.operation _ .extend ![g.eval (algebra M S.toCapability) ρ, a.eval (algebra M S.toCapability) ρ] = _
  simp [hg, ha, DependentJudgments.operation]

theorem packSub_valid : Satisfies (algebra M S.toCapability) packSubRule := by
  apply schema_valid
  intro Γ A B Δ σ
  let ρ : Fin 5 → Value M.toStructuralModel :=
    ![.context Γ, .family Γ A, .family (M.extend Γ A) B, .context Δ, .substitution Δ Γ σ]
  have hl := lift_eval M S ρ (.var 3) (.var 1) (.var 4) Γ Δ A σ rfl rfl rfl
  have hA := subTy_eval M S ρ (.var 1) (.var 4) Γ Δ A σ rfl rfl
  have hB := subTy_eval M S ρ (.var 2) firstLift _ _ B _ rfl hl
  have hSum := formation_eval M S ρ (.var 1) (.var 2) Γ A B rfl rfl
  have hsl := (lift_eval M S ρ (.var 3) (sigma (.var 1) (.var 2)) (.var 4)
    Γ Δ (S.sigma A B) σ rfl hSum rfl).trans (sumMap_value M S Γ Δ A B σ).symm
  have he := extend_eval M S ρ (.var 3) first Δ _ rfl hA
  have hbl := lift_eval M S ρ (extend (.var 3) first) (.var 2) firstLift _ _ B _ he rfl hl
  have hp := pack_eval M S ρ (.var 1) (.var 2) Γ A B rfl rfl
  have hp' := pack_eval M S ρ first second Δ _ _ hA hB
  change (comp sumLift (pack first second)).eval (algebra M S.toCapability) ρ = _
  rw [comp_eval M S ρ _ _ _ _ _ _ _ hsl hp', comp_eval M S ρ _ _ _ _ _ _ _ hp hbl]
  exact congrArg (Value.substitution _ _) (S.pack_sub A B σ)

theorem unpackSub_valid : Satisfies (algebra M S.toCapability) unpackSubRule := by
  apply schema_valid
  intro Γ A B Δ σ
  let ρ : Fin 5 → Value M.toStructuralModel :=
    ![.context Γ, .family Γ A, .family (M.extend Γ A) B, .context Δ, .substitution Δ Γ σ]
  have hl := lift_eval M S ρ (.var 3) (.var 1) (.var 4) Γ Δ A σ rfl rfl rfl
  have hA := subTy_eval M S ρ (.var 1) (.var 4) Γ Δ A σ rfl rfl
  have hB := subTy_eval M S ρ (.var 2) firstLift _ _ B _ rfl hl
  have hSum := formation_eval M S ρ (.var 1) (.var 2) Γ A B rfl rfl
  have hsl := (lift_eval M S ρ (.var 3) (sigma (.var 1) (.var 2)) (.var 4)
    Γ Δ (S.sigma A B) σ rfl hSum rfl).trans (sumMap_value M S Γ Δ A B σ).symm
  have he := extend_eval M S ρ (.var 3) first Δ _ rfl hA
  have hbl := lift_eval M S ρ (extend (.var 3) first) (.var 2) firstLift _ _ B _ he rfl hl
  have hp := unpack_eval M S ρ (.var 1) (.var 2) Γ A B rfl rfl
  have hp' := unpack_eval M S ρ first second Δ _ _ hA hB
  change (comp (unpack (.var 1) (.var 2)) sumLift).eval (algebra M S.toCapability) ρ = _
  rw [comp_eval M S ρ _ _ _ _ _ _ _ hp hsl, comp_eval M S ρ _ _ _ _ _ _ _ hbl hp']
  exact congrArg (Value.substitution _ _) (S.unpack_sub A B σ)

abbrev splitSchema (out : Judgment (Fin 7)) : Rule signature where
  parameterCount := 7
  hypotheses := 5
  premise := ![family (.var 0) (.var 1), family (extend (.var 0) (.var 1)) (.var 2),
    family (extend (.var 0) (sigma (.var 1) (.var 2))) (.var 3),
    term (branchContext (.var 0) (.var 1) (.var 2))
      (subTy (.var 3) (pack (.var 1) (.var 2))) (.var 4),
    substitution (.var 5) (.var 0) (.var 6)]
  conclusion := out

abbrev splitFirst : Expression (Fin 7) := subTy (.var 1) (.var 6)
abbrev splitFirstLift : Expression (Fin 7) := lift (.var 5) (.var 1) (.var 6)
abbrev splitSecond : Expression (Fin 7) := subTy (.var 2) splitFirstLift
abbrev splitSumLift : Expression (Fin 7) := lift (.var 5) (sigma (.var 1) (.var 2)) (.var 6)
abbrev splitBranchLift : Expression (Fin 7) := lift (extend (.var 5) splitFirst) (.var 2) splitFirstLift
abbrev splitSubRule := splitSchema (.eq (subTm (split (.var 1) (.var 2) (.var 4)) splitSumLift)
  (split splitFirst splitSecond (subTm (.var 4) splitBranchLift)))
abbrev branchTypeRule := splitSchema (.eq
  (subTy (subTy (.var 3) (pack (.var 1) (.var 2))) splitBranchLift)
  (subTy (subTy (.var 3) splitSumLift) (pack splitFirst splitSecond)))

theorem splitSchema_valid (out : Judgment (Fin 7))
    (valid : ∀ (Γ : M.Context) (A : M.Family Γ) (B : M.Family (M.extend Γ A))
      (C : M.Family (M.extend Γ (S.sigma A B)))
      (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B)))
      (Δ : M.Context) (σ : M.Substitution Δ Γ),
      out.eval (algebra M S.toCapability)
        ![.context Γ, .family Γ A, .family (M.extend Γ A) B,
          .family (M.extend Γ (S.sigma A B)) C,
          .term (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B)) d,
          .context Δ, .substitution Δ Γ σ]) :
    Satisfies (algebra M S.toCapability) (splitSchema out) := by
  intro ρ h
  let ρ₀ : Fin 5 → Value M.toStructuralModel := fun i => ρ (i.castAdd 2)
  have h₀ : ∀ i, (Sigma.splitRule.premise i).eval (algebra M S.toCapability) ρ₀ := by
    intro i
    fin_cases i <;> first | exact h 0 | exact h 1 | exact h 2 | exact h 3
  rcases Sigma.splitSchema_inputs M S.toCapability _ ρ₀ h₀ with ⟨Γ, A, B, C, d, e⟩
  have hΓ := congrFun e 0
  have hA := congrFun e 1
  have hB := congrFun e 2
  have hC := congrFun e 3
  have hd := congrFun e 4
  change ρ 0 = .context Γ at hΓ
  rcases h 4 with ⟨Δ, Γ', σ, hΔ, hΓ', hσ⟩
  change ρ 0 = .context Γ' at hΓ'
  have eΓ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have eρ : ρ = ![.context Γ, .family Γ A, .family (M.extend Γ A) B,
      .family (M.extend Γ (S.sigma A B)) C,
      .term (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B)) d,
      .context Δ, .substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hA | exact hB | exact hC | exact hd | exact hΔ | exact hσ
  subst ρ
  exact valid Γ A B C d Δ σ

private theorem subTm_eval {V : Type} (ρ : V → Value M.toStructuralModel)
    (t s : Expression V) (Γ Δ : M.Context) (A : M.Family Γ)
    (x : M.Section Γ A) (σ : M.Substitution Δ Γ)
    (ht : t.eval (algebra M S.toCapability) ρ = .term Γ A x)
    (hs : s.eval (algebra M S.toCapability) ρ = .substitution Δ Γ σ) :
    (subTm t s).eval (algebra M S.toCapability) ρ = .term Δ (M.subTy A σ) (M.subTm x σ) := by
  change DependentJudgments.operation _ .subTm ![t.eval (algebra M S.toCapability) ρ, s.eval (algebra M S.toCapability) ρ] = _
  simp [ht, hs, DependentJudgments.operation]

theorem splitSub_valid : Satisfies (algebra M S.toCapability) splitSubRule := by
  apply splitSchema_valid
  intro Γ A B C d Δ σ
  let ρ : Fin 7 → Value M.toStructuralModel :=
    ![.context Γ, .family Γ A, .family (M.extend Γ A) B,
      .family (M.extend Γ (S.sigma A B)) C,
      .term (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B)) d,
      .context Δ, .substitution Δ Γ σ]
  have hl := lift_eval M S ρ (.var 5) (.var 1) (.var 6) Γ Δ A σ rfl rfl rfl
  have hA := subTy_eval M S ρ (.var 1) (.var 6) Γ Δ A σ rfl rfl
  have hB := subTy_eval M S ρ (.var 2) splitFirstLift _ _ B _ rfl hl
  have hSum := formation_eval M S ρ (.var 1) (.var 2) Γ A B rfl rfl
  have hsl := (lift_eval M S ρ (.var 5) (sigma (.var 1) (.var 2)) (.var 6)
    Γ Δ (S.sigma A B) σ rfl hSum rfl).trans (sumMap_value M S Γ Δ A B σ).symm
  have he := extend_eval M S ρ (.var 5) splitFirst Δ _ rfl hA
  have hbl := lift_eval M S ρ (extend (.var 5) splitFirst) (.var 2) splitFirstLift _ _ B _ he rfl hl
  have hp := unpack_eval M S ρ (.var 1) (.var 2) Γ A B rfl rfl
  have hp' := unpack_eval M S ρ splitFirst splitSecond Δ _ _ hA hB
  have hd := subTm_eval M S ρ (.var 4) (unpack (.var 1) (.var 2)) _ _ _ d _ rfl hp
  have hd' := subTm_eval M S ρ (.var 4) splitBranchLift _ _ _ d _ rfl hbl
  change (subTm (split (.var 1) (.var 2) (.var 4)) splitSumLift).eval (algebra M S.toCapability) ρ = _
  rw [subTm_eval M S ρ _ _ _ _ _ _ _ hd hsl, subTm_eval M S ρ _ _ _ _ _ _ _ hd' hp']
  apply Value.term_eq
  · simp only [M.subTy_comp, S.unpack_sub, M.comp_assoc]
  · apply (M.subTm_comp _ _ _).trans
    rw [S.unpack_sub]
    exact (M.subTm_comp _ _ _).symm

theorem branchType_valid : Satisfies (algebra M S.toCapability) branchTypeRule := by
  apply splitSchema_valid
  intro Γ A B C d Δ σ
  let ρ : Fin 7 → Value M.toStructuralModel :=
    ![.context Γ, .family Γ A, .family (M.extend Γ A) B,
      .family (M.extend Γ (S.sigma A B)) C,
      .term (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B)) d,
      .context Δ, .substitution Δ Γ σ]
  have hl := lift_eval M S ρ (.var 5) (.var 1) (.var 6) Γ Δ A σ rfl rfl rfl
  have hA := subTy_eval M S ρ (.var 1) (.var 6) Γ Δ A σ rfl rfl
  have hB := subTy_eval M S ρ (.var 2) splitFirstLift _ _ B _ rfl hl
  have hSum := formation_eval M S ρ (.var 1) (.var 2) Γ A B rfl rfl
  have hsl := (lift_eval M S ρ (.var 5) (sigma (.var 1) (.var 2)) (.var 6)
    Γ Δ (S.sigma A B) σ rfl hSum rfl).trans (sumMap_value M S Γ Δ A B σ).symm
  have he := extend_eval M S ρ (.var 5) splitFirst Δ _ rfl hA
  have hbl := lift_eval M S ρ (extend (.var 5) splitFirst) (.var 2) splitFirstLift _ _ B _ he rfl hl
  have hp := pack_eval M S ρ (.var 1) (.var 2) Γ A B rfl rfl
  have hp' := pack_eval M S ρ splitFirst splitSecond Δ _ _ hA hB
  have hc := subTy_eval M S ρ (.var 3) (pack (.var 1) (.var 2)) _ _ C _ rfl hp
  have hc' := subTy_eval M S ρ (.var 3) splitSumLift _ _ C _ rfl hsl
  change (subTy (subTy (.var 3) (pack (.var 1) (.var 2))) splitBranchLift).eval (algebra M S.toCapability) ρ = _
  rw [subTy_eval M S ρ _ _ _ _ _ _ hc hbl, subTy_eval M S ρ _ _ _ _ _ _ hc' hp']
  exact congrArg (Value.family _) (S.branch_type A B σ C)

abbrev pairSchema (out : Judgment (Fin 7)) : Rule signature where
  parameterCount := 7
  hypotheses := 5
  premise := ![family (.var 0) (.var 1), family (extend (.var 0) (.var 1)) (.var 2),
    term (.var 0) (.var 1) (.var 3),
    term (.var 0) (subTy (.var 2) (pairSub (.var 1) (identitySub (.var 0)) (.var 3))) (.var 4),
    substitution (.var 5) (.var 0) (.var 6)]
  conclusion := out
abbrev pairSubRule := pairSchema (.eq
  (subTm (pair (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)) (.var 6))
  (pair (.var 5) splitFirst splitSecond (subTm (.var 3) (.var 6)) (subTm (.var 4) (.var 6))))

theorem pairSchema_valid (out : Judgment (Fin 7))
    (valid : ∀ (Γ : M.Context) (A : M.Family Γ) (B : M.Family (M.extend Γ A))
      (a : M.Section Γ A) (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A a)))
      (Δ : M.Context) (σ : M.Substitution Δ Γ),
      out.eval (algebra M S.toCapability)
        ![.context Γ, .family Γ A, .family (M.extend Γ A) B, .term Γ A a,
          .term Γ (M.subTy B (M.toStructuralModel.sectionSub A a)) b,
          .context Δ, .substitution Δ Γ σ]) :
    Satisfies (algebra M S.toCapability) (pairSchema out) := by
  intro ρ h
  let ρ₀ : Fin 3 → Value M.toStructuralModel := fun i => ρ (i.castAdd 4)
  have h₀ : ∀ i, (formationRule.premise i).eval (algebra M S.toCapability) ρ₀ := by
    intro i
    fin_cases i <;> first | exact h 0 | exact h 1
  rcases formationSchema_inputs M S.toCapability _ ρ₀ h₀ with ⟨Γ, A, B, e⟩
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
  have hs := sectionSub_eval M S.toCapability ρ (.var 0) (.var 1) (.var 3) Γ A a hΓ hA ha
  have ht := subTy_eval M S ρ (.var 2) (pairSub (.var 1) (identitySub (.var 0)) (.var 3))
    _ _ B _ hB hs
  have hb := h 3
  change ∃ Γ' B' b, ρ 0 = .context Γ' ∧
    (subTy (.var 2) (pairSub (.var 1) (identitySub (.var 0)) (.var 3))).eval (algebra M S.toCapability) ρ =
      .family Γ' B' ∧ ρ 4 = .term Γ' B' b at hb
  rw [ht] at hb
  rcases hb with ⟨Γ', B', b, eΓ, eB, hb⟩
  have eΓ' := Value.context.inj (eΓ.symm.trans hΓ)
  subst Γ'
  have eB' := eq_of_heq (Value.family.inj eB).2
  subst B'
  rcases h 4 with ⟨Δ, Γ', σ, hΔ, hΓ', hσ⟩
  change ρ 0 = .context Γ' at hΓ'
  have eΓ' := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have eρ : ρ = ![.context Γ, .family Γ A, .family (M.extend Γ A) B, .term Γ A a,
      .term Γ (M.subTy B (M.toStructuralModel.sectionSub A a)) b,
      .context Δ, .substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hA | exact hB | exact ha | exact hb | exact hΔ | exact hσ
  subst ρ
  exact valid Γ A B a b Δ σ

theorem pairSub_valid : Satisfies (algebra M S.toCapability) pairSubRule := by
  apply pairSchema_valid
  intro Γ A B a b Δ σ
  let ρ : Fin 7 → Value M.toStructuralModel :=
    ![.context Γ, .family Γ A, .family (M.extend Γ A) B, .term Γ A a,
      .term Γ (M.subTy B (M.toStructuralModel.sectionSub A a)) b,
      .context Δ, .substitution Δ Γ σ]
  have hl := lift_eval M S ρ (.var 5) (.var 1) (.var 6) Γ Δ A σ rfl rfl rfl
  have hA := subTy_eval M S ρ (.var 1) (.var 6) Γ Δ A σ rfl rfl
  have hB := subTy_eval M S ρ (.var 2) splitFirstLift _ _ B _ rfl hl
  have ha := subTm_eval M S ρ (.var 3) (.var 6) Γ Δ A a σ rfl rfl
  have hb := subTm_eval M S ρ (.var 4) (.var 6) Γ Δ _ b σ rfl rfl
  have hb' := hb.trans (Value.term_eq (Stable.pairSecond_type A B a σ)
    (cast_heq _ _).symm : _ = Value.term Δ _ (Stable.pairSecond A B a b σ))
  have hp := pair_eval M S.toCapability ρ (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
    Γ A B a b rfl rfl rfl rfl rfl
  have hp' := pair_eval M S.toCapability ρ (.var 5) splitFirst splitSecond
    (subTm (.var 3) (.var 6)) (subTm (.var 4) (.var 6)) Δ _ _ _ _ rfl hA hB ha hb'
  change (subTm (pair (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)) (.var 6) : Expression (Fin 7)).eval
    (algebra M S.toCapability) ρ = _
  rw [subTm_eval M S ρ _ _ _ _ _ _ _ hp rfl, hp']
  exact Value.term_eq (S.sigma_sub A B σ) (S.pair_sub A B a b σ)

/-- The second component remains dependent on the substituted first component. -/
abbrev pairSecondRule := pairSchema (.eq
  (subTy (subTy (.var 2) (pairSub (.var 1) (identitySub (.var 0)) (.var 3))) (.var 6))
  (subTy splitSecond (pairSub splitFirst (identitySub (.var 5)) (subTm (.var 3) (.var 6)))))

theorem pairSecond_valid : Satisfies (algebra M S.toCapability) pairSecondRule := by
  apply pairSchema_valid
  intro Γ A B a b Δ σ
  let ρ : Fin 7 → Value M.toStructuralModel :=
    ![.context Γ, .family Γ A, .family (M.extend Γ A) B, .term Γ A a,
      .term Γ (M.subTy B (M.toStructuralModel.sectionSub A a)) b,
      .context Δ, .substitution Δ Γ σ]
  have hl := lift_eval M S ρ (.var 5) (.var 1) (.var 6) Γ Δ A σ rfl rfl rfl
  have hA := subTy_eval M S ρ (.var 1) (.var 6) Γ Δ A σ rfl rfl
  have hB := subTy_eval M S ρ (.var 2) splitFirstLift _ _ B _ rfl hl
  have ha := subTm_eval M S ρ (.var 3) (.var 6) Γ Δ A a σ rfl rfl
  have hs := sectionSub_eval M S.toCapability ρ (.var 0) (.var 1) (.var 3) Γ A a rfl rfl rfl
  have hs' := sectionSub_eval M S.toCapability ρ (.var 5) splitFirst (subTm (.var 3) (.var 6))
    Δ _ _ rfl hA ha
  have hb := subTy_eval M S ρ (.var 2) _ _ _ B _ rfl hs
  change (subTy (subTy (.var 2) (pairSub (.var 1) (identitySub (.var 0)) (.var 3))) (.var 6) : Expression (Fin 7)).eval
    (algebra M S.toCapability) ρ = _
  rw [subTy_eval M S ρ _ _ _ _ _ _ hb rfl, subTy_eval M S ρ _ _ _ _ _ _ hB hs']
  exact congrArg (Value.family Δ) (Stable.pairSecond_type A B a σ)

/-- Only the first two clauses impose new stability requirements. The remaining
clauses package consequences proved above for ordinary source derivations. -/
inductive Axiom where
  | sigmaSub | packSub | unpackSub | pairSub | pairSecond | splitSub | branchType

def rule : Axiom → Rule signature
  | .sigmaSub => sigmaSubRule
  | .packSub => packSubRule
  | .unpackSub => unpackSubRule
  | .pairSub => pairSubRule
  | .pairSecond => pairSecondRule
  | .splitSub => splitSubRule
  | .branchType => branchTypeRule

/-- Axiom union keeps every source expression and judgment unchanged. -/
def theory : Theory signature where
  Axiom := Sum Sigma.theory.Axiom Axiom
  rule
    | .inl a => Sigma.theory.rule a
    | .inr a => rule a

theorem rule_valid : ∀ a, Satisfies (algebra M S.toCapability) (rule a)
  | .sigmaSub => sigmaSub_valid M S
  | .packSub => packSub_valid M S
  | .unpackSub => unpackSub_valid M S
  | .pairSub => pairSub_valid M S
  | .pairSecond => pairSecond_valid M S
  | .splitSub => splitSub_valid M S
  | .branchType => branchType_valid M S

noncomputable def model : GuardedTheory.Model theory where
  toAlgebra := algebra M S.toCapability
  rules
    | .inl a => (Sigma.model M S.toCapability).rules a
    | .inr a => rule_valid M S a

variable {V : Type} {Ω : List (Judgment V)}

/-- Inclusion of the Capability-only fragment preserves exact source data. -/
noncomputable def retain {a : Judgment V} (d : Derivation Sigma.theory Ω a) :
    Derivation theory Ω a := by
  induction d with
  | hypothesis h => exact .hypothesis h
  | rule a σ _ ih => exact .rule (T := theory) (Sum.inl a) σ ih
  | reflexive t => exact .reflexive t
  | symmetric _ ih => exact .symmetric ih
  | transitive _ _ ih ih' => exact .transitive ih ih'
  | congruence op _ ih => exact .congruence op ih
  | conversion p _ _ ih hp => exact .conversion p ih hp

/-- The final interpreter requires one model-side stability instance. Authors
supply source derivations and assumptions, including for dependent elimination. -/
theorem interpret {a : Judgment V} (d : Derivation theory Ω a)
    (M : PathTransport.Typed.Model.{u}) (S : Stable M.toStructuralModel)
    (ρ : V → Value M.toStructuralModel)
    (h : ∀ p ∈ Ω, p.eval (algebra M S.toCapability) ρ) :
    a.eval (algebra M S.toCapability) ρ := d.sound (model M S) ρ h

/-- Forgetting stability equations recovers the selected original interpreter. -/
noncomputable def forget : GuardedTheory.Model Sigma.theory where
  toAlgebra := (model M S).toAlgebra
  rules a := (model M S).rules (.inl a)

theorem forget_model : forget M S = Sigma.model M S.toCapability := rfl

end Reindexing
end SquareKit.Internal.DependentJudgments.Sigma
