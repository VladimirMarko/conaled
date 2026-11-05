import SquareKit.Internal.DependentJudgments.ContextualOperations
import SquareKit.Internal.DependentJudgments.ComprehensionMaps

/-! Contextual recipes commute with model maps on their defined source domain.
The comparison uses the constructed telescope, motive and branch transport;
it does not require reflection of the interpreter's index checks. -/

namespace SquareKit.Internal.DependentJudgments
open GuardedTheory PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u v

namespace Value
variable {M : StructuralModel.{u}} {N : StructuralModel.{v}}

theorem telescopeAt_some {Γ : M.Context} {n : Nat} {T : Telescope M Γ n} {x : Value M}
    (h : telescopeAt Γ x = some ⟨n, T⟩) : x = .telescope Γ n T := by
  cases x <;> simp only [telescopeAt] at h
  all_goals try contradiction
  split at h
  · rename_i e
    cases e
    simp only [Option.some.injEq, Sigma.mk.inj_iff] at h
    rcases h with ⟨hn, hT⟩
    cases hn
    cases eq_of_heq hT
    rfl
  · contradiction

theorem telescope_heq_eq {Γ Δ : M.Context} {n} {T : Telescope M Γ n}
    {U : Telescope M Δ n} (hΓ : Γ = Δ) (hT : HEq T U) :
    Value.telescope Γ n T = .telescope Δ n U := by
  cases hΓ; cases eq_of_heq hT; rfl

end Value

namespace Contextual
variable {M : StructuralModel.{u}} {N : StructuralModel.{v}}

theorem point_some {a x : Value M} {p : Point M} (h : point M a x = some p) :
    a = .family p.context p.family ∧ x = .term p.context p.family p.term := by
  cases a <;> simp only [point] at h
  all_goals try contradiction
  rename_i Γ A
  cases hx : Value.termAt Γ A x with
  | none => simp [hx] at h
  | some t =>
    simp only [hx, Option.map_some, Option.some.injEq] at h
    cases h
    exact ⟨rfl, Value.termAt_some hx⟩

theorem tail_some {a x t : Value M} {p : Tail M} (h : tail M a x t = some p) :
    a = .family p.context p.family ∧ x = .term p.context p.family p.term ∧
      t = .telescope (M.pathContext p.family p.term) p.length p.telescope := by
  cases hp : point M a x with
  | none => simp [tail, hp] at h
  | some q =>
    cases ht : Value.telescopeAt (M.pathContext q.family q.term) t with
    | none => simp [tail, hp, ht] at h
    | some T =>
      rcases T with ⟨n, T⟩
      simp [tail, hp, ht] at h
      cases h
      exact ⟨(point_some hp).1, (point_some hp).2, Value.telescopeAt_some ht⟩

theorem problem_some {a x t c d : Value M} {p : Problem M}
    (h : problem M a x t c d = some p) :
    a = .family p.context p.family ∧ x = .term p.context p.family p.term ∧
      t = .telescope (M.pathContext p.family p.term) p.length p.telescope ∧
      c = .family p.telescope.total p.motive ∧
      d = .term (Telescope.pullback M p.telescope (M.rootSub p.family p.term)).total
        (M.subTy p.motive (M.rootTail p.family p.term p.telescope)) p.branch := by
  cases hp : tail M a x t with
  | none => simp [problem, hp] at h
  | some q =>
    cases hc : Value.familyAt q.telescope.total c with
    | none => simp [problem, hp, hc] at h
    | some C =>
      cases hd : Value.termAt (Telescope.pullback M q.telescope (M.rootSub q.family q.term)).total
          (M.subTy C (M.rootTail q.family q.term q.telescope)) d with
      | none => simp [problem, hp, hc, hd] at h
      | some b =>
        simp [problem, hp, hc, hd] at h
        cases h
        exact ⟨(tail_some hp).1, (tail_some hp).2.1, (tail_some hp).2.2,
          Value.familyAt_some hc, Value.termAt_some hd⟩

def Point.map (F : StructuralMap M N) (p : Point M) : Point N :=
  ⟨F.context p.context, F.family p.family, F.mapTm p.term⟩

def Tail.map (F : StructuralMap M N) (p : Tail M) : Tail N :=
  ⟨p.toPoint.map F, p.length, F.pathTelescope p.family p.term p.telescope⟩

def Problem.map (F : StructuralMap M N) (p : Problem M) : Problem N :=
  ⟨p.toTail.map F, F.jMotive p.family p.term p.telescope p.motive,
    F.jBranch p.family p.term p.telescope p.motive p.branch⟩

theorem point_map (F : StructuralMap M N) {a x : Value M} {p : Point M}
    (h : point M a x = some p) :
    point N (Value.map F a) (Value.map F x) = some (p.map F) := by
  rcases point_some h with ⟨ha, hx⟩
  simp [ha, hx, Value.map, Point.map]

theorem tail_map (F : StructuralMap M N) {a x t : Value M} {p : Tail M}
    (h : tail M a x t = some p) :
    tail N (Value.map F a) (Value.map F x) (Value.map F t) = some (p.map F) := by
  rcases tail_some h with ⟨ha, hx, ht⟩
  rw [ha, hx, ht]
  simp only [Value.map]
  have hT := Value.telescope_heq_eq (F.pathContext p.family p.term)
    (show HEq (F.telescope p.telescope) (F.pathTelescope p.family p.term p.telescope) from
      (cast_heq _ _).symm)
  rw [hT]
  simp [Tail.map, Point.map]

theorem problem_map (F : StructuralMap M N) {a x t c d : Value M} {p : Problem M}
    (h : problem M a x t c d = some p) :
    problem N (Value.map F a) (Value.map F x) (Value.map F t)
      (Value.map F c) (Value.map F d) = some (p.map F) := by
  rcases problem_some h with ⟨ha, hx, ht, hc, hd⟩
  have hp : tail M a x t = some p.toTail := by rw [ha, hx, ht]; exact tail_values ..
  have hC := Value.family_heq_eq (F.pathTelescope_total p.family p.term p.telescope)
    (show HEq (F.family p.motive) (F.jMotive p.family p.term p.telescope p.motive) from
      (cast_heq _ _).symm)
  have hD := Value.term_heq_eq (F.rootTelescope_total p.family p.term p.telescope)
    (F.jBranch_type p.family p.term p.telescope p.motive)
    (F.jBranch_heq p.family p.term p.telescope p.motive p.branch).symm
  simp only [problem, tail_map F hp]
  rw [hc, hd]
  simp only [Value.map]
  rw [hC, hD]
  simp [Problem.map, Tail.map, Point.map]

@[simp] theorem point_invalid_left (x : Value M) : point M .invalid x = none := rfl
@[simp] theorem point_invalid_right (a : Value M) : point M a .invalid = none := by
  cases a <;> simp [point, Value.termAt]
@[simp] theorem tail_invalid_left (x t : Value M) : tail M .invalid x t = none := by
  simp [tail]
@[simp] theorem tail_invalid_point (a t : Value M) : tail M a .invalid t = none := by
  simp [tail]
@[simp] theorem tail_invalid_telescope (a x : Value M) : tail M a x .invalid = none := by
  simp [tail, Value.telescopeAt]
@[simp] theorem problem_invalid_left (x t c d : Value M) :
    problem M .invalid x t c d = none := by simp [problem]
@[simp] theorem problem_invalid_point (a t c d : Value M) :
    problem M a .invalid t c d = none := by simp [problem]
@[simp] theorem problem_invalid_telescope (a x c d : Value M) :
    problem M a x .invalid c d = none := by simp [problem]
@[simp] theorem problem_invalid_motive (a x t d : Value M) :
    problem M a x t .invalid d = none := by simp [problem, Value.familyAt]
@[simp] theorem problem_invalid_branch (a x t c : Value M) :
    problem M a x t c .invalid = none := by simp [problem, Value.termAt]

/-- Failure propagates from each operand of a contextual operation. -/
theorem operands_defined (M : Model.{u}) (op : Operation)
    (args : Fin op.arity → Value M.toStructuralModel)
    (h : operation M op args ≠ .invalid) : ∀ i, args i ≠ .invalid := by
  cases op <;> intro i <;> fin_cases i
  all_goals first
    | change args 0 ≠ .invalid
    | change args 1 ≠ .invalid
    | change args 2 ≠ .invalid
    | change args 3 ≠ .invalid
    | change args 4 ≠ .invalid
    | change args 5 ≠ .invalid
  all_goals intro hi
  all_goals simp [operation, hi, Value.termAt, Value.telescopeAt] at h
  all_goals repeat' first | split at h | contradiction

private theorem pullback_total (F : StructuralMap M N) {Γ Δ n}
    (T : Telescope M Γ n) (σ : M.Substitution Δ Γ) :
    F.context (Telescope.pullback M T σ).total =
      (Telescope.pullback N (F.telescope T) (F.substitution σ)).total :=
  (F.telescope_total _).trans (congrArg (Telescope.total N) (F.telescope_pullback T σ))

private theorem path_sub_context (F : StructuralMap M N) {Γ Δ}
    (A : M.Family Γ) (x : M.Section Γ A) (σ : M.Substitution Δ Γ) :
    F.context (M.pathContext (M.subTy A σ) (M.subTm x σ)) =
      N.pathContext (N.subTy (F.family A) (F.substitution σ))
        (N.subTm (F.mapTm x) (F.substitution σ)) :=
  (F.pathContext _ _).trans (N.pathContext_heq rfl (heq_of_eq (F.subTy A σ)) (F.subTm x σ))

private theorem path_tail_total (F : StructuralMap M N) {Γ Δ n}
    (A : M.Family Γ) (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n)
    (σ : M.Substitution Δ Γ) :
    F.context (M.pathTail A x T σ).total =
      (N.pathTail (F.family A) (F.mapTm x) (F.pathTelescope A x T) (F.substitution σ)).total :=
  (F.telescope_total _).trans
    (Telescope.total_heq N (path_sub_context F A x σ) (F.pathTail A x T σ))

private theorem reindex_branch_type (F : StructuralMap M N) {Γ Δ n}
    (A : M.Family Γ) (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n)
    (σ : M.Substitution Δ Γ) (C : M.Family T.total) :
    HEq (F.family (M.subTy (M.subTy C (M.pathTailMap A x T σ))
      (M.rootTail (M.subTy A σ) (M.subTm x σ) (M.pathTail A x T σ))))
      (N.subTy (N.subTy (F.jMotive A x T C)
        (N.pathTailMap (F.family A) (F.mapTm x) (F.pathTelescope A x T) (F.substitution σ)))
        (N.rootTail (N.subTy (F.family A) (F.substitution σ))
          (N.subTm (F.mapTm x) (F.substitution σ))
          (N.pathTail (F.family A) (F.mapTm x) (F.pathTelescope A x T) (F.substitution σ)))) := by
  apply (heq_of_eq (congrArg F.family (M.branchMap_type A x T σ C))).trans
  apply (heq_of_eq (F.subTy _ _)).trans
  apply HEq.trans _ (heq_of_eq (N.branchMap_type (F.family A) (F.mapTm x)
    (F.pathTelescope A x T) (F.substitution σ) (F.jMotive A x T C))).symm
  exact N.subTy_heq (F.rootTelescope_total A x T) (F.reindexedRootTelescope_total A x T σ)
    (F.jBranch_type A x T C) (F.branchMap A x T σ)

theorem operation_map {M : Model.{u}} {N : Model.{v}} (F : ModelMap M N)
    (op : Operation) (args : Fin op.arity → Value M.toStructuralModel)
    (h : operation M op args ≠ .invalid) :
    Value.map F.toStructuralMap (operation M op args) =
      operation N op (Value.map F.toStructuralMap ∘ args) := by
  let f := F.toStructuralMap
  change Value.map f (operation M op args) = operation N op (Value.map f ∘ args)
  cases op with
  | identity =>
    cases hp : point M.toStructuralModel (args 0) (args 1) with
    | none => simp [operation, hp] at h
    | some p =>
      cases hy : Value.termAt p.context p.family (args 2) with
      | none => simp [operation, hp, hy] at h
      | some y =>
        have hm := point_map f hp
        have hy' := Value.termAt_some hy
        simp only [operation, Function.comp_apply, hp, hm]
        simpa [operation, hp, hm, hy', Function.comp_def, Value.map, Point.map] using
          Value.family_heq_eq rfl (heq_of_eq (f.identity p.family p.term y))
  | reflexivity =>
    cases hp : point M.toStructuralModel (args 0) (args 1) with
    | none => simp [operation, hp] at h
    | some p =>
      have hm := point_map f hp
      simp only [operation, Function.comp_apply, hp, hm]
      simpa [operation, hp, hm, Function.comp_def, Value.map, Point.map] using
        Value.term_heq_eq rfl (heq_of_eq (f.identity p.family p.term p.term))
          (f.reflexivity p.family p.term)
  | path =>
    cases hp : point M.toStructuralModel (args 0) (args 1) with
    | none => simp [operation, hp] at h
    | some p =>
      have hm := point_map f hp
      simp only [operation, Function.comp_apply, hp, hm]
      simpa [operation, hp, hm, Function.comp_def, Value.map, Point.map] using
        congrArg Value.context (f.pathContext p.family p.term)
  | root =>
    cases hp : point M.toStructuralModel (args 0) (args 1) with
    | none => simp [operation, hp] at h
    | some p =>
      have hm := point_map f hp
      simp only [operation, Function.comp_apply, hp, hm]
      simpa [operation, hp, hm, Function.comp_def, Value.map, Point.map] using
        Value.substitution_heq_eq (f.pathContext p.family p.term) rfl (f.rootSub p.family p.term)
  | telNil =>
    cases h0 : args 0 <;> simp [operation, h0] at h ⊢
    rfl
  | telCons =>
    cases h0 : args 0 <;> simp only [operation, h0] at h
    all_goals try contradiction
    rename_i Γ A
    cases ht : Value.telescopeAt (M.extend Γ A) (args 1) with
    | none => simp [ht] at h
    | some T =>
      rcases T with ⟨n, T⟩
      have ht' := Value.telescopeAt_some ht
      have hm := Value.telescope_heq_eq (f.extend A)
        (show HEq (f.telescope T)
          (cast (congrArg (fun Ξ => Telescope N.toStructuralModel Ξ n) (f.extend A)) (f.telescope T)) from
          (cast_heq _ _).symm)
      simp only [operation, Function.comp_apply, h0, ht', Value.map]
      rw [hm]
      simp [StructuralMap.telescope]
  | total =>
    cases h0 : args 0 <;> simp only [operation, h0] at h
    all_goals try contradiction
    rename_i Γ n T
    simpa [operation, h0, Function.comp_def, Value.map] using
      congrArg Value.context (f.telescope_total T)
  | projection =>
    cases h0 : args 0 <;> simp only [operation, h0] at h
    all_goals try contradiction
    rename_i Γ n T
    simpa [operation, h0, Function.comp_def, Value.map] using
      Value.substitution_heq_eq rfl (f.telescope_total T) (f.telescope_projection T)
  | pullback =>
    cases h1 : args 1 <;> simp only [operation, h1] at h
    all_goals try contradiction
    rename_i Δ Γ σ
    cases ht : Value.telescopeAt Γ (args 0) with
    | none => simp [ht] at h
    | some T =>
      rcases T with ⟨n, T⟩
      have ht' := Value.telescopeAt_some ht
      simpa [operation, h1, ht', Function.comp_def, Value.map] using
        congrArg (Value.telescope (f.context Δ) n) (f.telescope_pullback T σ)
  | tailMap =>
    cases h1 : args 1 <;> simp only [operation, h1] at h
    all_goals try contradiction
    rename_i Δ Γ σ
    cases ht : Value.telescopeAt Γ (args 0) with
    | none => simp [ht] at h
    | some T =>
      rcases T with ⟨n, T⟩
      have ht' := Value.telescopeAt_some ht
      simpa [operation, h1, ht', Function.comp_def, Value.map] using
        Value.substitution_heq_eq (f.telescope_total T) (pullback_total f T σ) (f.telescope_liftSub T σ)
  | rootTail =>
    cases hp : tail M.toStructuralModel (args 0) (args 1) (args 2) with
    | none => simp [operation, hp] at h
    | some p =>
      have hm := tail_map f hp
      simp only [operation, Function.comp_apply, hp, hm]
      simpa [operation, hp, hm, Function.comp_def, Value.map, Tail.map, Point.map] using
        Value.substitution_heq_eq (f.pathTelescope_total p.family p.term p.telescope)
          (f.rootTelescope_total p.family p.term p.telescope) (f.rootTail p.family p.term p.telescope)
  | pathSub =>
    cases hp : point M.toStructuralModel (args 0) (args 1) with
    | none => simp [operation, hp] at h
    | some p =>
      cases h2 : args 2 <;> simp only [operation, hp, h2] at h
      all_goals try contradiction
      rename_i Δ Γ σ
      cases hs : Value.substitutionAt Δ p.context (args 2) with
      | none => simp [h2] at hs; simp [hs] at h
      | some τ =>
        have hs' := Value.substitutionAt_some hs
        have hm := point_map f hp
        simp only [operation, Function.comp_apply, hp, hm]
        simpa [operation, hp, hm, hs', Function.comp_def, Value.map, Point.map] using
          Value.substitution_heq_eq (f.pathContext p.family p.term)
            (path_sub_context f p.family p.term τ) (f.pathSub p.family p.term τ)
  | pathTail =>
    cases hp : tail M.toStructuralModel (args 0) (args 1) (args 2) with
    | none => simp [operation, hp] at h
    | some p =>
      cases h3 : args 3 <;> simp only [operation, hp, h3] at h
      all_goals try contradiction
      rename_i Δ Γ σ
      cases hs : Value.substitutionAt Δ p.context (args 3) with
      | none => simp [h3] at hs; simp [hs] at h
      | some τ =>
        have hs' := Value.substitutionAt_some hs
        have hm := tail_map f hp
        simp only [operation, Function.comp_apply, hp, hm]
        simpa [operation, hp, hm, hs', Function.comp_def, Value.map, Tail.map, Point.map] using
          Value.telescope_heq_eq (path_sub_context f p.family p.term τ)
            (f.pathTail p.family p.term p.telescope τ)
  | pathTailMap =>
    cases hp : tail M.toStructuralModel (args 0) (args 1) (args 2) with
    | none => simp [operation, hp] at h
    | some p =>
      cases h3 : args 3 <;> simp only [operation, hp, h3] at h
      all_goals try contradiction
      rename_i Δ Γ σ
      cases hs : Value.substitutionAt Δ p.context (args 3) with
      | none => simp [h3] at hs; simp [hs] at h
      | some τ =>
        have hs' := Value.substitutionAt_some hs
        have hm := tail_map f hp
        simp only [operation, Function.comp_apply, hp, hm]
        simpa [operation, hp, hm, hs', Function.comp_def, Value.map, Tail.map, Point.map] using
          Value.substitution_heq_eq (f.pathTelescope_total p.family p.term p.telescope)
            (path_tail_total f p.family p.term p.telescope τ) (f.pathTailMap p.family p.term p.telescope τ)
  | branchMap =>
    cases hp : tail M.toStructuralModel (args 0) (args 1) (args 2) with
    | none => simp [operation, hp] at h
    | some p =>
      cases h3 : args 3 <;> simp only [operation, hp, h3] at h
      all_goals try contradiction
      rename_i Δ Γ σ
      cases hs : Value.substitutionAt Δ p.context (args 3) with
      | none => simp [h3] at hs; simp [hs] at h
      | some τ =>
        have hs' := Value.substitutionAt_some hs
        have hm := tail_map f hp
        simp only [operation, Function.comp_apply, hp, hm]
        simpa [operation, hp, hm, hs', Function.comp_def, Value.map, Tail.map, Point.map] using
          Value.substitution_heq_eq (f.rootTelescope_total p.family p.term p.telescope)
            (f.reindexedRootTelescope_total p.family p.term p.telescope τ)
            (f.branchMap p.family p.term p.telescope τ)
  | reindexBranch =>
    cases hp : problem M.toStructuralModel (args 0) (args 1) (args 2) (args 4) (args 5) with
    | none => simp [operation, hp] at h
    | some p =>
      cases h3 : args 3 <;> simp only [operation, hp, h3] at h
      all_goals try contradiction
      rename_i Δ Γ σ
      cases hs : Value.substitutionAt Δ p.context (args 3) with
      | none => simp [h3] at hs; simp [hs] at h
      | some τ =>
        have hs' := Value.substitutionAt_some hs
        have hm := problem_map f hp
        simp only [operation, Function.comp_apply, hp, hm]
        simpa [operation, hp, hm, hs', Function.comp_def, Value.map, Problem.map, Tail.map, Point.map] using
          Value.term_heq_eq (f.reindexedRootTelescope_total p.family p.term p.telescope τ)
            (reindex_branch_type f p.family p.term p.telescope τ p.motive)
            (f.reindexBranch p.family p.term p.telescope τ p.motive p.branch)
  | j =>
    cases hp : problem M.toStructuralModel (args 0) (args 1) (args 2) (args 3) (args 4) with
    | none => simp [operation, hp] at h
    | some p =>
      have hm := problem_map f hp
      simp only [operation, Function.comp_apply, hp, hm]
      simpa [operation, hp, hm, Function.comp_def, Value.map, Problem.map, Tail.map, Point.map] using
        Value.term_heq_eq (f.pathTelescope_total p.family p.term p.telescope)
          (show HEq (f.family p.motive) (f.jMotive p.family p.term p.telescope p.motive) from
            (cast_heq _ _).symm)
          (F.mapJ p.family p.term p.telescope p.motive p.branch)

/-- The combined structural/contextual interpreter is strict in failure. -/
noncomputable def partialAlgebra (M : Model.{u}) : PartialAlgebra signature where
  toAlgebra := algebra M
  invalid := .invalid
  strict op args h := by
    cases op with
    | inl op => exact (DependentJudgments.partialAlgebra M.toStructuralModel).strict op args h
    | inr op => exact operands_defined M op args h

theorem predicate_map (F : StructuralMap M N) (p : Predicate)
    (args : Fin 2 → Value M) (h : predicate M p args) :
    predicate N p (Value.map F ∘ args) := by
  cases p with
  | telescope n =>
    rcases h with ⟨Γ, T, hΓ, hT⟩
    exact ⟨F.context Γ, F.telescope T, by simp [hΓ, Value.map], by simp [hT, Value.map]⟩

/-- Model maps preserve all defined contextual operations and positive guards. -/
noncomputable def partialHom {M : Model.{u}} {N : Model.{v}} (F : ModelMap M N) :
    PartialHom (partialAlgebra M) (partialAlgebra N) where
  map := Value.map F.toStructuralMap
  operation op args h := by
    cases op with
    | inl op => exact (DependentJudgments.partialHom F.toStructuralMap).operation op args h
    | inr op => exact operation_map F op args h
  defined := Value.map_defined F.toStructuralMap
  predicate p args h := by
    cases p with
    | inl p => exact DependentJudgments.predicate_map F.toStructuralMap p args h
    | inr p => exact predicate_map F.toStructuralMap p args h

/-- Every defined source recipe commutes with a contextual model map. -/
theorem interpret_map {M : Model.{u}} {N : Model.{v}} (F : ModelMap M N)
    {V : Type} (e : Expression V) (ρ : V → Value M.toStructuralModel)
    (h : e.eval (algebra M) ρ ≠ .invalid) :
    Value.map F.toStructuralMap (e.eval (algebra M) ρ) =
      e.eval (algebra N) (Value.map F.toStructuralMap ∘ ρ) :=
  (partialHom F).eval e ρ h

/-- The full J application is a defined recipe, with its actual motive and
branch, so the generic preservation theorem applies for every finite tail. -/
theorem j_expression_map {M : Model.{u}} {N : Model.{v}} (F : ModelMap M N)
    {Γ n} (A : M.Family Γ) (x : M.Section Γ A)
    (T : Telescope M.toStructuralModel (M.toStructuralModel.pathContext A x) n)
    (C : M.Family T.total)
    (d : M.Section (Telescope.pullback M.toStructuralModel T (M.toStructuralModel.rootSub A x)).total
      (M.subTy C (M.toStructuralModel.rootTail A x T))) :
    let ρ : Fin 5 → Value M.toStructuralModel :=
      ![.family Γ A, .term Γ A x, .telescope (M.toStructuralModel.pathContext A x) n T,
        .family T.total C,
        .term (Telescope.pullback M.toStructuralModel T (M.toStructuralModel.rootSub A x)).total
          (M.subTy C (M.toStructuralModel.rootTail A x T)) d]
    Value.map F.toStructuralMap (.term T.total C (M.j A x T C d)) =
      (j (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)).eval (algebra N)
        (Value.map F.toStructuralMap ∘ ρ) := by
  dsimp only
  let ρ : Fin 5 → Value M.toStructuralModel :=
      ![.family Γ A, .term Γ A x, .telescope (M.toStructuralModel.pathContext A x) n T,
        .family T.total C,
        .term (Telescope.pullback M.toStructuralModel T (M.toStructuralModel.rootSub A x)).total
          (M.subTy C (M.toStructuralModel.rootTail A x T)) d]
  let e : Expression (Fin 5) := j (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
  have he : e.eval (algebra M) ρ = .term T.total C (M.j A x T C d) := by
    simp [e, ρ, Term.eval, algebra, operation]
  change Value.map F.toStructuralMap (.term T.total C (M.j A x T C d)) =
    e.eval (algebra N) (Value.map F.toStructuralMap ∘ ρ)
  rw [← he]
  apply interpret_map F
  rw [he]
  intro h
  cases h

end Contextual
end SquareKit.Internal.DependentJudgments
