import SquareKit.Internal.DependentJudgments.Comprehension
import SquareKit.GuardedTheory.Extension

/-! The contextual identity/J signature extends the guarded comprehension
language. Semantic parsing is separate from source admissibility: no model
object appears in a source expression or judgment index. -/

namespace SquareKit.Internal.DependentJudgments.Contextual
set_option backward.isDefEq.respectTransparency false
open GuardedTheory PathTransport.Typed
open StructuralModel
universe u

inductive Operation where
  | identity | reflexivity | path | root | telNil | telCons | total | projection
  | pullback | tailMap | rootTail | pathSub | pathTail | pathTailMap | branchMap
  | reindexBranch | j
  deriving DecidableEq

abbrev Operation.arity : Operation → Nat
  | .telNil | .total | .projection => 1
  | .identity | .rootTail | .pathSub => 3
  | .pathTail | .pathTailMap | .branchMap => 4
  | .j => 5
  | .reindexBranch => 6
  | _ => 2

inductive Predicate where
  | telescope (length : Nat)
  deriving DecidableEq

def extraSignature : Signature where
  Operation := Operation
  arity := Operation.arity
  Predicate := Predicate
  arguments := fun _ => 2

abbrev signature := DependentJudgments.signature.sum extraSignature
abbrev Expression (V : Type) := Term signature V
abbrev Judgment (V : Type) := Atom signature V

/-- A parser result contains actual dependent inputs, including their types. -/
structure Point (M : StructuralModel.{u}) where
  context : M.Context
  family : M.Family context
  term : M.Section context family

noncomputable def point (M : StructuralModel.{u}) (a x : Value M) : Option (Point M) :=
  match a with
  | .family Γ A => (x.termAt Γ A).map (fun t => ⟨Γ, A, t⟩)
  | _ => none

@[simp] theorem point_values (M : StructuralModel.{u}) (Γ : M.Context)
    (A : M.Family Γ) (x : M.Section Γ A) :
    point M (.family Γ A) (.term Γ A x) = some ⟨Γ, A, x⟩ := by simp [point]

structure Tail (M : StructuralModel.{u}) extends Point M where
  length : Nat
  telescope : Telescope M (M.pathContext family term) length

noncomputable def tail (M : StructuralModel.{u}) (a x t : Value M) : Option (Tail M) := do
  let p ← point M a x
  let ⟨n, T⟩ ← t.telescopeAt (M.pathContext p.family p.term)
  pure ⟨p, n, T⟩

@[simp] theorem tail_values (M : StructuralModel.{u}) (Γ : M.Context)
    (A : M.Family Γ) (x : M.Section Γ A) (n : Nat)
    (T : Telescope M (M.pathContext A x) n) :
    tail M (.family Γ A) (.term Γ A x) (.telescope (M.pathContext A x) n T) =
      some ⟨⟨Γ, A, x⟩, n, T⟩ := by simp [tail]

structure Problem (M : StructuralModel.{u}) extends Tail M where
  motive : M.Family telescope.total
  branch : M.Section (Telescope.pullback M telescope (M.rootSub family term)).total
    (M.subTy motive (M.rootTail family term telescope))

noncomputable def problem (M : StructuralModel.{u}) (a x t d b : Value M) :
    Option (Problem M) := do
  let p ← tail M a x t
  let D ← d.familyAt p.telescope.total
  let b ← b.termAt (Telescope.pullback M p.telescope (M.rootSub p.family p.term)).total
    (M.subTy D (M.rootTail p.family p.term p.telescope))
  pure ⟨p, D, b⟩

@[simp] theorem problem_values (M : StructuralModel.{u}) (Γ : M.Context)
    (A : M.Family Γ) (x : M.Section Γ A) (n : Nat)
    (T : Telescope M (M.pathContext A x) n) (D : M.Family T.total)
    (d : M.Section (Telescope.pullback M T (M.rootSub A x)).total (M.subTy D (M.rootTail A x T))) :
    problem M (.family Γ A) (.term Γ A x) (.telescope (M.pathContext A x) n T)
      (.family T.total D)
      (.term (Telescope.pullback M T (M.rootSub A x)).total (M.subTy D (M.rootTail A x T)) d) =
      some ⟨⟨⟨Γ, A, x⟩, n, T⟩, D, d⟩ := by simp [problem]

noncomputable def operation (M : PathTransport.Typed.Model.{u}) :
    (op : Operation) → (Fin op.arity → Value M.toStructuralModel) → Value M.toStructuralModel
  | .identity, args => Id.run do
    let some p := point M.toStructuralModel (args 0) (args 1) | return .invalid
    let some y := (args 2).termAt p.context p.family | return .invalid
    return .family p.context (M.identity p.family p.term y)
  | .reflexivity, args => Id.run do
    let some p := point M.toStructuralModel (args 0) (args 1) | return .invalid
    return .term p.context (M.identity p.family p.term p.term) (M.reflexivity p.family p.term)
  | .path, args => Id.run do
    let some p := point M.toStructuralModel (args 0) (args 1) | return .invalid
    return .context (M.toStructuralModel.pathContext p.family p.term)
  | .root, args => Id.run do
    let some p := point M.toStructuralModel (args 0) (args 1) | return .invalid
    return .substitution p.context (M.toStructuralModel.pathContext p.family p.term) (M.toStructuralModel.rootSub p.family p.term)
  | .telNil, args => Id.run do
    let .context Γ := args 0 | return .invalid
    return .telescope Γ 0 .nil
  | .telCons, args => Id.run do
    let .family Γ A := args 0 | return .invalid
    let some ⟨n, T⟩ := (args 1).telescopeAt (M.extend Γ A) | return .invalid
    return .telescope Γ (n + 1) (.cons A T)
  | .total, args => Id.run do
    let .telescope _ _ T := args 0 | return .invalid
    return .context T.total
  | .projection, args => Id.run do
    let .telescope Γ _ T := args 0 | return .invalid
    return .substitution T.total Γ T.projection
  | .pullback, args => Id.run do
    let .substitution Δ Γ σ := args 1 | return .invalid
    let some ⟨n, T⟩ := (args 0).telescopeAt Γ | return .invalid
    return .telescope Δ n (Telescope.pullback M.toStructuralModel T σ)
  | .tailMap, args => Id.run do
    let .substitution _Δ Γ σ := args 1 | return .invalid
    let some ⟨_, T⟩ := (args 0).telescopeAt Γ | return .invalid
    return .substitution (Telescope.pullback M.toStructuralModel T σ).total T.total (Telescope.liftSub M.toStructuralModel T σ)
  | .rootTail, args => Id.run do
    let some p := tail M.toStructuralModel (args 0) (args 1) (args 2) | return .invalid
    return .substitution (Telescope.pullback M.toStructuralModel p.telescope (M.toStructuralModel.rootSub p.family p.term)).total
      p.telescope.total (M.toStructuralModel.rootTail p.family p.term p.telescope)
  | .pathSub, args => Id.run do
    let some p := point M.toStructuralModel (args 0) (args 1) | return .invalid
    let .substitution Δ _ _ := args 2 | return .invalid
    let some σ := (args 2).substitutionAt Δ p.context | return .invalid
    return .substitution (M.toStructuralModel.pathContext (M.subTy p.family σ) (M.subTm p.term σ))
      (M.toStructuralModel.pathContext p.family p.term) (M.toStructuralModel.pathSub p.family p.term σ)
  | .pathTail, args => Id.run do
    let some p := tail M.toStructuralModel (args 0) (args 1) (args 2) | return .invalid
    let .substitution Δ _ _ := args 3 | return .invalid
    let some σ := (args 3).substitutionAt Δ p.context | return .invalid
    return .telescope (M.toStructuralModel.pathContext (M.subTy p.family σ) (M.subTm p.term σ)) p.length
      (M.toStructuralModel.pathTail p.family p.term p.telescope σ)
  | .pathTailMap, args => Id.run do
    let some p := tail M.toStructuralModel (args 0) (args 1) (args 2) | return .invalid
    let .substitution Δ _ _ := args 3 | return .invalid
    let some σ := (args 3).substitutionAt Δ p.context | return .invalid
    return .substitution (M.toStructuralModel.pathTail p.family p.term p.telescope σ).total p.telescope.total
      (M.toStructuralModel.pathTailMap p.family p.term p.telescope σ)
  | .branchMap, args => Id.run do
    let some p := tail M.toStructuralModel (args 0) (args 1) (args 2) | return .invalid
    let .substitution Δ _ _ := args 3 | return .invalid
    let some σ := (args 3).substitutionAt Δ p.context | return .invalid
    return .substitution
      (Telescope.pullback M.toStructuralModel (M.toStructuralModel.pathTail p.family p.term p.telescope σ)
        (M.toStructuralModel.rootSub (M.subTy p.family σ) (M.subTm p.term σ))).total
      (Telescope.pullback M.toStructuralModel p.telescope (M.toStructuralModel.rootSub p.family p.term)).total
      (M.toStructuralModel.branchMap p.family p.term p.telescope σ)
  | .reindexBranch, args => Id.run do
    let some p := problem M.toStructuralModel (args 0) (args 1) (args 2) (args 4) (args 5) | return .invalid
    let .substitution Δ _ _ := args 3 | return .invalid
    let some σ := (args 3).substitutionAt Δ p.context | return .invalid
    return .term
      (Telescope.pullback M.toStructuralModel (M.toStructuralModel.pathTail p.family p.term p.telescope σ)
        (M.toStructuralModel.rootSub (M.subTy p.family σ) (M.subTm p.term σ))).total
      (M.subTy (M.subTy p.motive (M.toStructuralModel.pathTailMap p.family p.term p.telescope σ))
        (M.toStructuralModel.rootTail (M.subTy p.family σ) (M.subTm p.term σ)
          (M.toStructuralModel.pathTail p.family p.term p.telescope σ)))
      (M.toStructuralModel.reindexBranch p.family p.term p.telescope σ p.motive p.branch)
  | .j, args => Id.run do
    let some p := problem M.toStructuralModel (args 0) (args 1) (args 2) (args 3) (args 4) | return .invalid
    return .term p.telescope.total p.motive (M.j p.family p.term p.telescope p.motive p.branch)

def predicate (M : StructuralModel.{u}) (p : Predicate) (args : Fin 2 → Value M) : Prop :=
  match p with
  | .telescope n => ∃ (Γ : M.Context) (T : Telescope M Γ n),
      args 0 = .context Γ ∧ args 1 = .telescope Γ n T

noncomputable def algebra (M : PathTransport.Typed.Model.{u}) : Algebra signature where
  Carrier := Value M.toStructuralModel
  operation
    | .inl op => DependentJudgments.operation M.toStructuralModel op
    | .inr op => operation M op
  predicate
    | .inl p => DependentJudgments.predicate M.toStructuralModel p
    | .inr p => predicate M.toStructuralModel p


variable {V : Type}

abbrev context (Γ : Expression V) : Judgment V := .pred (.inl .context) ![Γ]
abbrev family (Γ A : Expression V) : Judgment V := .pred (.inl .family) ![Γ, A]
abbrev term (Γ A t : Expression V) : Judgment V := .pred (.inl .term) ![Γ, A, t]
abbrev substitution (Δ Γ σ : Expression V) : Judgment V := .pred (.inl .substitution) ![Δ, Γ, σ]
abbrev telescope (n : Nat) (Γ T : Expression V) : Judgment V := .pred (.inr (.telescope n)) ![Γ, T]
abbrev empty : Expression V := .app (.inl .empty) Fin.elim0
abbrev extend (Γ A : Expression V) : Expression V := .app (.inl .extend) ![Γ, A]
abbrev identitySub (Γ : Expression V) : Expression V := .app (.inl .id) ![Γ]
abbrev comp (σ τ : Expression V) : Expression V := .app (.inl .comp) ![σ, τ]
abbrev subTy (A σ : Expression V) : Expression V := .app (.inl .subTy) ![A, σ]
abbrev subTm (t σ : Expression V) : Expression V := .app (.inl .subTm) ![t, σ]
abbrev weaken (Γ A : Expression V) : Expression V := .app (.inl .weaken) ![Γ, A]
abbrev generic (Γ A : Expression V) : Expression V := .app (.inl .generic) ![Γ, A]
abbrev pair (A σ t : Expression V) : Expression V := .app (.inl .pair) ![A, σ, t]
abbrev identity (A x y : Expression V) : Expression V := .app (.inr .identity) ![A, x, y]
abbrev reflexivity (A x : Expression V) : Expression V := .app (.inr .reflexivity) ![A, x]
abbrev path (A x : Expression V) : Expression V := .app (.inr .path) ![A, x]
abbrev root (A x : Expression V) : Expression V := .app (.inr .root) ![A, x]
abbrev telNil (Γ : Expression V) : Expression V := .app (.inr .telNil) ![Γ]
abbrev telCons (A T : Expression V) : Expression V := .app (.inr .telCons) ![A, T]
abbrev total (T : Expression V) : Expression V := .app (.inr .total) ![T]
abbrev projection (T : Expression V) : Expression V := .app (.inr .projection) ![T]
abbrev pullback (T σ : Expression V) : Expression V := .app (.inr .pullback) ![T, σ]
abbrev tailMap (T σ : Expression V) : Expression V := .app (.inr .tailMap) ![T, σ]
abbrev rootTail (A x T : Expression V) : Expression V := .app (.inr .rootTail) ![A, x, T]
abbrev pathSub (A x σ : Expression V) : Expression V := .app (.inr .pathSub) ![A, x, σ]
abbrev pathTail (A x T σ : Expression V) : Expression V := .app (.inr .pathTail) ![A, x, T, σ]
abbrev pathTailMap (A x T σ : Expression V) : Expression V := .app (.inr .pathTailMap) ![A, x, T, σ]
abbrev branchMap (A x T σ : Expression V) : Expression V := .app (.inr .branchMap) ![A, x, T, σ]
abbrev reindexBranch (A x T σ D d : Expression V) : Expression V :=
  .app (.inr .reindexBranch) ![A, x, T, σ, D, d]
abbrev j (A x T D d : Expression V) : Expression V := .app (.inr .j) ![A, x, T, D, d]

abbrev pointSchema (out : Judgment (Fin 3)) : Rule signature where
  parameterCount := 3
  hypotheses := 1
  premise := ![term (.var 0) (.var 1) (.var 2)]
  conclusion := out

theorem pointSchema_valid (M : PathTransport.Typed.Model.{u}) (out : Judgment (Fin 3))
    (h : ∀ Γ A x, out.eval (algebra M) ![.context Γ, .family Γ A, .term Γ A x]) :
    Satisfies (algebra M) (pointSchema out) := by
  intro ρ hs
  rcases hs 0 with ⟨Γ, A, x, hΓ, hA, hx⟩
  have e : ρ = ![Value.context Γ, .family Γ A, .term Γ A x] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hA | exact hx
  subst ρ
  exact h Γ A x

abbrev reflexivityRule := pointSchema
  (term (.var 0) (identity (.var 1) (.var 2) (.var 2)) (reflexivity (.var 1) (.var 2)))
abbrev pathRule := pointSchema (context (path (.var 1) (.var 2)))
abbrev rootRule := pointSchema
  (substitution (.var 0) (path (.var 1) (.var 2)) (root (.var 1) (.var 2)))

theorem reflexivity_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) reflexivityRule := by
  apply pointSchema_valid
  intro Γ A x
  refine ⟨Γ, M.identity A x x, M.reflexivity A x, rfl, ?_, ?_⟩ <;>
    simp [Term.eval, algebra, operation]

theorem path_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) pathRule := by
  apply pointSchema_valid
  intro Γ A x
  exact ⟨M.toStructuralModel.pathContext A x, by simp [Term.eval, algebra, operation]⟩

theorem root_valid (M : PathTransport.Typed.Model.{u}) : Satisfies (algebra M) rootRule := by
  apply pointSchema_valid
  intro Γ A x
  refine ⟨Γ, M.toStructuralModel.pathContext A x, M.toStructuralModel.rootSub A x, rfl, ?_, ?_⟩ <;>
    simp [Term.eval, algebra, operation]

abbrev jSchema (n : Nat) (out : Judgment (Fin 6)) : Rule signature where
  parameterCount := 6
  hypotheses := 4
  premise := ![term (.var 0) (.var 1) (.var 2),
    telescope n (path (.var 1) (.var 2)) (.var 3),
    family (total (.var 3)) (.var 4),
    term (total (pullback (.var 3) (root (.var 1) (.var 2))))
      (subTy (.var 4) (rootTail (.var 1) (.var 2) (.var 3))) (.var 5)]
  conclusion := out

abbrev jRule (n : Nat) := jSchema n
  (term (total (.var 3)) (.var 4) (j (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)))
abbrev jBetaRule (n : Nat) := jSchema n
  (.eq (subTm (j (.var 1) (.var 2) (.var 3) (.var 4) (.var 5))
    (rootTail (.var 1) (.var 2) (.var 3))) (.var 5))

def problemEnvironment (M : StructuralModel.{u}) (p : Problem M) : Fin 6 → Value M :=
  ![.context p.context, .family p.context p.family, .term p.context p.family p.term,
    .telescope (M.pathContext p.family p.term) p.length p.telescope,
    .family p.telescope.total p.motive,
    .term (Telescope.pullback M p.telescope (M.rootSub p.family p.term)).total
      (M.subTy p.motive (M.rootTail p.family p.term p.telescope)) p.branch]

theorem jSchema_inputs (M : PathTransport.Typed.Model.{u}) (n : Nat)
    (out : Judgment (Fin 6)) (ρ : Fin 6 → Value M.toStructuralModel)
    (h : ∀ i, ((jSchema n out).premise i).eval (algebra M) ρ) :
    ∃ p : Problem M.toStructuralModel, p.length = n ∧ ρ = problemEnvironment M.toStructuralModel p := by
  rcases h 0 with ⟨Γ, A, x, hΓ, hA, hx⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .family Γ A at hA
  change ρ 2 = .term Γ A x at hx
  have hp : (path (.var 1) (.var 2)).eval (algebra M) ρ =
      .context (M.toStructuralModel.pathContext A x) := by
    simp [Term.eval, algebra, operation, hA, hx]
  have hT := h 1
  change ∃ (Γ' : M.Context) (T : Telescope M.toStructuralModel Γ' n),
    (path (.var 1) (.var 2)).eval (algebra M) ρ = .context Γ' ∧
      ρ 3 = .telescope Γ' n T at hT
  rw [hp] at hT
  rcases hT with ⟨Γ', T, hΓ', hT⟩
  have eΓ : M.toStructuralModel.pathContext A x = Γ' := Value.context.inj hΓ'
  subst Γ'
  have ht : (total (.var 3)).eval (algebra M) ρ = .context T.total := by
    simp [Term.eval, algebra, operation, hT]
  have hD := h 2
  change ∃ (Γ' : M.Context) (D : M.Family Γ'),
    (total (.var 3)).eval (algebra M) ρ = .context Γ' ∧ ρ 4 = .family Γ' D at hD
  rw [ht] at hD
  rcases hD with ⟨Γ', D, hΓ', hD⟩
  have eΓ : T.total = Γ' := Value.context.inj hΓ'
  subst Γ'
  have hr : (total (pullback (.var 3) (root (.var 1) (.var 2)))).eval (algebra M) ρ =
      .context (Telescope.pullback M.toStructuralModel T (M.toStructuralModel.rootSub A x)).total := by
    simp [Term.eval, algebra, operation, hA, hx, hT]
  have hb : (subTy (.var 4) (rootTail (.var 1) (.var 2) (.var 3))).eval (algebra M) ρ =
      .family (Telescope.pullback M.toStructuralModel T (M.toStructuralModel.rootSub A x)).total
        (M.subTy D (M.toStructuralModel.rootTail A x T)) := by
    simp [Term.eval, algebra, operation, DependentJudgments.operation, hA, hx, hT, hD]
  have hd := h 3
  change ∃ (Γ' : M.Context) (D' : M.Family Γ') (d : M.Section Γ' D'),
    (total (pullback (.var 3) (root (.var 1) (.var 2)))).eval (algebra M) ρ = .context Γ' ∧
    (subTy (.var 4) (rootTail (.var 1) (.var 2) (.var 3))).eval (algebra M) ρ = .family Γ' D' ∧
    ρ 5 = .term Γ' D' d at hd
  rw [hr, hb] at hd
  rcases hd with ⟨Γ', D', d, hΓ', hD', hd⟩
  have eΓ := Value.context.inj hΓ'
  subst Γ'
  have eD := eq_of_heq (Value.family.inj hD').2
  subst D'
  refine ⟨⟨⟨⟨Γ, A, x⟩, n, T⟩, D, d⟩, rfl, ?_⟩
  funext i
  fin_cases i <;> first | exact hΓ | exact hA | exact hx | exact hT | exact hD | exact hd

theorem jSchema_valid (M : PathTransport.Typed.Model.{u}) (n : Nat)
    (out : Judgment (Fin 6))
    (valid : ∀ p : Problem M.toStructuralModel,
      out.eval (algebra M) (problemEnvironment M.toStructuralModel p)) :
    Satisfies (algebra M) (jSchema n out) := by
  intro ρ h
  rcases jSchema_inputs M n out ρ h with ⟨p, _, rfl⟩
  exact valid p

theorem j_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (jRule n) := by
  apply jSchema_valid
  intro p
  rcases p with ⟨⟨⟨Γ, A, x⟩, k, T⟩, D, d⟩
  refine ⟨T.total, D, M.j A x T D d, ?_, rfl, ?_⟩ <;>
    simp [Term.eval, algebra, operation, problemEnvironment]

theorem jBeta_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (jBetaRule n) := by
  apply jSchema_valid
  intro p
  rcases p with ⟨⟨⟨Γ, A, x⟩, k, T⟩, D, d⟩
  change (subTm (j (.var 1) (.var 2) (.var 3) (.var 4) (.var 5))
    (rootTail (.var 1) (.var 2) (.var 3))).eval (algebra M) _ = _
  simpa [Term.eval, algebra, operation, problemEnvironment, DependentJudgments.operation]
    using Value.term_eq (M := M.toStructuralModel) rfl (M.j_beta A x T D d)


abbrev jSubSchema (n : Nat) (out : Judgment (Fin 8)) : Rule signature where
  parameterCount := 8
  hypotheses := 5
  premise := ![term (.var 0) (.var 1) (.var 2),
    telescope n (path (.var 1) (.var 2)) (.var 3),
    family (total (.var 3)) (.var 4),
    term (total (pullback (.var 3) (root (.var 1) (.var 2))))
      (subTy (.var 4) (rootTail (.var 1) (.var 2) (.var 3))) (.var 5),
    substitution (.var 6) (.var 0) (.var 7)]
  conclusion := out

abbrev jSubRule (n : Nat) := jSubSchema n
  (.eq (subTm (j (.var 1) (.var 2) (.var 3) (.var 4) (.var 5))
    (pathTailMap (.var 1) (.var 2) (.var 3) (.var 7)))
    (j (subTy (.var 1) (.var 7)) (subTm (.var 2) (.var 7))
      (pathTail (.var 1) (.var 2) (.var 3) (.var 7))
      (subTy (.var 4) (pathTailMap (.var 1) (.var 2) (.var 3) (.var 7)))
      (reindexBranch (.var 1) (.var 2) (.var 3) (.var 7) (.var 4) (.var 5))))

def substitutedEnvironment (M : StructuralModel.{u}) (p : Problem M)
    (Δ : M.Context) (σ : M.Substitution Δ p.context) : Fin 8 → Value M :=
  ![.context p.context, .family p.context p.family, .term p.context p.family p.term,
    .telescope (M.pathContext p.family p.term) p.length p.telescope,
    .family p.telescope.total p.motive,
    .term (Telescope.pullback M p.telescope (M.rootSub p.family p.term)).total
      (M.subTy p.motive (M.rootTail p.family p.term p.telescope)) p.branch,
    .context Δ, .substitution Δ p.context σ]

theorem jSubSchema_valid (M : PathTransport.Typed.Model.{u}) (n : Nat)
    (out : Judgment (Fin 8))
    (valid : ∀ (p : Problem M.toStructuralModel) (Δ : M.Context) (σ : M.Substitution Δ p.context),
      out.eval (algebra M) (substitutedEnvironment M.toStructuralModel p Δ σ)) :
    Satisfies (algebra M) (jSubSchema n out) := by
  intro ρ h
  let ρ₀ : Fin 6 → Value M.toStructuralModel := fun i => ρ (i.castAdd 2)
  have h₀ : ∀ i, ((jRule n).premise i).eval (algebra M) ρ₀ := by
    intro i
    fin_cases i <;> first | exact h 0 | exact h 1 | exact h 2 | exact h 3
  rcases jSchema_inputs M n _ ρ₀ h₀ with ⟨p, _, hp⟩
  have hΓ := congrFun hp 0
  change ρ 0 = .context p.context at hΓ
  rcases h 4 with ⟨Δ, Γ, σ, hΔ, hΓ', hσ⟩
  change ρ 6 = .context Δ at hΔ
  change ρ 0 = .context Γ at hΓ'
  change ρ 7 = .substitution Δ Γ σ at hσ
  have eΓ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ
  have e : ρ = substitutedEnvironment M.toStructuralModel p Δ σ := by
    funext i
    fin_cases i
    · exact congrFun hp 0
    · exact congrFun hp 1
    · exact congrFun hp 2
    · exact congrFun hp 3
    · exact congrFun hp 4
    · exact congrFun hp 5
    · exact hΔ
    · exact hσ
  subst ρ
  exact valid p Δ σ

theorem jSub_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (jSubRule n) := by
  apply jSubSchema_valid
  intro p Δ σ
  rcases p with ⟨⟨⟨Γ, A, x⟩, k, T⟩, D, d⟩
  change (subTm (j (.var 1) (.var 2) (.var 3) (.var 4) (.var 5))
    (pathTailMap (.var 1) (.var 2) (.var 3) (.var 7))).eval (algebra M) _ = _
  simpa [Term.eval, algebra, operation, substitutedEnvironment, DependentJudgments.operation]
    using Value.term_eq (M := M.toStructuralModel) rfl (M.j_sub A x T D d σ)

end SquareKit.Internal.DependentJudgments.Contextual
