import SquareKit.Internal.DependentJudgments.GeneratedSubstitutions

/-! Explicit finite-telescope equations for comparing conventional dependent
contexts with the guarded presentation. These rules form a separate extension;
this module does not claim their derivability in the original theory. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u

abbrev consSchema (n : Nat) (out : Judgment (Fin 3)) : Rule signature where
  parameterCount := 3
  hypotheses := 2
  premise := ![family (.var 0) (.var 1), telescope n (extend (.var 0) (.var 1)) (.var 2)]
  conclusion := out

abbrev totalConsRule (n : Nat) := consSchema n
  (.eq (total (telCons (.var 1) (.var 2))) (total (.var 2)))

abbrev projectionConsRule (n : Nat) := consSchema n
  (.eq (projection (telCons (.var 1) (.var 2)))
    (comp (weaken (.var 0) (.var 1)) (projection (.var 2))))

theorem consSchema_valid (M : PathTransport.Typed.Model.{u}) (n : Nat)
    (out : Judgment (Fin 3))
    (valid : ∀ Γ A (T : Telescope M.toStructuralModel (M.extend Γ A) n),
      out.eval (algebra M) ![.context Γ, .family Γ A, .telescope (M.extend Γ A) n T]) :
    Satisfies (algebra M) (consSchema n out) := by
  intro ρ h
  rcases h 0 with ⟨Γ, A, hΓ, hA⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 1 = .family Γ A at hA
  have he : (extend (.var 0) (.var 1)).eval (algebra M) ρ = .context (M.extend Γ A) := by
    simp [Term.eval, algebra, DependentJudgments.operation, hΓ, hA]
  rcases h 1 with ⟨Γ', T, hΓ', hT⟩
  change (extend (.var 0) (.var 1)).eval (algebra M) ρ = .context Γ' at hΓ'
  have eΓ := Value.context.inj (he.symm.trans hΓ')
  subst Γ'
  have e : ρ = ![Value.context Γ, .family Γ A, .telescope (M.extend Γ A) n T] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hA | exact hT
  subst ρ
  exact valid Γ A T

theorem totalCons_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (totalConsRule n) := by
  apply consSchema_valid
  intro Γ A T
  simp [Atom.eval, Term.eval, algebra, operation, Telescope.total]

theorem projectionCons_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (projectionConsRule n) := by
  apply consSchema_valid
  intro Γ A T
  simp [Atom.eval, Term.eval, algebra, operation, DependentJudgments.operation,
    Telescope.total, Telescope.projection]


abbrev consSubSchema (n : Nat) (out : Judgment (Fin 5)) : Rule signature where
  parameterCount := 5
  hypotheses := 3
  premise := ![family (.var 0) (.var 2),
    telescope n (extend (.var 0) (.var 2)) (.var 3),
    substitution (.var 1) (.var 0) (.var 4)]
  conclusion := out

abbrev pullbackConsRule (n : Nat) := consSubSchema n
  (.eq (pullback (telCons (.var 2) (.var 3)) (.var 4))
    (telCons (subTy (.var 2) (.var 4))
      (pullback (.var 3) (liftSyntax (.var 1) (.var 2) (.var 4)))))

abbrev tailMapConsRule (n : Nat) := consSubSchema n
  (.eq (tailMap (telCons (.var 2) (.var 3)) (.var 4))
    (tailMap (.var 3) (liftSyntax (.var 1) (.var 2) (.var 4))))

theorem consSubSchema_valid (M : PathTransport.Typed.Model.{u}) (n : Nat)
    (out : Judgment (Fin 5))
    (valid : ∀ Γ Δ A (T : Telescope M.toStructuralModel (M.extend Γ A) n)
      (σ : M.Substitution Δ Γ),
      out.eval (algebra M) ![.context Γ, .context Δ, .family Γ A,
        .telescope (M.extend Γ A) n T, .substitution Δ Γ σ]) :
    Satisfies (algebra M) (consSubSchema n out) := by
  intro ρ h
  rcases h 0 with ⟨Γ, A, hΓ, hA⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 2 = .family Γ A at hA
  have he : (extend (.var 0) (.var 2)).eval (algebra M) ρ = .context (M.extend Γ A) := by
    simp [Term.eval, algebra, DependentJudgments.operation, hΓ, hA]
  rcases h 1 with ⟨Γ', T, hΓ', hT⟩
  change (extend (.var 0) (.var 2)).eval (algebra M) ρ = .context Γ' at hΓ'
  have eΓ := Value.context.inj (he.symm.trans hΓ')
  subst Γ'
  rcases h 2 with ⟨Δ, Γ', σ, hΔ, hΓ', hσ⟩
  change ρ 0 = .context Γ' at hΓ'
  have eΓ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have e : ρ = ![Value.context Γ, .context Δ, .family Γ A,
      .telescope (M.extend Γ A) n T, .substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hA | exact hT | exact hσ
  subst ρ
  exact valid Γ Δ A T σ

theorem pullbackCons_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (pullbackConsRule n) := by
  apply consSubSchema_valid
  intro Γ Δ A T σ
  have hl := liftSyntax_eval M
    (![Value.context Γ, .context Δ, .family Γ A,
      .telescope (M.extend Γ A) n T, .substitution Δ Γ σ])
    (.var 1) (.var 2) (.var 4) Γ Δ A σ rfl rfl rfl
  change Term.eval (algebra M) _ _ = _
  simp only [Term.eval, algebra] at hl
  simp [Term.eval, FinitaryTerm.fold, algebra, operation, DependentJudgments.operation,
    hl, Telescope.pullback, Telescope.reindex]

theorem tailMapCons_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (tailMapConsRule n) := by
  apply consSubSchema_valid
  intro Γ Δ A T σ
  have hl := liftSyntax_eval M
    (![Value.context Γ, .context Δ, .family Γ A,
      .telescope (M.extend Γ A) n T, .substitution Δ Γ σ])
    (.var 1) (.var 2) (.var 4) Γ Δ A σ rfl rfl rfl
  change Term.eval (algebra M) _ _ = _
  simp only [Term.eval, algebra] at hl
  simp [Term.eval, FinitaryTerm.fold, algebra, operation,
    hl, Telescope.pullback, Telescope.reindex, Telescope.liftSub, Telescope.total]

abbrev projectionNilRule := contextSchema
  (.eq (projection (telNil (.var 0))) (identitySub (.var 0)))
abbrev tailMapNilRule := subSchema
  (.eq (tailMap (telNil (.var 0)) (.var 2)) (.var 2))
abbrev rootTailDefRule (n : Nat) := tailSchema n
  (.eq (rootTail (.var 1) (.var 2) (.var 3))
    (tailMap (.var 3) (root (.var 1) (.var 2))))

theorem projectionNil_valid (M : PathTransport.Typed.Model.{u}) :
    Satisfies (algebra M) projectionNilRule := by
  apply contextSchema_valid
  intro Γ
  rfl

theorem tailMapNil_valid (M : PathTransport.Typed.Model.{u}) :
    Satisfies (algebra M) tailMapNilRule := by
  apply subSchema_valid
  intro Γ Δ σ
  simp [Atom.eval, Term.eval, FinitaryTerm.fold, algebra, operation,
    Telescope.liftSub, Telescope.reindex, Telescope.pullback, Telescope.total]

theorem rootTailDef_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (rootTailDefRule n) := by
  apply tailSchema_valid
  intro Γ A x T
  simp [Atom.eval, Term.eval, algebra, operation, StructuralModel.rootTail]

abbrev pathTailDefRule (n : Nat) := tailSubSchema n
  (.eq (pathTail (.var 1) (.var 2) (.var 3) (.var 5))
    (pullback (.var 3) (pathSub (.var 1) (.var 2) (.var 5))))

abbrev pathTailMapDefRule (n : Nat) := tailSubSchema n
  (.eq (pathTailMap (.var 1) (.var 2) (.var 3) (.var 5))
    (tailMap (.var 3) (pathSub (.var 1) (.var 2) (.var 5))))

abbrev branchSquareRule (n : Nat) := tailSubSchema n
  (.eq (comp (pathTailMap (.var 1) (.var 2) (.var 3) (.var 5))
    (rootTail (subTy (.var 1) (.var 5)) (subTm (.var 2) (.var 5))
      (pathTail (.var 1) (.var 2) (.var 3) (.var 5))))
    (comp (rootTail (.var 1) (.var 2) (.var 3))
      (branchMap (.var 1) (.var 2) (.var 3) (.var 5))))

theorem pathTailDef_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (pathTailDefRule n) := by
  apply tailSubSchema_valid
  intro Γ Δ A x T σ
  simp [Atom.eval, Term.eval, algebra, operation, StructuralModel.pathTail]

theorem pathTailMapDef_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (pathTailMapDefRule n) := by
  apply tailSubSchema_valid
  intro Γ Δ A x T σ
  simp [Atom.eval, Term.eval, algebra, operation, StructuralModel.pathTailMap,
    StructuralModel.pathTail]

theorem branchSquare_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (branchSquareRule n) := by
  apply tailSubSchema_valid
  intro Γ Δ A x T σ
  simp [Atom.eval, Term.eval, algebra, operation, DependentJudgments.operation]
  exact M.toStructuralModel.branchMap_square A x T σ

abbrev reindexBranchDefRule (n : Nat) := jSubSchema n
  (.eq (reindexBranch (.var 1) (.var 2) (.var 3) (.var 7) (.var 4) (.var 5))
    (subTm (.var 5) (branchMap (.var 1) (.var 2) (.var 3) (.var 7))))

theorem reindexBranchDef_valid (M : PathTransport.Typed.Model.{u}) (n : Nat) :
    Satisfies (algebra M) (reindexBranchDefRule n) := by
  apply jSubSchema_valid
  intro p Δ σ
  rcases p with ⟨⟨⟨Γ, A, x⟩, k, T⟩, D, d⟩
  change Term.eval (algebra M) _ _ = _
  simp [Term.eval, FinitaryTerm.fold, algebra, operation, DependentJudgments.operation,
    substitutedEnvironment]
  constructor
  · exact M.toStructuralModel.branchMap_type A x T σ D
  · unfold StructuralModel.reindexBranch
    exact cast_heq _ _

inductive Extra where
  | reindexBranchDef (n : Nat)
  | pathTailDef (n : Nat) | pathTailMapDef (n : Nat) | branchSquare (n : Nat)
  | projectionNil | tailMapNil
  | rootTailDef (n : Nat)
  | totalCons (n : Nat)
  | projectionCons (n : Nat)
  | pullbackCons (n : Nat)
  | tailMapCons (n : Nat)

def extraRule : Extra → Rule signature
  | .reindexBranchDef n => reindexBranchDefRule n
  | .pathTailDef n => pathTailDefRule n
  | .pathTailMapDef n => pathTailMapDefRule n
  | .branchSquare n => branchSquareRule n
  | .projectionNil => projectionNilRule
  | .tailMapNil => tailMapNilRule
  | .rootTailDef n => rootTailDefRule n
  | .totalCons n => totalConsRule n
  | .projectionCons n => projectionConsRule n
  | .pullbackCons n => pullbackConsRule n
  | .tailMapCons n => tailMapConsRule n

/-- The original signature and rules are retained; only the displayed
finite-tail computation schemes are added. -/
def theory : Theory signature where
  Axiom := Contextual.theory.Axiom ⊕ Extra
  rule
    | .inl a => Contextual.theory.rule a
    | .inr a => extraRule a

/-- Every existing contextual model validates the added equations. This is
an expansion of these models, not an expansion theorem for all guarded models. -/
noncomputable def model (M : PathTransport.Typed.Model.{u}) : GuardedTheory.Model theory where
  toAlgebra := algebra M
  rules
    | .inr (.reindexBranchDef n) => reindexBranchDef_valid M n
    | .inr (.pathTailDef n) => pathTailDef_valid M n
    | .inr (.pathTailMapDef n) => pathTailMapDef_valid M n
    | .inr (.branchSquare n) => branchSquare_valid M n
    | .inl a => (Contextual.model M).rules a
    | .inr .projectionNil => projectionNil_valid M
    | .inr .tailMapNil => tailMapNil_valid M
    | .inr (.rootTailDef n) => rootTailDef_valid M n
    | .inr (.totalCons n) => totalCons_valid M n
    | .inr (.projectionCons n) => projectionCons_valid M n
    | .inr (.pullbackCons n) => pullbackCons_valid M n
    | .inr (.tailMapCons n) => tailMapCons_valid M n

/-- Forgetting added rules preserves the underlying algebra exactly. -/
def reduct (M : GuardedTheory.Model theory) : GuardedTheory.Model Contextual.theory where
  toAlgebra := M.toAlgebra
  rules a := M.rules (.inl a)

@[simp] theorem model_reduct (M : PathTransport.Typed.Model.{u}) :
    (reduct (model M)).toAlgebra = (Contextual.model M).toAlgebra := rfl

/-- The original calculus embeds syntactically, with unchanged assumptions
and conclusion. No converse is asserted. -/
noncomputable def embed {V : Type} {Ω : List (Judgment V)} {a : Judgment V}
    (d : Derivation Contextual.theory Ω a) : Derivation theory Ω a := by
  induction d with
  | hypothesis h => exact .hypothesis h
  | rule a σ _ ih => exact .rule (T := theory) (Sum.inl a) σ ih
  | reflexive t => exact .reflexive t
  | symmetric _ ih => exact .symmetric ih
  | transitive _ _ ih ih' => exact .transitive ih ih'
  | congruence op _ ih => exact .congruence op ih
  | conversion p _ _ ih hp => exact .conversion p ih hp

/-- Substitute proofs for open assumptions in an original derivation. This
lets the comparison reuse checked rule mechanics without identifying its
reference judgments with guarded derivability. -/
noncomputable def importProof {V : Type} {Ω Ξ : List (Judgment V)} {a : Judgment V}
    (d : Derivation Contextual.theory Ξ a)
    (h : ∀ b, b ∈ Ξ → Derivation theory Ω b) : Derivation theory Ω a := by
  induction d with
  | hypothesis hb => exact h _ hb
  | rule a σ _ ih => exact .rule (T := theory) (Sum.inl a) σ ih
  | reflexive t => exact .reflexive t
  | symmetric _ ih => exact .symmetric ih
  | transitive _ _ ih ih' => exact .transitive ih ih'
  | congruence op _ ih => exact .congruence op ih
  | conversion p _ _ ih hp => exact .conversion p ih hp

noncomputable def unary {V : Type} {Ω : List (Judgment V)} {a b : Judgment V}
    (f : Derivation Contextual.theory [a] b) (h : Derivation theory Ω a) :
    Derivation theory Ω b := importProof f (by intro c hc; simp only [List.mem_singleton] at hc; subst c; exact h)

noncomputable def binary {V : Type} {Ω : List (Judgment V)} {a b c : Judgment V}
    (f : Derivation Contextual.theory [a, b] c)
    (ha : Derivation theory Ω a) (hb : Derivation theory Ω b) : Derivation theory Ω c :=
  importProof f (by
    classical
    intro d hd
    simp at hd
    by_cases e : d = a
    · subst d; exact ha
    · have e' : d = b := hd.resolve_left e
      subst d; exact hb)

noncomputable def ternary {V : Type} {Ω : List (Judgment V)} {a b c d : Judgment V}
    (f : Derivation Contextual.theory [a, b, c] d)
    (ha : Derivation theory Ω a) (hb : Derivation theory Ω b)
    (hc : Derivation theory Ω c) : Derivation theory Ω d :=
  importProof f (by
    classical
    intro e he
    simp at he
    by_cases h : e = a
    · subst e; exact ha
    · by_cases h' : e = b
      · subst e; exact hb
      · have h'' : e = c := (he.resolve_left h).resolve_left h'
        subst e; exact hc)

noncomputable def quaternary {V : Type} {Ω : List (Judgment V)} {a b c d e : Judgment V}
    (f : Derivation Contextual.theory [a, b, c, d] e)
    (ha : Derivation theory Ω a) (hb : Derivation theory Ω b)
    (hc : Derivation theory Ω c) (hd : Derivation theory Ω d) : Derivation theory Ω e :=
  importProof f (by
    classical
    intro p hp
    simp at hp
    by_cases h : p = a
    · subst p; exact ha
    · by_cases h' : p = b
      · subst p; exact hb
      · by_cases h'' : p = c
        · subst p; exact hc
        · have hlast := ((hp.resolve_left h).resolve_left h').resolve_left h''
          subst p; exact hd)

end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
