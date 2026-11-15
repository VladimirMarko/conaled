import SquareKit.GuardedTheory

/-! Same-signature theory interpretations supplied by derivations of primitive
rules. Composition substitutes proofs, rather than asking clients to reprove
transport of each derived argument. This does not change the underlying logic. -/
namespace SquareKit.GuardedTheory

/-- Replace assumptions by selected derivations, retaining the conclusion. -/
noncomputable def Derivation.cut {S : Signature} {T : Theory S} {V : Type}
    {Γ Δ : List (Atom S V)} {a : Atom S V} (d : Derivation T Γ a)
    (h : ∀ p ∈ Γ, Derivation T Δ p) : Derivation T Δ a := by
  induction d with
  | hypothesis hp => exact h _ hp
  | rule ax σ _ ih => exact .rule ax σ ih
  | reflexive t => exact .reflexive t
  | symmetric _ ih => exact .symmetric ih
  | transitive _ _ ih ih' => exact .transitive ih ih'
  | congruence op _ ih => exact .congruence op ih
  | conversion p _ _ ih hp => exact .conversion p ih hp

/-- A source rule can expand to an arbitrary target derivation. Operations,
predicates, and their equality judgment stay fixed in this bounded interface. -/
structure RuleInterpretation {S : Signature} (T U : Theory S) where
  rule : ∀ a, Derivation U (List.ofFn (T.rule a).premise) (T.rule a).conclusion

namespace RuleInterpretation
variable {S : Signature} {T U W : Theory S}

/-- Primitive certificates induce transport of the whole proof tree. -/
noncomputable def transport (F : RuleInterpretation T U) {V : Type}
    {Γ : List (Atom S V)} {a : Atom S V} (d : Derivation T Γ a) :
    Derivation U Γ a := by
  induction d with
  | hypothesis hp => exact .hypothesis hp
  | rule ax σ _ ih =>
    apply ((F.rule ax).substitute σ).cut
    intro p hp
    have hx : ∃ i, ((T.rule ax).premise i).subst σ = p := by
      rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
      rcases List.mem_ofFn.mp hq with ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    exact (Classical.choose_spec hx) ▸ ih (Classical.choose hx)
  | reflexive t => exact .reflexive t
  | symmetric _ ih => exact .symmetric ih
  | transitive _ _ ih ih' => exact .transitive ih ih'
  | congruence op _ ih => exact .congruence op ih
  | conversion p _ _ ih hp => exact .conversion p ih hp

/-- A primitive rule is derivable from its own listed premises. -/
noncomputable def axiomDerivation (T : Theory S) (a : T.Axiom) :
    Derivation T (List.ofFn (T.rule a).premise) (T.rule a).conclusion := by
  simpa only [Atom.subst_id] using
    (Derivation.rule (T := T) a Term.var (fun i => by
      simpa only [Atom.subst_id] using
        (Derivation.hypothesis (T := T) (List.mem_ofFn.mpr ⟨i, rfl⟩))))

/-- Exact inclusion is a special case; arbitrary derived-rule expansions use
`RuleInterpretation` directly. -/
noncomputable def ofRuleMap (f : T.Axiom → U.Axiom)
    (h : ∀ a, U.rule (f a) = T.rule a) : RuleInterpretation T U where
  rule a := by
    have d := axiomDerivation U (f a)
    rw [h a] at d
    exact d

noncomputable def identity (T : Theory S) : RuleInterpretation T T := ⟨axiomDerivation T⟩

noncomputable def compose (G : RuleInterpretation U W) (F : RuleInterpretation T U) :
    RuleInterpretation T W := ⟨fun a => G.transport (F.rule a)⟩

/-- Model reduction uses the same algebra. Only its rule certificates change. -/
noncomputable def reduct (F : RuleInterpretation T U) (M : Model U) : Model T where
  toAlgebra := M.toAlgebra
  rules a ρ h := (F.rule a).sound M ρ (by
    intro p hp
    rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
    exact h i)

theorem reduct_identity (M : Model T) : (identity T).reduct M = M := by
  cases M
  rfl

/-- This satisfaction square is exact because the syntax and algebra agree. -/
theorem satisfaction (F : RuleInterpretation T U) (M : Model U) {V : Type}
    (a : Atom S V) (ρ : V → M.Carrier) :
    a.eval (F.reduct M).toAlgebra ρ ↔ a.eval M.toAlgebra ρ := Iff.rfl

/-- Reducing models along the composed route retains the exact algebra and
its selected operation values, not merely existence of a satisfying model. -/
theorem reduct_compose (G : RuleInterpretation U W) (F : RuleInterpretation T U)
    (M : Model W) : (G.compose F).reduct M = F.reduct (G.reduct M) := rfl

/-- Substitution and proof transport retain precisely the same source judgment. -/
noncomputable def transportSubstitute (F : RuleInterpretation T U) {V X : Type}
    {Γ : List (Atom S V)} {a : Atom S V} (d : Derivation T Γ a)
    (σ : V → Term S X) : Derivation U (Γ.map (Atom.subst σ)) (a.subst σ) :=
  F.transport (d.substitute σ)

end RuleInterpretation
end SquareKit.GuardedTheory
