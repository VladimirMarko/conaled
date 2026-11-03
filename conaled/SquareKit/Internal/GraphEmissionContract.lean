import SquareKit.Internal.GraphEmissionProof

/-! Telescope abstraction and the producer-independent artifact contract. -/
namespace SquareKit.Internal.GraphEmissionPure
open GraphTarget
universe v

inductive Telescope (M : Interpretation Graph.Arrow) : Frame M → E → E → Prop → Prop where
  | implication : f.prop p P → f.prop q Q →
      ProofDenotes M f.proofBinder
        (addHyp (fun _ _ _ => False) (.bvar 0) p.shift P) body q.shift Q →
      Telescope M f (.all p q.shift) (.lam p body) (P → Q)
  | data {s : Ty} {P : M.Carrier s → Prop} :
      (∀ x, Telescope M (f.dataBinder x) ty body (P x)) →
      Telescope M f (.all (f.model.carrier s) ty) (.lam (f.model.carrier s) body) (∀ x, P x)
  | meaning : Telescope M f ty body P → (P ↔ Q) → Telescope M f ty body Q

theorem Telescope.sound (d : Telescope M f ty body P) : P := by
  induction d with
  | implication _ _ hd =>
    intro hp
    apply hd.sound
    intro e p P hh
    rcases hh with ⟨_, _, rfl⟩ | hh
    · exact hp
    · exact False.elim hh
  | data _ ih => exact ih
  | meaning _ h ih => exact h.mp ih

def emptyAssignment : Assignment [] := fun i => nomatch i
def emptyEnv (M : Interpretation Graph.Arrow) : Env M [] := fun i => nomatch i

theorem env_eta {M : Interpretation Graph.Arrow} (ρ : Env M (s :: Γ)) :
    (fun {t} (i : Var (s :: Γ) t) => Env.extend (ρ .zero) (fun i => ρ (.succ i)) i) =
      (fun {t} (i : Var (s :: Γ) t) => ρ i) := by
  funext t i; cases i <;> rfl

/-- Abstract any object telescope. The continuation contract is independent of
how its type and body were produced. The context's head becomes the last binder. -/
theorem context_denotes (M : Interpretation Graph.Arrow) (m : Model) (Γ : List Ty)
    (k : Model → Assignment Γ → E × E) (P : Env M Γ → Prop)
    (hk : ∀ m a ρ, Telescope M ⟨Γ, m, a, ρ⟩ (k m a).1 (k m a).2 (P ρ)) :
    Telescope M ⟨[], m, emptyAssignment, emptyEnv M⟩
      (context m Γ k).1 (context m Γ k).2 (∀ ρ, P ρ) := by
  induction Γ with
  | nil =>
    apply Telescope.meaning (hk m emptyAssignment (emptyEnv M))
    constructor
    · intro h ρ
      have he : (fun {s} (i : Var [] s) => ρ i) = (fun {s} (i : Var [] s) => emptyEnv M i) := by funext s i; exact nomatch i
      simpa only [he] using h
    · exact fun h => h _
  | cons s Γ ih =>
    let k' : Model → Assignment Γ → E × E := fun m a =>
      let r := k m.shift (extend (shift a) (.bvar 0))
      (.all (m.carrier s) r.1, .lam (m.carrier s) r.2)
    have hd : ∀ m a ρ, Telescope M ⟨Γ, m, a, ρ⟩ (k' m a).1 (k' m a).2
        (∀ x, P (ρ.extend x)) := by
      intro m a ρ
      exact .data (fun x => hk m.shift (extend (shift a) (.bvar 0)) (ρ.extend x))
    apply Telescope.meaning (ih k' (fun ρ => ∀ x, P (ρ.extend x)) hd)
    constructor
    · intro h ρ
      simpa only [env_eta] using h (fun i => ρ (.succ i)) (ρ .zero)
    · exact fun h ρ x => h (ρ.extend x)

/-- Closed typing and meaning at the five graph parameters. The literal syntax
in this rule fixes Type v, f : A → B, g : B → C, and their de Bruijn positions.
The interpretation record packages exactly these carrier and arrow choices;
its empty relation signature supplies no additional mathematical assumption. -/
inductive ClosedDenotes : E → E → Prop → Prop where
  | parameters {P : Interpretation.{0,v} Graph.Arrow → Prop} :
      (∀ M, Telescope M ⟨[], parameterModel, emptyAssignment, emptyEnv M⟩ ty body (P M)) →
      ClosedDenotes
        (.all (.sort (.succ (.param `v)))
          (.all (.sort (.succ (.param `v)))
            (.all (.sort (.succ (.param `v)))
              (.all (.all (.bvar 2) (.bvar 2))
                (.all (.all (.bvar 2) (.bvar 2)) ty)))))
        (.lam (.sort (.succ (.param `v)))
          (.lam (.sort (.succ (.param `v)))
            (.lam (.sort (.succ (.param `v)))
              (.lam (.all (.bvar 2) (.bvar 2))
                (.lam (.all (.bvar 2) (.bvar 2)) body))))) (∀ M, P M)

theorem ClosedDenotes.sound (d : ClosedDenotes ty body P) : P := by
  cases d with
  | parameters hd => exact fun M => (hd M).sound

/-- The contract accepts any artifact carrying this derivation, not only the
pure producer's byte sequence. It decodes both type and body from Lean.Expr. -/
def ArtifactDenotes (artifact : Lean.Expr × Lean.Expr) (P : Prop) : Prop :=
  ∃ ty body, CoreSyntax.Expr.ofLean artifact.1 = some ty ∧
    CoreSyntax.Expr.ofLean artifact.2 = some body ∧ ClosedDenotes.{v} ty body P

theorem ArtifactDenotes.sound (h : ArtifactDenotes artifact P) : P := by
  obtain ⟨_, _, _, _, hd⟩ := h
  exact hd.sound

theorem emitCore_denotes (d : GraphTarget.Declaration) :
    ClosedDenotes.{v} (emitCore d).1 (emitCore d).2 (Declaration.denote.{v} d) := by
  apply ClosedDenotes.parameters
  intro M
  apply context_denotes
  intro m a ρ
  have hp : ProofDenotes M ⟨d.context, m.shift, shift a, ρ⟩
      (addHyp (fun _ _ _ => False) (.bvar 0) (formula m a d.premise).shift
        (d.premise.eval M ρ)) (.bvar 0)
      (formula m.shift (shift a) d.premise) (d.premise.eval M ρ) := by
    rw [formula_weaken]
    exact .hyp (.inl ⟨rfl, rfl, rfl⟩)
  have hd := code_denotes M d.code m.shift (shift a) ρ _ (.bvar 0) hp
  simpa only [formula_weaken] using
    Telescope.implication (f := ⟨d.context, m, a, ρ⟩)
      (formula_denotes M m a ρ d.premise) (formula_denotes M m a ρ d.conclusion)
      (by simpa only [formula_weaken, Frame.proofBinder] using hd)

/-- Preservation for every declaration and all its Code constructors. -/
theorem emit_denotes (d : GraphTarget.Declaration) :
    ArtifactDenotes.{v} (emit d) (Declaration.denote.{v} d) :=
  ⟨_, _, (emit_decodes d).1, (emit_decodes d).2, emitCore_denotes d⟩

end SquareKit.Internal.GraphEmissionPure
