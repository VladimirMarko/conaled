import SquareKit.Internal.CoreTyping
import SquareKit.Internal.GraphEmissionPure

/-! Typing preservation with explicit compatible contexts and assignments. -/
namespace SquareKit.Internal.GraphEmissionPure
open GraphTarget CoreSyntax

structure ModelTyped (C : Context) (m : Model) : Prop where
  carrier : ∀ s, HasType C (m.carrier s) (.sort m.level)
  first : HasType C m.first (.all (m.carrier .input) (m.carrier .middle).shift)
  second : HasType C m.second (.all (m.carrier .middle) (m.carrier .output).shift)

def AssignmentTyped (C : Context) (m : Model) (a : Assignment Γ) : Prop :=
  ∀ {s} (i : Var Γ s), HasType C (a i) (m.carrier s)

theorem ModelTyped.arrow (hm : ModelTyped C m) (f : Graph.Arrow s t) :
    HasType C (m.arrow f) (.all (m.carrier s) (m.carrier t).shift) := by
  cases f
  · exact hm.first
  · exact hm.second

theorem ModelTyped.shift (hm : ModelTyped C m) (b : E) : ModelTyped (b :: C) m.shift := by
  have hr : liftRen Nat.succ ∘ Nat.succ = Nat.succ ∘ Nat.succ := by funext n; rfl
  constructor
  · intro s; exact HasType.weaken (hm.carrier s)
  · have h := HasType.weaken (b := b) hm.first
    simpa only [Model.shift, Model.map, Expr.shift, Expr.rename, Expr.rename_comp, hr] using h
  · have h := HasType.weaken (b := b) hm.second
    simpa only [Model.shift, Model.map, Expr.shift, Expr.rename, Expr.rename_comp, hr] using h

theorem AssignmentTyped.shift {Γ : List Ty} {a : Assignment Γ} (ha : AssignmentTyped C m a) (b : E) :
    AssignmentTyped (b :: C) m.shift (GraphEmissionPure.shift a) := fun i => HasType.weaken (ha i)

theorem AssignmentTyped.extend {Γ : List Ty} {a : Assignment Γ} (ha : AssignmentTyped C m a) (s : Ty) :
    AssignmentTyped (m.carrier s :: C) m.shift (GraphEmissionPure.extend (s := s) (GraphEmissionPure.shift a) (.bvar 0)) := by
  intro t i
  cases i with
  | zero => exact .var .zero
  | succ i => exact HasType.weaken (ha i)

theorem instantiate_eq (b t : E) : CoreSyntax.instantiate b t = b.subst (singleCore t) := by
  apply congrArg (fun σ => b.subst σ)
  funext n; cases n <;> rfl

theorem term_typed {Γ : List Ty} {a : Assignment Γ} (hm : ModelTyped C m) (ha : AssignmentTyped C m a)
    (t : GraphTarget.Term Γ s) : HasType C (term m a t) (m.carrier s) := by
  induction t with
  | var i => exact ha i
  | app f t ih =>
    have h := HasType.app (hm.arrow f) ih
    rw [instantiate_eq, shift_single] at h
    exact h

theorem formula_typed {Γ : List Ty} {a : Assignment Γ} (hm : ModelTyped C m) (ha : AssignmentTyped C m a)
    (p : GraphTarget.Formula Γ) : HasType C (formula m a p) (.sort .zero) := by
  induction p generalizing C m with
  | eq x y => exact .eqType (hm.carrier _) (term_typed hm ha x) (term_typed hm ha y)
  | conj p q hp hq => exact .andType (hp hm ha) (hq hm ha)
  | @ex s Γ p ih => exact .existsType (hm.carrier s) (ih (hm.shift _) (AssignmentTyped.extend ha s))

theorem code_typed {a : Assignment Γ} {p q : GraphTarget.Formula Γ} (d : Code p q)
    (hm : ModelTyped C m) (ha : AssignmentTyped C m a)
    (hh : HasType C h (formula m a p)) : HasType C (code m a d h) (formula m a q) := by
  induction d generalizing C m h with
  | ident => exact hh
  | cut d e hd he => exact he hm ha (hd hm ha hh)
  | left => exact .andLeft (formula_typed hm ha _) (formula_typed hm ha _) hh
  | right => exact .andRight (formula_typed hm ha _) (formula_typed hm ha _) hh
  | pair d e hd he =>
    exact .andIntro (formula_typed hm ha _) (formula_typed hm ha _)
      (hd hm ha hh) (he hm ha hh)
  | refl => exact .eqRefl (hm.carrier _) (term_typed hm ha _)
  | symm d ih => exact .eqSymm (hm.carrier _) (term_typed hm ha _) (term_typed hm ha _) (ih hm ha hh)
  | trans d e hd he =>
    exact .eqTrans (hm.carrier _) (term_typed hm ha _) (term_typed hm ha _) (term_typed hm ha _)
      (hd hm ha hh) (he hm ha hh)
  | congr d ih =>
    exact .congrArg (hm.carrier _) (hm.carrier _) (term_typed hm ha _) (term_typed hm ha _)
      (hm.arrow _) (ih hm ha hh)
  | intro p t =>
    apply HasType.existsIntro (hm.carrier _) (formula_typed (hm.shift _) (AssignmentTyped.extend ha _) p)
      (term_typed hm ha t)
    simpa only [formula_instantiate, instantiate_eq] using hh
  | subst σ d ih =>
    simp only [code, formula_subst] at hh ⊢
    exact ih hm (fun i => term_typed hm ha (σ i)) hh
  | @elim Γ s p q d ih =>
    apply HasType.existsElim (hm.carrier s) (formula_typed (hm.shift _) (AssignmentTyped.extend ha s) p)
      (formula_typed hm ha q) hh
    have hb : HasType
        (formula m.shift (GraphEmissionPure.extend (s := s) (GraphEmissionPure.shift a) (.bvar 0)) p :: m.carrier s :: C)
        (.bvar 0) (formula m.shift.shift (shift (extend (GraphEmissionPure.shift a) (.bvar 0))) p) := by
      rw [formula_weaken]; exact .var .zero
    have hr := ih ((hm.shift _).shift _) (AssignmentTyped.shift (AssignmentTyped.extend ha s) _) hb
    simpa only [formula_weaken, formula_shift] using hr
  | @elimWith Γ s p b q d ih =>
    apply HasType.existsElim (hm.carrier s) (formula_typed (hm.shift _) (AssignmentTyped.extend ha s) p)
      (formula_typed hm ha q)
      (.andRight (formula_typed hm ha b) (formula_typed hm ha (.ex p)) hh)
    have hw : HasType
        (formula m.shift (GraphEmissionPure.extend (s := s) (GraphEmissionPure.shift a) (.bvar 0)) p :: m.carrier s :: C)
        (.bvar 0) (formula m.shift.shift (shift (extend (GraphEmissionPure.shift a) (.bvar 0))) p) := by
      rw [formula_weaken]; exact .var .zero
    have hb := HasType.weaken (b := formula m.shift (GraphEmissionPure.extend (s := s) (GraphEmissionPure.shift a) (.bvar 0)) p)
      (HasType.weaken (b := m.carrier s)
        (HasType.andLeft (formula_typed hm ha b) (formula_typed hm ha (.ex p)) hh))
    have hb' : HasType
        (formula m.shift (GraphEmissionPure.extend (s := s) (GraphEmissionPure.shift a) (.bvar 0)) p :: m.carrier s :: C)
        (Expr.apps (.const ``And.left []) [formula m a b, formula m a (.ex p), h]).shift.shift
        (formula m.shift.shift (shift (extend (GraphEmissionPure.shift a) (.bvar 0))) (b.shift (s := s))) := by
      simpa only [formula_weaken, formula_shift] using hb
    have hm' := (hm.shift (m.carrier s)).shift (formula m.shift (GraphEmissionPure.extend (s := s) (GraphEmissionPure.shift a) (.bvar 0)) p)
    have ha' : AssignmentTyped
        (formula m.shift (extend (shift a) (.bvar 0)) p :: m.carrier s :: C)
        m.shift.shift (shift (extend (shift a) (.bvar 0))) :=
      AssignmentTyped.shift (AssignmentTyped.extend ha s) _
    have hp := HasType.andIntro (formula_typed hm' ha' b.shift) (formula_typed hm' ha' p) hb' hw
    have hr := ih hm' ha' hp
    simpa only [formula_weaken, formula_shift] using hr


/-- Types of g, f, C, B, A in their respective preceding contexts. -/
def parameterContext : Context :=
  [.all (.bvar 2) (.bvar 2), .all (.bvar 2) (.bvar 2),
    .sort (.succ (.param `v)), .sort (.succ (.param `v)), .sort (.succ (.param `v))]

theorem parameterModel_typed : ModelTyped parameterContext parameterModel := by
  constructor
  · intro s
    cases s
    · exact .var (.succ (.succ (.succ (.succ .zero))))
    · exact .var (.succ (.succ (.succ .zero)))
    · exact .var (.succ (.succ .zero))
  · exact .var (.succ .zero)
  · exact .var .zero

/-- Telescope abstraction preserves typing for any suitably typed continuation. -/
theorem context_typed (Γ : List Ty) (k : Model → Assignment Γ → E × E)
    (hm : ModelTyped C m)
    (hk : ∀ C m a, ModelTyped C m → AssignmentTyped C m a →
      HasType C (k m a).2 (k m a).1) :
    HasType C (context m Γ k).2 (context m Γ k).1 := by
  induction Γ with
  | nil => exact hk C m _ hm (fun i => nomatch i)
  | cons s Γ ih =>
    apply ih
    intro C m a hm ha
    exact .lam (hm.carrier s)
      (hk _ m.shift (extend (shift a) (.bvar 0)) (hm.shift _) (AssignmentTyped.extend ha s))

theorem closeParameters_typed (ht : HasType parameterContext body ty) :
    HasType [] (closeParameters false body) (closeParameters true ty) := by
  apply HasType.lam HasType.sort
  apply HasType.lam HasType.sort
  apply HasType.lam HasType.sort
  apply HasType.lam
    (HasType.pi (HasType.var (Lookup.succ (Lookup.succ Lookup.zero)))
      (HasType.var (Lookup.succ (Lookup.succ Lookup.zero))))
  apply HasType.lam
    (HasType.pi (HasType.var (Lookup.succ (Lookup.succ Lookup.zero)))
      (HasType.var (Lookup.succ (Lookup.succ Lookup.zero))))
  exact ht

/-- Empty-context typing, with no model or assignment well-formedness premise
left to the caller. It covers exactly the type and body sent for installation. -/
theorem emitCore_typed (d : GraphTarget.Declaration) :
    HasType [] (emitCore d).2 (emitCore d).1 := by
  apply closeParameters_typed
  apply context_typed d.context _ parameterModel_typed
  intro C m a hm ha
  apply HasType.lam (formula_typed hm ha d.premise)
  apply code_typed d.code (hm.shift _) (AssignmentTyped.shift ha _)
  rw [formula_weaken]
  exact .var .zero

/-- Raw Lean.Expr typing uses the independently defined decoder, not a test
of equality to this particular producer. -/
def ArtifactTyped (artifact : Lean.Expr × Lean.Expr) : Prop :=
  ∃ ty body, Expr.ofLean artifact.1 = some ty ∧ Expr.ofLean artifact.2 = some body ∧
    HasType [] body ty

theorem emit_typed (d : GraphTarget.Declaration) : ArtifactTyped (emit d) :=
  ⟨_, _, (emit_decodes d).1, (emit_decodes d).2, emitCore_typed d⟩

end SquareKit.Internal.GraphEmissionPure
