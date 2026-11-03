import SquareKit.Internal.GraphEmissionPure

/-! Primitive proof rules for the emitted fragment, independent of Code.
The judgment records both the raw proposition syntax and its native meaning.
Structural rules name their binder action; they do not admit arbitrary
semantic equivalence as a conversion rule for Lean types. -/
namespace SquareKit.Internal.GraphEmissionPure
open GraphTarget

structure Frame (M : Interpretation Graph.Arrow) where
  context : List Ty
  model : Model
  assignment : Assignment context
  values : Env M context

def Frame.proofBinder (f : Frame M) : Frame M :=
  ⟨f.context, f.model.shift, shift f.assignment, f.values⟩

def Frame.dataBinder (f : Frame M) (x : M.Carrier s) : Frame M :=
  ⟨s :: f.context, f.model.shift, extend (shift f.assignment) (.bvar 0), Env.extend x f.values⟩

def Frame.term (f : Frame M) (e : E) (x : M.Carrier s) : Prop :=
  TermDenotes M f.model f.assignment f.values e x

def Frame.prop (f : Frame M) (e : E) (P : Prop) : Prop :=
  FormulaDenotes M f.model f.assignment f.values e P

abbrev Hypotheses := E → E → Prop → Prop

def shiftHyp (H : Hypotheses) : Hypotheses := fun e p P =>
  ∃ e' p', H e' p' P ∧ e = e'.shift ∧ p = p'.shift

def addHyp (H : Hypotheses) (e p : E) (P : Prop) : Hypotheses := fun e' p' P' =>
  (e' = e ∧ p' = p ∧ P' = P) ∨ H e' p' P'

def SoundHyp (H : Hypotheses) : Prop := ∀ e p P, H e p P → P

inductive ProofDenotes (M : Interpretation Graph.Arrow) :
    Frame M → Hypotheses → E → E → Prop → Prop where
  | hyp : H e p P → ProofDenotes M f H e p P
  | mapHyp : (∀ e p P, H e p P → H' e p P) →
      ProofDenotes M f H e p P → ProofDenotes M f H' e p P
  | reindex : f.model = g.model →
      (∀ {s} (i : Var f.context s), g.term (f.assignment i) (f.values i)) →
      ProofDenotes M f H e p P → ProofDenotes M g H e p P
  | cutHyp : ProofDenotes M f H e p P →
      ProofDenotes M f (addHyp H e p P) d q Q → ProofDenotes M f H d q Q
  | weakenProof : ProofDenotes M f H e p P →
      ProofDenotes M f.proofBinder (shiftHyp H) e.shift p.shift P
  | weakenData (x : M.Carrier s) : ProofDenotes M f H e p P →
      ProofDenotes M (f.dataBinder x) (shiftHyp H) e.shift p.shift P
  | left : f.prop p P → f.prop q Q → ProofDenotes M f H e (conj p q) (P ∧ Q) →
      ProofDenotes M f H (.apps (.const ``And.left []) [p, q, e]) p P
  | right : f.prop p P → f.prop q Q → ProofDenotes M f H e (conj p q) (P ∧ Q) →
      ProofDenotes M f H (.apps (.const ``And.right []) [p, q, e]) q Q
  | pair : f.prop p P → f.prop q Q →
      ProofDenotes M f H e p P → ProofDenotes M f H d q Q →
      ProofDenotes M f H (.apps (.const ``And.intro []) [p, q, e, d]) (conj p q) (P ∧ Q)
  | refl {s : Ty} {x : M.Carrier s} : f.term t x →
      ProofDenotes M f H (.apps (.const ``Eq.refl [f.model.level]) [f.model.carrier s, t])
        (eq f.model s t t) (x = x)
  | symm {s : Ty} {x y : M.Carrier s} : f.term a x → f.term b y →
      ProofDenotes M f H e (eq f.model s a b) (x = y) →
      ProofDenotes M f H
        (.apps (.const ``Eq.symm [f.model.level]) [f.model.carrier s, a, b, e])
        (eq f.model s b a) (y = x)
  | trans {s : Ty} {x y z : M.Carrier s} : f.term a x → f.term b y → f.term c z →
      ProofDenotes M f H e (eq f.model s a b) (x = y) →
      ProofDenotes M f H d (eq f.model s b c) (y = z) →
      ProofDenotes M f H
        (.apps (.const ``Eq.trans [f.model.level]) [f.model.carrier s, a, b, c, e, d])
        (eq f.model s a c) (x = z)
  | congr {s t : Ty} {x y : M.Carrier s} (g : Graph.Arrow s t) :
      f.term a x → f.term b y → ProofDenotes M f H e (eq f.model s a b) (x = y) →
      ProofDenotes M f H
        (.apps (.const ``congrArg [f.model.level, f.model.level])
          [f.model.carrier s, f.model.carrier t, a, b, f.model.arrow g, e])
        (eq f.model t (.app (f.model.arrow g) a) (.app (f.model.arrow g) b))
        (M.arrow g x = M.arrow g y)
  | intro {s : Ty} {x : M.Carrier s} {P : M.Carrier s → Prop} :
      (∀ x, (f.dataBinder x).prop p (P x)) → f.term t x →
      ProofDenotes M f H e (p.subst (singleCore t)) (P x) →
      ProofDenotes M f H
        (.apps (.const ``Exists.intro [f.model.level])
          [f.model.carrier s, .lam (f.model.carrier s) p, t, e])
        (ex f.model s p) (∃ x, P x)
  | elim {s : Ty} {P : M.Carrier s → Prop} :
      (∀ x, (f.dataBinder x).prop p (P x)) → f.prop q Q →
      ProofDenotes M f H e (ex f.model s p) (∃ x, P x) →
      (∀ x, ProofDenotes M (f.dataBinder x).proofBinder
        (addHyp (shiftHyp (shiftHyp H)) (.bvar 0) p.shift (P x))
        branch q.shift.shift Q) →
      ProofDenotes M f H
        (.apps (.const ``Exists.elim [f.model.level])
          [f.model.carrier s, .lam (f.model.carrier s) p, q, e,
            .lam (f.model.carrier s) (.lam p branch)]) q Q

/-- Soundness of the primitive derivation rules, without reference to Code or
its emitter. Typing syntax remains an index throughout this argument. -/
theorem ProofDenotes.sound (d : ProofDenotes M f H e p P) (h : SoundHyp H) : P := by
  induction d with
  | hyp hd => exact h _ _ _ hd
  | mapHyp hm _ ih => exact ih (fun e p P hp => h e p P (hm e p P hp))
  | reindex _ _ _ ih => exact ih h
  | cutHyp _ _ ih ij =>
    apply ij
    intro e p P hp
    rcases hp with ⟨_, _, rfl⟩ | hp
    · exact ih h
    · exact h e p P hp
  | weakenProof _ ih | weakenData _ _ ih =>
    exact ih (fun e p P hp => h e.shift p.shift P ⟨e, p, hp, rfl, rfl⟩)
  | left _ _ _ ih => exact (ih h).1
  | right _ _ _ ih => exact (ih h).2
  | pair _ _ _ _ ih ij => exact ⟨ih h, ij h⟩
  | refl _ => rfl
  | symm _ _ _ ih => exact (ih h).symm
  | trans _ _ _ _ _ ih ij => exact (ih h).trans (ij h)
  | congr g _ _ _ ih => exact congrArg (M.arrow g) (ih h)
  | intro _ _ _ ih => exact ⟨_, ih h⟩
  | elim _ _ _ _ ih ij =>
    obtain ⟨x, hx⟩ := ih h
    apply ij x
    intro e p P hp
    rcases hp with ⟨_, _, rfl⟩ | ⟨e', p', ⟨e'', p'', hh, _, _⟩, _, _⟩
    · exact hx
    · exact h e'' p'' P hh


theorem code_denotes (M : Interpretation Graph.Arrow) {p q : GraphTarget.Formula Γ}
    (d : Code p q) (m : Model) (a : Assignment Γ) (ρ : Env M Γ) (H : Hypotheses) (h : E)
    (hp : ProofDenotes M ⟨Γ, m, a, ρ⟩ H h (formula m a p) (p.eval M ρ)) :
    ProofDenotes M ⟨Γ, m, a, ρ⟩ H (code m a d h) (formula m a q) (q.eval M ρ) := by
  induction d generalizing m H h with
  | ident => exact hp
  | cut d e hd he => exact he m a ρ H _ (hd m a ρ H h hp)
  | left => exact .left (formula_denotes M m a ρ _) (formula_denotes M m a ρ _) hp
  | right => exact .right (formula_denotes M m a ρ _) (formula_denotes M m a ρ _) hp
  | pair d e hd he =>
    exact .pair (formula_denotes M m a ρ _) (formula_denotes M m a ρ _)
      (hd m a ρ H h hp) (he m a ρ H h hp)
  | refl => exact .refl (term_denotes M m a ρ _)
  | symm d ih =>
    exact .symm (term_denotes M m a ρ _) (term_denotes M m a ρ _)
      (ih m a ρ H h hp)
  | trans d e hd he =>
    exact .trans (term_denotes M m a ρ _) (term_denotes M m a ρ _)
      (term_denotes M m a ρ _) (hd m a ρ H h hp) (he m a ρ H h hp)
  | congr d ih =>
    exact .congr _ (term_denotes M m a ρ _) (term_denotes M m a ρ _)
      (ih m a ρ H h hp)
  | intro p t =>
    apply ProofDenotes.intro (f := ⟨_, m, a, ρ⟩) (fun x => formula_denotes M m.shift (extend (shift a) (.bvar 0)) (ρ.extend x) p)
      (term_denotes M m a ρ t)
    simpa only [formula_instantiate, GraphTarget.formula_instantiate] using hp
  | @subst Γ Δ p q σ d ih =>
    simp only [code, formula_subst, GraphTarget.formula_subst] at hp ⊢
    apply ProofDenotes.cutHyp hp
    apply ProofDenotes.reindex (g := ⟨Δ, m, a, ρ⟩) (f := ⟨Γ, m, (fun i => term m a (σ i)),
      (fun i => (σ i).eval M ρ)⟩) rfl
    · intro s i; exact term_denotes M m a ρ (σ i)
    · exact ih m _ _ _ h (.hyp (.inl ⟨rfl, rfl, rfl⟩))
  | @elim Γ s p q d ih =>
    apply ProofDenotes.elim (f := ⟨_, m, a, ρ⟩) (fun x => formula_denotes M m.shift (extend (shift a) (.bvar 0)) (ρ.extend x) p)
      (formula_denotes M m a ρ q) hp
    intro x
    have hb : ProofDenotes M
        ⟨s :: Γ, m.shift.shift, shift (extend (shift a) (.bvar 0)), ρ.extend x⟩
        (addHyp (shiftHyp (shiftHyp H)) (.bvar 0)
          (formula m.shift (extend (shift a) (.bvar 0)) p).shift (p.eval M (ρ.extend x)))
        (.bvar 0) (formula m.shift.shift (shift (extend (shift a) (.bvar 0))) p)
        (p.eval M (ρ.extend x)) := by
      rw [formula_weaken]
      exact .hyp (.inl ⟨rfl, rfl, rfl⟩)
    have hr := ih m.shift.shift _ (ρ.extend x) _ (.bvar 0) hb
    simpa only [formula_weaken, formula_shift, GraphTarget.formula_shift,
      Frame.dataBinder, Frame.proofBinder] using hr
  | @elimWith Γ s p b q d ih =>
    apply ProofDenotes.elim (f := ⟨_, m, a, ρ⟩) (fun x => formula_denotes M m.shift (extend (shift a) (.bvar 0)) (ρ.extend x) p)
      (formula_denotes M m a ρ q)
      (.right (f := ⟨_, m, a, ρ⟩) (formula_denotes M m a ρ b) (formula_denotes M m a ρ (.ex p)) hp)
    intro x
    let B := formula m.shift (extend (shift a) (.bvar 0)) p
    let H' := addHyp (shiftHyp (shiftHyp H)) (.bvar 0) B.shift (p.eval M (ρ.extend x))
    have hh := ProofDenotes.weakenProof (ProofDenotes.weakenData x
      (ProofDenotes.left (f := ⟨_, m, a, ρ⟩) (formula_denotes M m a ρ b) (formula_denotes M m a ρ (.ex p)) hp))
    have hh' := ProofDenotes.mapHyp (H' := H') (fun _ _ _ hx => Or.inr hx) hh
    have hw : ProofDenotes M
        ⟨s :: Γ, m.shift.shift, shift (extend (shift a) (.bvar 0)), ρ.extend x⟩ H'
        (.bvar 0) (formula m.shift.shift (shift (extend (shift a) (.bvar 0))) p)
        (p.eval M (ρ.extend x)) := by
      rw [formula_weaken]
      exact .hyp (.inl ⟨rfl, rfl, rfl⟩)
    have hh'' : ProofDenotes M
        ⟨s :: Γ, m.shift.shift, shift (extend (shift a) (.bvar 0)), ρ.extend x⟩ H'
        (CoreSyntax.Expr.apps (.const ``And.left [])
          [formula m a b, formula m a (.ex p), h]).shift.shift
        (formula m.shift.shift (shift (extend (shift a) (.bvar 0))) (b.shift (s := s)))
        (b.shift.eval M (ρ.extend x)) := by
      simpa only [formula_weaken, formula_shift, GraphTarget.formula_shift,
        Frame.dataBinder, Frame.proofBinder] using hh'
    have hb := ProofDenotes.pair (f := ⟨s :: Γ, m.shift.shift,
      shift (extend (shift a) (.bvar 0)), ρ.extend x⟩)
      (formula_denotes M m.shift.shift (shift (extend (shift a) (.bvar 0))) (ρ.extend x) b.shift)
      (formula_denotes M m.shift.shift (shift (extend (shift a) (.bvar 0))) (ρ.extend x) p) hh'' hw
    have hr := ih m.shift.shift _ (ρ.extend x) H' _ hb
    simpa only [formula_weaken, formula_shift, GraphTarget.formula_shift,
      Frame.dataBinder, Frame.proofBinder] using hr

end SquareKit.Internal.GraphEmissionPure
