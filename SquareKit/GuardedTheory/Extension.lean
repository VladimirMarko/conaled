import SquareKit.GuardedTheory

/-! Signature extension retains source derivations. Additional rules may refer
to both earlier and new operations; models must interpret those complete rules. -/

namespace SquareKit.GuardedTheory
set_option backward.isDefEq.respectTransparency false
universe u v

def Signature.sum (S R : Signature.{u}) : Signature where
  Operation := S.Operation ⊕ R.Operation
  arity := Sum.elim S.arity R.arity
  Predicate := S.Predicate ⊕ R.Predicate
  arguments := Sum.elim S.arguments R.arguments

def Term.inl {S : Signature.{u}} {V : Type v} (R : Signature.{u}) :
    Term S V → Term (S.sum R) V
  | .var x => .var x
  | .app op args => .app (.inl op) (fun i => (args i).inl R)

def Atom.inl {S : Signature.{u}} {V : Type v} (R : Signature.{u}) :
    Atom S V → Atom (S.sum R) V
  | .eq a b => .eq (a.inl R) (b.inl R)
  | .pred p args => .pred (.inl p) (fun i => (args i).inl R)

def Rule.inl {S : Signature.{u}} (R : Signature.{u}) (r : Rule S) : Rule (S.sum R) where
  parameterCount := r.parameterCount
  hypotheses := r.hypotheses
  premise i := (r.premise i).inl R
  conclusion := r.conclusion.inl R

theorem Term.inl_subst {S R : Signature} {V W : Type} (t : Term S V)
    (σ : V → Term S W) :
    (t.subst σ).inl R = (t.inl R).subst (fun x => (σ x).inl R) := by
  induction t with
  | var => rfl
  | app op args ih => simp only [subst, inl, ih]

theorem Atom.inl_subst {S R : Signature} {V W : Type} (a : Atom S V)
    (σ : V → Term S W) :
    (a.subst σ).inl R = (a.inl R).subst (fun x => (σ x).inl R) := by
  cases a <;> simp only [subst, inl, Term.inl_subst]

def Theory.extend {S : Signature.{u}} (T : Theory S) (R : Signature.{u})
    (Extra : Type u) (rule : Extra → Rule (S.sum R)) : Theory (S.sum R) where
  Axiom := T.Axiom ⊕ Extra
  rule
    | .inl a => (T.rule a).inl R
    | .inr a => rule a

def Algebra.restrictLeft {S R : Signature.{u}} (M : Algebra.{u,v} (S.sum R)) : Algebra S where
  Carrier := M.Carrier
  operation op args := M.operation (.inl op) args
  predicate p args := M.predicate (.inl p) args

theorem Term.eval_inl {S R : Signature} (M : Algebra (S.sum R)) {V : Type}
    (t : Term S V) (ρ : V → M.Carrier) :
    (t.inl R).eval M ρ = t.eval M.restrictLeft ρ := by
  induction t with
  | var => rfl
  | app op args ih => simp only [inl, eval, Algebra.restrictLeft, ih]; rfl

theorem Atom.eval_inl {S R : Signature} (M : Algebra (S.sum R)) {V : Type}
    (a : Atom S V) (ρ : V → M.Carrier) :
    (a.inl R).eval M ρ = a.eval M.restrictLeft ρ := by
  cases a <;> simp only [inl, eval, Term.eval_inl, Algebra.restrictLeft] <;> rfl

/-- Model restriction forgets new operations and laws. Its soundness field is
constructed from the old-rule branch of the supplied extended model. -/
def Model.restrictLeft {S R : Signature} {T : Theory S} {Extra : Type}
    {rule : Extra → Rule (S.sum R)} (M : Model (T.extend R Extra rule)) : Model T where
  toAlgebra := M.toAlgebra.restrictLeft
  rules a ρ h := by
    have h' := M.rules (.inl a) ρ
    simp only [Theory.extend, Rule.inl, Atom.eval_inl] at h'
    exact h' h

/-- An admitted extension preserves old derivations as source data, without
asking ordinary callers to rebuild their interpretations or annotations. -/
noncomputable def Derivation.inl {S R : Signature} {T : Theory S} {Extra : Type}
    (rule : Extra → Rule (S.sum R)) {V : Type} {Γ : List (Atom S V)} {a : Atom S V}
    (d : Derivation T Γ a) :
    Derivation (T.extend R Extra rule) (Γ.map (Atom.inl R)) (a.inl R) := by
  induction d with
  | hypothesis h => exact .hypothesis (List.mem_map_of_mem h)
  | rule ax σ _ ih =>
    rw [Atom.inl_subst]
    exact Derivation.rule (T := T.extend R Extra rule) (Sum.inl ax) (fun x => (σ x).inl R)
      (fun i => by simpa only [Theory.extend, Rule.inl, Atom.inl_subst] using ih i)
  | reflexive t => exact .reflexive (t.inl R)
  | symmetric _ ih => exact .symmetric ih
  | transitive _ _ ih ih' => exact .transitive ih ih'
  | congruence op _ ih => exact Derivation.congruence (T := T.extend R Extra rule) (Sum.inl op) ih
  | conversion p _ _ ih hp => exact Derivation.conversion (T := T.extend R Extra rule) (Sum.inl p) ih hp

end SquareKit.GuardedTheory
