import SquareKit.FinitaryTerm

/-! Annotation-free terms and guarded equational derivations. Object-language
identity, when supplied by a signature, is an operation of that signature.
The equality atom below is the equational judgment of the presented theory. -/

namespace SquareKit.GuardedTheory
universe u v w

structure Signature where
  Operation : Type u
  arity : Operation → Nat
  Predicate : Type u
  arguments : Predicate → Nat

abbrev Term (S : Signature.{u}) (V : Type v) := FinitaryTerm S.Operation S.arity V

@[match_pattern] abbrev Term.var {S : Signature.{u}} {V : Type v} (x : V) : Term S V :=
  FinitaryTerm.leaf x
@[match_pattern] abbrev Term.app {S : Signature.{u}} {V : Type v}
    (op : S.Operation) (args : Fin (S.arity op) → Term S V) : Term S V :=
  FinitaryTerm.node op args

abbrev Term.subst {S : Signature.{u}} {V : Type v} {W : Type w}
    (σ : V → Term S W) : Term S V → Term S W := FinitaryTerm.bind σ

@[simp] theorem Term.subst_id {S : Signature} {V : Type} (t : Term S V) :
    t.subst .var = t := FinitaryTerm.bind_leaf t

theorem Term.subst_comp {S : Signature} {V W X : Type} (t : Term S V)
    (σ : V → Term S W) (τ : W → Term S X) :
    (t.subst σ).subst τ = t.subst (fun x => (σ x).subst τ) :=
  FinitaryTerm.bind_assoc t σ τ

inductive Atom (S : Signature.{u}) (V : Type v) : Type (max u v) where
  | eq : Term S V → Term S V → Atom S V
  | pred : (p : S.Predicate) → (Fin (S.arguments p) → Term S V) → Atom S V

def Atom.subst {S : Signature.{u}} {V : Type v} {W : Type w}
    (σ : V → Term S W) : Atom S V → Atom S W
  | .eq a b => .eq (a.subst σ) (b.subst σ)
  | .pred p args => .pred p (fun i => (args i).subst σ)

@[simp] theorem Atom.subst_id {S : Signature} {V : Type} (a : Atom S V) :
    a.subst .var = a := by
  cases a <;> simp only [subst, Term.subst_id]

theorem Atom.subst_comp {S : Signature} {V W X : Type} (a : Atom S V)
    (σ : V → Term S W) (τ : W → Term S X) :
    (a.subst σ).subst τ = a.subst (fun x => (σ x).subst τ) := by
  cases a <;> simp only [subst, Term.subst_comp]

structure Rule (S : Signature.{u}) where
  parameterCount : Nat
  hypotheses : Nat
  premise : Fin hypotheses → Atom S (Fin parameterCount)
  conclusion : Atom S (Fin parameterCount)

structure Theory (S : Signature.{u}) where
  Axiom : Type u
  rule : Axiom → Rule S

structure Algebra (S : Signature.{u}) where
  Carrier : Type v
  operation : (op : S.Operation) → (Fin (S.arity op) → Carrier) → Carrier
  predicate : (p : S.Predicate) → (Fin (S.arguments p) → Carrier) → Prop

abbrev Term.eval {S : Signature.{u}} {V : Type w} (M : Algebra.{u,v} S)
    (ρ : V → M.Carrier) : Term S V → M.Carrier := FinitaryTerm.fold M.operation ρ

def Atom.eval {S : Signature.{u}} {V : Type w} (M : Algebra.{u,v} S)
    (ρ : V → M.Carrier) : Atom S V → Prop
  | .eq a b => a.eval M ρ = b.eval M ρ
  | .pred p args => M.predicate p (fun i => (args i).eval M ρ)

theorem Term.eval_subst {S : Signature} {V W : Type} (M : Algebra S)
    (ρ : W → M.Carrier) (σ : V → Term S W) (t : Term S V) :
    (t.subst σ).eval M ρ = t.eval M (fun x => (σ x).eval M ρ) :=
  FinitaryTerm.fold_bind M.operation σ ρ t

theorem Atom.eval_subst {S : Signature} {V W : Type} (M : Algebra S)
    (ρ : W → M.Carrier) (σ : V → Term S W) (a : Atom S V) :
    (a.subst σ).eval M ρ = a.eval M (fun x => (σ x).eval M ρ) := by
  cases a <;> simp only [subst, eval, Term.eval_subst]

def Satisfies {S : Signature} (M : Algebra S) (r : Rule S) : Prop :=
  ∀ ρ : Fin r.parameterCount → M.Carrier,
    (∀ i, (r.premise i).eval M ρ) → r.conclusion.eval M ρ

structure Model {S : Signature.{u}} (T : Theory S) extends Algebra.{u,v} S where
  rules : ∀ a, Satisfies toAlgebra (T.rule a)

inductive Derivation {S : Signature.{u}} (T : Theory S) {V : Type v}
    (Γ : List (Atom S V)) : Atom S V → Type (max u v) where
  | hypothesis : a ∈ Γ → Derivation T Γ a
  | rule (a : T.Axiom) (σ : Fin (T.rule a).parameterCount → Term S V)
      (premises : ∀ i, Derivation T Γ ((T.rule a).premise i |>.subst σ)) :
      Derivation T Γ ((T.rule a).conclusion.subst σ)
  | reflexive (t : Term S V) : Derivation T Γ (.eq t t)
  | symmetric : Derivation T Γ (.eq s t) → Derivation T Γ (.eq t s)
  | transitive : Derivation T Γ (.eq r s) → Derivation T Γ (.eq s t) →
      Derivation T Γ (.eq r t)
  | congruence (op : S.Operation) {args args' : Fin (S.arity op) → Term S V}
      (proofs : ∀ i, Derivation T Γ (.eq (args i) (args' i))) :
      Derivation T Γ (.eq (.app op args) (.app op args'))
  | conversion (p : S.Predicate) {args args' : Fin (S.arguments p) → Term S V}
      (proofs : ∀ i, Derivation T Γ (.eq (args i) (args' i)))
      (proof : Derivation T Γ (.pred p args)) : Derivation T Γ (.pred p args')

/-- Substitution acts on complete derivations, including rule instances and
all equality/conversion premises. It introduces no semantic annotations. -/
noncomputable def Derivation.substitute {S : Signature} {T : Theory S} {V W : Type}
    {Γ : List (Atom S V)} {a : Atom S V} (σ : V → Term S W)
    (d : Derivation T Γ a) :
    Derivation T (Γ.map (Atom.subst σ)) (a.subst σ) := by
  induction d with
  | hypothesis h => exact .hypothesis (List.mem_map_of_mem h)
  | rule a τ _ ih =>
    rw [Atom.subst_comp]
    exact .rule a (fun i => (τ i).subst σ)
      (fun i => by simpa only [Atom.subst_comp] using ih i)
  | reflexive t => exact .reflexive (t.subst σ)
  | symmetric _ ih => exact .symmetric ih
  | transitive _ _ ih ih' => exact .transitive ih ih'
  | congruence op _ ih => exact .congruence op ih
  | conversion p _ _ ih hp => exact .conversion p ih hp

theorem Derivation.sound {S : Signature} {T : Theory S} {V : Type}
    (M : Model T) {Γ : List (Atom S V)} {a : Atom S V} (d : Derivation T Γ a)
    (ρ : V → M.Carrier) (hΓ : ∀ p ∈ Γ, p.eval M.toAlgebra ρ) :
    a.eval M.toAlgebra ρ := by
  induction d with
  | hypothesis h => exact hΓ _ h
  | rule a σ _ ih =>
    rw [Atom.eval_subst]
    apply M.rules a
    intro i
    simpa only [Atom.eval_subst] using ih i
  | reflexive => rfl
  | symmetric _ ih => exact ih.symm
  | transitive _ _ ih ih' => exact ih.trans ih'
  | congruence op _ ih => exact congrArg (M.operation op) (funext ih)
  | conversion p _ _ ih hp =>
    change M.predicate p _
    change M.predicate p _ at hp
    rwa [← funext ih]

structure Hom {S : Signature.{u}} (M : Algebra.{u,v} S) (N : Algebra.{u,w} S) where
  map : M.Carrier → N.Carrier
  operation : ∀ op args, map (M.operation op args) = N.operation op (map ∘ args)
  predicate : ∀ p args, M.predicate p args → N.predicate p (map ∘ args)

theorem Hom.eval {S : Signature} {M N : Algebra S} (F : Hom M N)
    {V : Type} (t : Term S V) (ρ : V → M.Carrier) :
    F.map (t.eval M ρ) = t.eval N (F.map ∘ ρ) := by
  induction t with
  | leaf => rfl
  | node op args ih =>
    rw [Term.eval, FinitaryTerm.fold, F.operation]
    congr 1
    exact funext ih

def Hom.identity {S : Signature} (M : Algebra S) : Hom M M where
  map x := x
  operation _ _ := rfl
  predicate _ _ h := h

def Hom.compose {S : Signature} {M N P : Algebra S} (G : Hom N P) (F : Hom M N) :
    Hom M P where
  map := G.map ∘ F.map
  operation op args := (congrArg G.map (F.operation op args)).trans (G.operation op _)
  predicate p args h := G.predicate p _ (F.predicate p args h)

/-- A totalized partial algebra. Defined results require defined operands.
The distinguished failure value belongs to the interpreter, not the source. -/
structure PartialAlgebra (S : Signature.{u}) extends Algebra.{u,v} S where
  invalid : Carrier
  strict : ∀ op args, operation op args ≠ invalid → ∀ i, args i ≠ invalid

/-- Only defined operations must commute. The map need not reflect definedness
and may send formerly ill-sorted raw operands to well-sorted target operands. -/
structure PartialHom {S : Signature.{u}} (M : PartialAlgebra.{u,v} S)
    (N : PartialAlgebra.{u,w} S) where
  map : M.Carrier → N.Carrier
  operation : ∀ op args, M.operation op args ≠ M.invalid →
    map (M.operation op args) = N.operation op (map ∘ args)
  defined : ∀ x, x ≠ M.invalid → map x ≠ N.invalid
  predicate : ∀ p args, M.predicate p args → N.predicate p (map ∘ args)

theorem PartialHom.eval {S : Signature} {M N : PartialAlgebra S} (F : PartialHom M N)
    {V : Type} (t : Term S V) (ρ : V → M.Carrier)
    (ht : t.eval M.toAlgebra ρ ≠ M.invalid) :
    F.map (t.eval M.toAlgebra ρ) = t.eval N.toAlgebra (F.map ∘ ρ) := by
  induction t with
  | leaf => rfl
  | node op args ih =>
    rw [Term.eval, FinitaryTerm.fold, F.operation op _ ht]
    congr 1
    exact funext (fun i => ih i (M.strict op _ ht i))

def PartialHom.identity {S : Signature} (M : PartialAlgebra S) : PartialHom M M where
  map x := x
  operation _ _ _ := rfl
  defined _ h := h
  predicate _ _ h := h

def PartialHom.compose {S : Signature} {M N P : PartialAlgebra S}
    (G : PartialHom N P) (F : PartialHom M N) : PartialHom M P where
  map := G.map ∘ F.map
  operation op args h := by
    have hn : N.operation op (F.map ∘ args) ≠ N.invalid := by
      intro e
      exact F.defined _ h ((F.operation op args h).trans e)
    exact (congrArg G.map (F.operation op args h)).trans (G.operation op _ hn)
  defined x h := G.defined _ (F.defined x h)
  predicate p args h := G.predicate p _ (F.predicate p args h)

end SquareKit.GuardedTheory
