import SquareKit.Lawvere.Operations
import SquareKit.GuardedTheory

/-! Ordinary equational presentations use the existing finitary term syntax.
Conditional rules and predicates are not quotiented as unconditional equations. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SquareKit.Lawvere
open CategoryTheory
universe u w

structure Presentation where
  Symbol : Type u
  arity : Symbol → Nat
  Equation : Type u
  variableCount : Equation → Nat
  lhs : (e : Equation) → FinitaryTerm Symbol arity (Fin (variableCount e))
  rhs : (e : Equation) → FinitaryTerm Symbol arity (Fin (variableCount e))

namespace Presentation
variable (P : Presentation.{u})
abbrev Term (n : Nat) := FinitaryTerm P.Symbol P.arity (Fin n)

/-- Equational congruence, closed under simultaneous substitution. -/
inductive Equal : {n : Nat} → P.Term n → P.Term n → Prop where
  | refl (t) : Equal t t
  | symm : Equal s t → Equal t s
  | trans : Equal r s → Equal s t → Equal r t
  | node (op) {s t} : (∀ i, Equal (s i) (t i)) → Equal (.node op s) (.node op t)
  | equation (e) : Equal (P.lhs e) (P.rhs e)
  | subst {m n} {s t : P.Term n} (h : Equal s t) (σ : Fin n → P.Term m) :
      Equal (s.bind σ) (t.bind σ)

abbrev setoid (n : Nat) : Setoid (P.Term n) :=
  ⟨P.Equal, ⟨Equal.refl, Equal.symm, Equal.trans⟩⟩

theorem bind_congr {m n} (t : P.Term n) (σ τ : Fin n → P.Term m)
    (h : ∀ i, P.Equal (σ i) (τ i)) : P.Equal (t.bind σ) (t.bind τ) := by
  induction t with
  | leaf i => exact h i
  | node op ts ih => exact .node op ih

/-- Quotient terms form the operations of the presented theory. -/
noncomputable def operations : Operations.{u} where
  Op n := Quotient (P.setoid n)
  var i := Quotient.mk _ (.leaf i)
  subst t σ := Quotient.liftOn t
    (fun t => Quotient.mk _ (t.bind (fun i => (σ i).out)))
    (fun _ _ h => Quotient.sound (.subst h _))
  var_subst i σ := Quotient.out_eq (σ i)
  subst_var t := by
    refine Quotient.inductionOn t ?_
    intro t
    apply Quotient.sound
    have h := P.bind_congr t (fun i => (Quotient.mk (P.setoid _) (.leaf i)).out)
      FinitaryTerm.leaf (fun i => (Quotient.exact (Quotient.out_eq (Quotient.mk (P.setoid _) (.leaf i))) : P.Equal _ _))
    change P.Equal _ _
    simpa only [FinitaryTerm.bind_leaf] using h
  subst_assoc t σ τ := by
    refine Quotient.inductionOn t ?_
    intro t
    apply Quotient.sound
    rw [FinitaryTerm.bind_assoc]
    apply P.bind_congr t
    intro i
    have he : (σ i).liftOn (fun s => Quotient.mk (P.setoid _) (s.bind (fun j => (τ j).out)))
        (fun _ _ h => Quotient.sound (.subst h _)) =
        Quotient.mk (P.setoid _) ((σ i).out.bind (fun j => (τ j).out)) := by
      conv_lhs => rw [← Quotient.out_eq (σ i)]
      rfl
    dsimp only
    rw [he]
    exact Equal.symm (Quotient.exact (Quotient.out_eq (Quotient.mk (P.setoid _) ((σ i).out.bind (fun j => (τ j).out)))))

/-- Existing guarded syntax receives only the presentation's unconditional equations. -/
def signature : GuardedTheory.Signature := ⟨P.Symbol, P.arity, PEmpty, PEmpty.elim⟩
def guarded : GuardedTheory.Theory P.signature where
  Axiom := P.Equation
  rule e := ⟨P.variableCount e, 0, Fin.elim0, .eq (P.lhs e) (P.rhs e)⟩

/-- A guarded model of these equations interprets every derived equality. -/
theorem sound (M : GuardedTheory.Model P.guarded) {n} {s t : P.Term n}
    (h : P.Equal s t) (ρ : Fin n → M.Carrier) :
    FinitaryTerm.fold M.operation ρ s = FinitaryTerm.fold M.operation ρ t := by
  induction h with
  | refl => rfl
  | symm _ ih => exact (ih ρ).symm
  | trans _ _ ih ih' => exact (ih ρ).trans (ih' ρ)
  | node op h ih => exact congrArg (M.operation op) (funext (fun i => ih i ρ))
  | equation e => exact M.rules e ρ (fun i => Fin.elim0 i)
  | subst h σ ih => simpa only [FinitaryTerm.fold_bind] using ih (fun i => FinitaryTerm.fold M.operation ρ (σ i))

noncomputable def algebra (M : GuardedTheory.Model.{u,w} P.guarded) : P.operations.Algebra where
  Carrier := M.Carrier
  act t ρ := Quotient.liftOn t (FinitaryTerm.fold M.operation ρ) (fun _ _ h => P.sound M h ρ)
  var_act _ _ := rfl
  subst_act t σ ρ := by
    refine Quotient.inductionOn t ?_
    intro t
    change FinitaryTerm.fold M.operation ρ (t.bind _) = _
    rw [FinitaryTerm.fold_bind]
    congr 1
    funext i
    exact congrArg (fun q => Quotient.liftOn q (FinitaryTerm.fold M.operation ρ)
      (fun _ _ h => P.sound M h ρ)) (Quotient.out_eq (σ i))
/-- Interpret a signature by operations of another theory. -/
def evaluate {O : Operations} (op : (s : P.Symbol) → O.Op (P.arity s)) {n} :
    P.Term n → O.Op n := FinitaryTerm.fold (fun s args => O.subst (op s) args) O.var

theorem evaluate_bind {O : Operations} (op : (s : P.Symbol) → O.Op (P.arity s))
    {m n} (t : P.Term n) (σ : Fin n → P.Term m) :
    P.evaluate op (t.bind σ) = O.subst (P.evaluate op t) (fun i => P.evaluate op (σ i)) := by
  induction t with
  | leaf i => exact (O.var_subst i (fun j => P.evaluate op (σ j))).symm
  | node s ts ih =>
    change O.subst (op s) (fun i => P.evaluate op ((ts i).bind σ)) = _
    rw [show P.evaluate op (.node s ts) = O.subst (op s) (fun i => P.evaluate op (ts i)) from rfl,
      O.subst_assoc]
    exact congrArg (O.subst (op s)) (funext ih)

theorem evaluate_sound {O : Operations} (op : (s : P.Symbol) → O.Op (P.arity s))
    (laws : ∀ e, P.evaluate op (P.lhs e) = P.evaluate op (P.rhs e))
    {n} {s t : P.Term n} (h : P.Equal s t) : P.evaluate op s = P.evaluate op t := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | node s h ih => exact congrArg (O.subst (op s)) (funext ih)
  | equation e => exact laws e
  | subst h σ ih => rw [P.evaluate_bind, P.evaluate_bind, ih]

/-- A law-respecting assignment of generators induces a theory morphism. -/
noncomputable def interpretation {O : Operations} (op : (s : P.Symbol) → O.Op (P.arity s))
    (laws : ∀ e, P.evaluate op (P.lhs e) = P.evaluate op (P.rhs e)) :
    P.operations.Map O where
  map t := Quotient.liftOn t (P.evaluate op) (fun _ _ h => P.evaluate_sound op laws h)
  map_var _ := rfl
  map_subst t σ := by
    refine Quotient.inductionOn t ?_
    intro t
    change P.evaluate op (t.bind _) = _
    rw [P.evaluate_bind]
    congr 1
    funext i
    exact congrArg (fun q => Quotient.liftOn q (P.evaluate op)
      (fun _ _ h => P.evaluate_sound op laws h)) (Quotient.out_eq (σ i))

end Presentation
end SquareKit.Lawvere
