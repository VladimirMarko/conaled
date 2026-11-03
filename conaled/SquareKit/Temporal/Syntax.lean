import SquareKit.Temporal.Finite

/-! Optional syntax for products, next and finite until. Context entries carry
absolute processing indices. Next introduction requires evidence at the next
index; it does not predict a future atom from current data. -/
namespace Temporal
universe u

inductive Formula (Atom : Type u) : Type u
  | atom : Atom → Formula Atom
  | unit : Formula Atom
  | prod : Formula Atom → Formula Atom → Formula Atom
  | next : Formula Atom → Formula Atom
  | until : Formula Atom → Formula Atom → Formula Atom

def Formula.meaning {Atom : Type u} (V : Atom → Nat → Type u) : Formula Atom → Nat → Type u
  | .atom p, n => V p n
  | .unit, _ => PUnit
  | .prod a b, n => a.meaning V n × b.meaning V n
  | .next a, n => a.meaning V (n+1)
  | .until a b, n => Until (a.meaning V) (b.meaning V) n

abbrev Context (Atom : Type u) := List (Nat × Formula Atom)

/-- Proof-relevant occurrence, allowing repeated context entries. -/
inductive Var {Atom : Type u} : Context Atom → Nat → Formula Atom → Type u
  | here {Γ n a} : Var ((n,a)::Γ) n a
  | there {Γ n a m b} : Var Γ n a → Var ((m,b)::Γ) n a

inductive Term {Atom : Type u} (Γ : Context Atom) : Nat → Formula Atom → Type u
  | var {n a} : Var Γ n a → Term Γ n a
  | unit {n} : Term Γ n .unit
  | pair {n a b} : Term Γ n a → Term Γ n b → Term Γ n (.prod a b)
  | fst {n a b} : Term Γ n (.prod a b) → Term Γ n a
  | snd {n a b} : Term Γ n (.prod a b) → Term Γ n b
  | nextI {n a} : Term Γ (n+1) a → Term Γ n (.next a)
  | nextE {n a} : Term Γ n (.next a) → Term Γ (n+1) a
  | untilNow {n a b} : Term Γ n b → Term Γ n (.until a b)
  | untilWait {n a b} : Term Γ n a → Term Γ (n+1) (.until a b) → Term Γ n (.until a b)

abbrev Env {Atom : Type u} (V : Atom → Nat → Type u) (Γ : Context Atom) :=
  ∀ {n a}, Var Γ n a → a.meaning V n

namespace Term
variable {Atom : Type u} {Γ Δ Θ : Context Atom} {n : Nat} {a : Formula Atom}

def eval {V : Atom → Nat → Type u} (ρ : Env V Γ) : {n : Nat} → {a : Formula Atom} → Term Γ n a → a.meaning V n
  | _, _, .var x => ρ x
  | _, _, .unit => PUnit.unit
  | _, _, .pair x y => (eval ρ x, eval ρ y)
  | _, _, .fst x => (eval ρ x).1
  | _, _, .snd x => (eval ρ x).2
  | _, _, .nextI (n := m) (a := b) x => eval ρ (n := m+1) (a := b) x
  | _, _, .nextE (n := m) (a := b) x => eval ρ (n := m) (a := .next b) x
  | _, _, .untilNow x => .now (eval ρ x)
  | _, _, .untilWait x y => .wait (eval ρ x) (eval ρ y)

abbrev Substitution (Δ Γ : Context Atom) := ∀ {n a}, Var Γ n a → Term Δ n a

def subst (σ : Substitution Δ Γ) : {n : Nat} → {a : Formula Atom} → Term Γ n a → Term Δ n a
  | _, _, .var x => σ x
  | _, _, .unit => .unit
  | _, _, .pair x y => .pair (subst σ x) (subst σ y)
  | _, _, .fst x => .fst (subst σ x)
  | _, _, .snd x => .snd (subst σ x)
  | _, _, .nextI x => .nextI (subst σ x)
  | _, _, .nextE x => .nextE (subst σ x)
  | _, _, .untilNow x => .untilNow (subst σ x)
  | _, _, .untilWait x y => .untilWait (subst σ x) (subst σ y)

@[simp] theorem subst_id (t : Term Γ n a) : subst (fun x => .var x) t = t := by
  induction t <;> simp_all [subst]

theorem subst_comp (σ : Substitution Δ Γ) (τ : Substitution Θ Δ) (t : Term Γ n a) :
    subst τ (subst σ t) = subst (fun x => subst τ (σ x)) t := by
  induction t <;> simp_all [subst]

/-- Syntactic substitution commutes with the interpretation of every constructor. -/
theorem eval_subst {V : Atom → Nat → Type u} (ρ : Env V Δ)
    (σ : Substitution Δ Γ) (t : Term Γ n a) :
    eval ρ (subst σ t) = eval (fun x => eval ρ (σ x)) t := by
  induction t <;> simp_all [subst, eval] <;> rfl

end Term
end Temporal
