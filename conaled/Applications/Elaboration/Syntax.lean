import SquareKit.Relations
import Mathlib.Data.Vector.Basic

/-! A bounded elaboration experiment: natural numbers and packages containing a
length and a vector indexed by that length. Contexts and declaration signatures
are explicit. This is an ordinary Lean client, not a replacement core language. -/
namespace Elaboration

inductive Ty where
  | nat | packet
  deriving DecidableEq, Repr

abbrev Ty.Value : Ty → Type
  | .nat => Nat
  | .packet => (n : Nat) × Vector Nat n

inductive Var : List Ty → Ty → Type where
  | here : Var (t :: Γ) t
  | there : Var Γ t → Var (u :: Γ) t

abbrev Valuation (Γ : List Ty) := ∀ {t}, Var Γ t → t.Value

def Valuation.extend (ρ : Valuation Γ) (v : t.Value) : Valuation (t :: Γ)
  | _, .here => v
  | _, .there x => ρ x

/-- This dependent consumer uses the retained length and all vector entries. -/
def consume (p : Ty.Value .packet) : Nat := p.1 + p.2.toList.sum

def makePacket (n a : Nat) : Ty.Value .packet := ⟨n, Vector.replicate n a⟩

/-- A typed, scoped surface presentation. Hole identifiers are not variables. -/
inductive Source (Γ Δ : List Ty) : Ty → Type where
  | lit : Nat → Source Γ Δ .nat
  | bound : Var Γ t → Source Γ Δ t
  | named : Var Δ t → Source Γ Δ t
  | hole : Nat → Source Γ Δ .nat
  | add : Source Γ Δ .nat → Source Γ Δ .nat → Source Γ Δ .nat
  | vector : Nat → Source Γ Δ .nat → Source Γ Δ .nat → Source Γ Δ .packet
  | total : Source Γ Δ .packet → Source Γ Δ .nat

/-- The bounded target exposes its pair constructor and dependent elimination. -/
inductive Core (Γ Δ : List Ty) : Ty → Type where
  | numeral : Nat → Core Γ Δ .nat
  | variable : Var Γ t → Core Γ Δ t
  | constant : Var Δ t → Core Γ Δ t
  | metavariable : Nat → Core Γ Δ .nat
  | plus : Core Γ Δ .nat → Core Γ Δ .nat → Core Γ Δ .nat
  | pack : Nat → Core Γ Δ .nat → Core Γ Δ .nat → Core Γ Δ .packet
  | fold : Core Γ Δ .packet → Core Γ Δ .nat

/-- A vector carries a universe metavariable. This fragment admits its Nat
entries only at level zero; final elaboration must discharge that obligation. -/
def Source.eval (μ : Nat → Nat) (ρ : Valuation Γ) (δ : Valuation Δ) :
    Source Γ Δ t → t.Value
  | .lit n => n
  | .bound x => ρ x
  | .named x => δ x
  | .hole k => μ k
  | .add a b => a.eval μ ρ δ + b.eval μ ρ δ
  | .vector _ n a => makePacket (n.eval μ ρ δ) (a.eval μ ρ δ)
  | .total p => consume (p.eval μ ρ δ)

def Core.eval (μ : Nat → Nat) (ρ : Valuation Γ) (δ : Valuation Δ) :
    Core Γ Δ t → t.Value
  | .numeral n => n
  | .variable x => ρ x
  | .constant x => δ x
  | .metavariable k => μ k
  | .plus a b => a.eval μ ρ δ + b.eval μ ρ δ
  | .pack _ n a => makePacket (n.eval μ ρ δ) (a.eval μ ρ δ)
  | .fold p => consume (p.eval μ ρ δ)

def lower : Source Γ Δ t → Core Γ Δ t
  | .lit n => .numeral n
  | .bound x => .variable x
  | .named x => .constant x
  | .hole k => .metavariable k
  | .add a b => .plus (lower a) (lower b)
  | .vector u n a => .pack u (lower n) (lower a)
  | .total p => .fold (lower p)

theorem lower_sound (s : Source Γ Δ t) (μ ρ δ) :
    (lower s).eval μ ρ δ = s.eval μ ρ δ := by
  induction s <;> simp_all [lower, Core.eval, Source.eval]

abbrev Substitution (Γ Γ' Δ : List Ty) := ∀ {t}, Var Γ t → Source Γ' Δ t

def Source.subst (σ : Substitution Γ Γ' Δ) : Source Γ Δ t → Source Γ' Δ t
  | .lit n => .lit n
  | .bound x => σ x
  | .named x => .named x
  | .hole k => .hole k
  | .add a b => .add (a.subst σ) (b.subst σ)
  | .vector u n a => .vector u (n.subst σ) (a.subst σ)
  | .total p => .total (p.subst σ)

def Core.subst (σ : ∀ {t}, Var Γ t → Core Γ' Δ t) : Core Γ Δ t → Core Γ' Δ t
  | .numeral n => .numeral n
  | .variable x => σ x
  | .constant x => .constant x
  | .metavariable k => .metavariable k
  | .plus a b => .plus (a.subst σ) (b.subst σ)
  | .pack u n a => .pack u (n.subst σ) (a.subst σ)
  | .fold p => .fold (p.subst σ)

theorem lower_subst (s : Source Γ Δ t) (σ : Substitution Γ Γ' Δ) :
    lower (s.subst σ) = (lower s).subst (fun x => lower (σ x)) := by
  induction s <;> simp_all [Source.subst, Core.subst, lower]

theorem Source.eval_subst (s : Source Γ Δ t) (σ : Substitution Γ Γ' Δ) (μ ρ δ) :
    (s.subst σ).eval μ ρ δ = s.eval μ (fun x => (σ x).eval μ ρ δ) δ := by
  induction s <;> simp_all [Source.subst, Source.eval]

theorem Source.subst_comp (s : Source Γ Δ t) (σ : Substitution Γ Γ' Δ)
    (τ : Substitution Γ' Γ'' Δ) :
    (s.subst σ).subst τ = s.subst (fun x => (σ x).subst τ) := by
  induction s <;> simp_all [Source.subst]

def Source.weaken (s : Source Γ Δ t) : Source (u :: Γ) Δ t :=
  s.subst (fun x => .bound (.there x))

theorem weaken_sound (s : Source Γ Δ t) (μ ρ δ) (v : Ty.Value u) :
    s.weaken.eval μ (ρ.extend v) δ = s.eval μ ρ δ := by
  simp [Source.weaken, Source.eval_subst, Source.eval, Valuation.extend]

/-- Renaming declarations never changes their meanings. -/
def Source.renameGlobals (f : ∀ {t}, Var Δ t → Var Δ' t) :
    Source Γ Δ t → Source Γ Δ' t
  | .lit n => .lit n
  | .bound x => .bound x
  | .named x => .named (f x)
  | .hole k => .hole k
  | .add a b => .add (a.renameGlobals f) (b.renameGlobals f)
  | .vector u n a => .vector u (n.renameGlobals f) (a.renameGlobals f)
  | .total p => .total (p.renameGlobals f)

theorem Source.eval_renameGlobals (s : Source Γ Δ t)
    (f : ∀ {t}, Var Δ t → Var Δ' t) (μ ρ δ) :
    (s.renameGlobals f).eval μ ρ δ = s.eval μ ρ (fun x => δ (f x)) := by
  induction s <;> simp_all [Source.renameGlobals, Source.eval]

theorem environment_extension (s : Source Γ Δ t) (μ ρ δ) (v : Ty.Value u) :
    (s.renameGlobals (fun x => .there x)).eval μ ρ (δ.extend v) = s.eval μ ρ δ := by
  simp [Source.eval_renameGlobals, Valuation.extend]

/-- Source fidelity is pointwise equality of independently specified denotations,
not the assertion that the target happens to typecheck. -/
def Faithful (s : Source Γ Δ t) (c : Core Γ Δ t) : Prop :=
  ∀ μ ρ δ, c.eval μ ρ δ = s.eval μ ρ δ

def sourceRep (Γ Δ : List Ty) (t : Ty) : Relational.RelRep where
  R := Source Γ Δ t
  S := (Nat → Nat) → Valuation Γ → Valuation Δ → t.Value
  Rel s f := s.eval = f

def coreRep (Γ Δ : List Ty) (t : Ty) : Relational.RelRep where
  R := Core Γ Δ t
  S := (Nat → Nat) → Valuation Γ → Valuation Δ → t.Value
  Rel c f := c.eval = f

def loweringSquare : Relational.RelSquare (sourceRep Γ Δ t) (coreRep Γ Δ t) where
  impl := lower
  spec := id
  preserves h := by
    dsimp [sourceRep, coreRep] at *
    rw [← h]
    funext μ ρ δ
    exact lower_sound _ _ _ _

end Elaboration
