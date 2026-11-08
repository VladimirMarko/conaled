import Mathlib.Data.List.Basic

/-! Experimental two-lock access fragment (#375). Context declarations are Boolean;
identity fibers and their selected dependent pairs are generated separately. This
is not an implementation of all MTT type formers or dependent context extension. -/
namespace SquareKit.Internal.ModalAccess

inductive Letter where
  | a | b | c
  deriving DecidableEq
abbrev Word := List Letter

/-- Generated reachability in the one-mode word theory. Cells are proof irrelevant;
this is the thin presentation, with identities, vertical and horizontal composition. -/
inductive Cell : Word → Word → Prop
  | id (w) : Cell w w
  | alpha : Cell [.a] [.b]
  | comp {u v w} : Cell u v → Cell v w → Cell u w
  | tensor {u v u' v'} : Cell u v → Cell u' v' → Cell (u ++ u') (v ++ v')

theorem Cell.length {u v} (k : Cell u v) : u.length = v.length := by
  induction k with
  | id => rfl
  | alpha => rfl
  | comp _ _ h j => exact h.trans j
  | tensor _ _ h j => simp only [List.length_append, h, j]

/-- Horizontal and vertical compositions obey interchange in the thin theory. -/
theorem Cell.interchange {u v w u' v' w'}
    (k : Cell u v) (h : Cell v w) (k' : Cell u' v') (h' : Cell v' w') :
    (k.tensor k').comp (h.tensor h') = (k.comp h).tensor (k'.comp h') := rfl

abbrev Ctx (n : Nat) := Fin n → Word

/-- Generated Boolean judgment under the composite trailing lock word. -/
inductive Term {n} (Γ : Ctx n) (w : Word) : Type
  | lit : Bool → Term Γ w
  | var (i : Fin n) : Cell (Γ i) w → Term Γ w
  | neg : Term Γ w → Term Γ w

namespace Term
variable {n m l : Nat} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx l} {u v w : Word}

def key (k : Cell u v) : Term Γ u → Term Γ v
  | .lit b => .lit b
  | .var i h => .var i (h.comp k)
  | .neg t => .neg (t.key k)

@[simp] theorem key_id (t : Term Γ w) : t.key (.id w) = t := by
  induction t with
  | lit => rfl
  | var => rfl
  | neg t ih => exact congrArg neg ih

@[simp] theorem key_comp (t : Term Γ u) (k : Cell u v) (h : Cell v w) :
    (t.key k).key h = t.key (k.comp h) := by
  induction t with
  | lit => rfl
  | var => rfl
  | neg t ih => exact congrArg neg ih

end Term

/-- An admissible substitution supplies each declaration under its own locks. -/
abbrev Sub {n m} (Δ : Ctx m) (Γ : Ctx n) := (i : Fin n) → Term Δ (Γ i)

namespace Term
variable {n m l : Nat} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx l} {u v w : Word}

def subst (σ : Sub Δ Γ) : Term Γ w → Term Δ w
  | .lit b => .lit b
  | .var i k => (σ i).key k
  | .neg t => .neg (t.subst σ)

@[simp] theorem subst_key (t : Term Γ u) (σ : Sub Δ Γ) (k : Cell u v) :
    (t.key k).subst σ = (t.subst σ).key k := by
  induction t with
  | lit => rfl
  | var => exact (key_comp _ _ _).symm
  | neg t ih => exact congrArg neg ih

@[simp] theorem subst_comp (t : Term Γ w) (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
  induction t with
  | lit => rfl
  | var => exact subst_key _ _ _
  | neg t ih => exact congrArg neg ih

@[simp] theorem subst_id (t : Term Γ w) :
    t.subst (fun i => .var i (.id (Γ i))) = t := by
  induction t with
  | lit => rfl
  | var => rfl
  | neg t ih => exact congrArg neg ih
end Term

/-- A concrete lock-indexed environment contains exactly the accessible variables.
Keys pull environments back, contravariantly to their word cells. -/
abbrev Env {n} (Γ : Ctx n) (w : Word) := (i : Fin n) → Cell (Γ i) w → Bool

def Env.key {n} {Γ : Ctx n} {u v} (k : Cell u v) (ρ : Env Γ v) : Env Γ u :=
  fun i h => ρ i (h.comp k)

@[simp] theorem Env.key_id {n} {Γ : Ctx n} {w} (ρ : Env Γ w) :
    ρ.key (.id w) = ρ := rfl

@[simp] theorem Env.key_comp {n} {Γ : Ctx n} {u v w}
    (ρ : Env Γ w) (k : Cell u v) (h : Cell v w) :
    (ρ.key h).key k = ρ.key (k.comp h) := rfl

namespace Term
variable {n m : Nat} {Γ : Ctx n} {Δ : Ctx m} {u v w : Word}
def eval : Term Γ w → Env Γ w → Bool
  | .lit b, _ => b
  | .var i k, ρ => ρ i k
  | .neg t, ρ => !(t.eval ρ)

@[simp] theorem eval_key (t : Term Γ u) (k : Cell u v) (ρ : Env Γ v) :
    (t.key k).eval ρ = t.eval (ρ.key k) := by
  induction t with
  | lit => rfl
  | var => rfl
  | neg t ih => exact congrArg Bool.not ih
end Term

def Sub.eval {n m} {Γ : Ctx n} {Δ : Ctx m} (σ : Sub Δ Γ) {w}
    (ρ : Env Δ w) : Env Γ w := fun i k => ((σ i).key k).eval ρ

@[simp] theorem Term.eval_subst {n m} {Γ : Ctx n} {Δ : Ctx m} {w}
    (t : Term Γ w) (σ : Sub Δ Γ) (ρ : Env Δ w) :
    (t.subst σ).eval ρ = t.eval (σ.eval ρ) := by
  induction t with
  | lit => rfl
  | var => rfl
  | neg t ih => exact congrArg Bool.not ih

theorem Sub.eval_key {n m} {Γ : Ctx n} {Δ : Ctx m} {u v}
    (σ : Sub Δ Γ) (k : Cell u v) (ρ : Env Δ v) :
    (σ.eval ρ).key k = σ.eval (ρ.key k) := by
  funext i h
  change ((σ i).key (h.comp k)).eval ρ = ((σ i).key h).eval (ρ.key k)
  rw [← Term.key_comp, Term.eval_key]

theorem Sub.eval_comp {n m l} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx l}
    (σ : Sub Δ Γ) (τ : Sub Θ Δ) {w} (ρ : Env Θ w) :
    Sub.eval (fun i => (σ i).subst τ : Sub Θ Γ) ρ = σ.eval (τ.eval ρ) := by
  funext i k
  change (((σ i).subst τ).key k).eval ρ = ((σ i).key k).eval (τ.eval ρ)
  rw [← Term.subst_key, Term.eval_subst]

/-- Generated identity introduction, indexed by both endpoints. There is no
conversion rule reflecting equality from a single environment. -/
inductive IdTerm {n} {Γ : Ctx n} {w} : Term Γ w → Term Γ w → Type
  | refl (t) : IdTerm t t

theorem IdTerm.eval {n} {Γ : Ctx n} {w} {s t : Term Γ w}
    (p : IdTerm s t) (ρ : Env Γ w) : s.eval ρ = t.eval ρ := by
  cases p
  rfl

def IdTerm.subst {n m} {Γ : Ctx n} {Δ : Ctx m} {w} {s t : Term Γ w}
    (p : IdTerm s t) (σ : Sub Δ Γ) : IdTerm (s.subst σ) (t.subst σ) :=
  by cases p; exact .refl _

/-- Type interpretation is an actual family over locked environments. It can
have empty fibers when its two endpoint terms disagree. -/
def IdFamily {n} {Γ : Ctx n} {w} (s t : Term Γ w) : Env Γ w → Type :=
  fun ρ => PLift (s.eval ρ = t.eval ρ)

theorem IdFamily.subst {n m} {Γ : Ctx n} {Δ : Ctx m} {w}
    (s t : Term Γ w) (σ : Sub Δ Γ) :
    IdFamily (s.subst σ) (t.subst σ) = fun ρ => IdFamily s t (σ.eval ρ) := by
  funext ρ
  simp only [IdFamily, Term.eval_subst]

theorem IdFamily.key {n} {Γ : Ctx n} {u v}
    (s t : Term Γ u) (k : Cell u v) :
    IdFamily (s.key k) (t.key k) = fun ρ => IdFamily s t (ρ.key k) := by
  funext ρ
  simp only [IdFamily, Term.eval_key]

def IdTerm.key {n} {Γ : Ctx n} {u v} {s t : Term Γ u}
    (p : IdTerm s t) (k : Cell u v) : IdTerm (s.key k) (t.key k) := by
  cases p
  exact .refl _

/-- The selected dependent sum Σ z : Bool, Id Bool z z. -/
structure Selected {n} (Γ : Ctx n) (w : Word) where
  value : Term Γ w
  witness : IdTerm value value

abbrev Observation := (b : Bool) × PLift (b = b)

def Selected.eval {n} {Γ : Ctx n} {w} (t : Selected Γ w) (ρ : Env Γ w) :
    Observation := ⟨t.value.eval ρ, ⟨t.witness.eval ρ⟩⟩

def Selected.subst {n m} {Γ : Ctx n} {Δ : Ctx m} {w}
    (t : Selected Γ w) (σ : Sub Δ Γ) : Selected Δ w :=
  ⟨t.value.subst σ, t.witness.subst σ⟩

def Selected.key {n} {Γ : Ctx n} {u v}
    (t : Selected Γ u) (k : Cell u v) : Selected Γ v :=
  ⟨t.value.key k, t.witness.key k⟩

theorem Selected.eval_key {n} {Γ : Ctx n} {u v}
    (t : Selected Γ u) (k : Cell u v) (ρ : Env Γ v) :
    (t.key k).eval ρ = t.eval (ρ.key k) :=
  congrArg (fun b : Bool => (⟨b, ⟨rfl⟩⟩ : Observation)) (Term.eval_key _ _ _)

theorem Selected.subst_comp {n m l} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx l}
    {w} (t : Selected Γ w) (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
  rcases t with ⟨t, p⟩
  cases p
  exact congrArg (fun t => (⟨t, .refl t⟩ : Selected Θ w)) (Term.subst_comp t σ τ)

theorem Selected.subst_id {n} {Γ : Ctx n} {w} (t : Selected Γ w) :
    t.subst (fun i => .var i (.id (Γ i))) = t := by
  rcases t with ⟨t, p⟩
  cases p
  exact congrArg (fun t => (⟨t, .refl t⟩ : Selected Γ w)) (Term.subst_id t)

theorem Selected.key_comp {n} {Γ : Ctx n} {u v w}
    (t : Selected Γ u) (k : Cell u v) (h : Cell v w) :
    (t.key k).key h = t.key (k.comp h) := by
  rcases t with ⟨t, p⟩
  cases p
  exact congrArg (fun t => (⟨t, .refl t⟩ : Selected Γ w)) (Term.key_comp t k h)

theorem Selected.subst_key {n m} {Γ : Ctx n} {Δ : Ctx m} {u v}
    (t : Selected Γ u) (σ : Sub Δ Γ) (k : Cell u v) :
    (t.key k).subst σ = (t.subst σ).key k := by
  rcases t with ⟨t, p⟩
  cases p
  exact congrArg (fun t => (⟨t, .refl t⟩ : Selected Δ v)) (Term.subst_key t σ k)

/-- Exact equality of dependent packages, not just equality of first projections. -/
theorem Selected.eval_subst {n m} {Γ : Ctx n} {Δ : Ctx m} {w}
    (t : Selected Γ w) (σ : Sub Δ Γ) (ρ : Env Δ w) :
    (t.subst σ).eval ρ = t.eval (σ.eval ρ) := by
  exact congrArg (fun b : Bool => (⟨b, ⟨rfl⟩⟩ : Observation))
    (Term.eval_subst t.value σ ρ)

theorem Selected.eval_two_substitutions {n m l} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx l}
    {w} (t : Selected Γ w) (σ : Sub Δ Γ) (τ : Sub Θ Δ) (ρ : Env Θ w) :
    ((t.subst σ).subst τ).eval ρ =
      (t.subst (fun i => (σ i).subst τ)).eval ρ := by
  rw [Selected.eval_subst, Selected.eval_subst, Selected.eval_subst, Sub.eval_comp]

end SquareKit.Internal.ModalAccess
