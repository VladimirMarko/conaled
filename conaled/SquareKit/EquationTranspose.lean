import Squares

/-! Indexed equation transposition for a binding-free, typed expression calculus.
Constructor and observer parameter blocks exchange positions in every body.
The syntax has no recursion or local match; primitive interpretations are total. -/
namespace SquareKit.EquationTranspose
universe u v w

inductive Slot (A B : Type u) : Type u → Type (u+1)
  | first : Slot A B A
  | second : Slot A B B

def Slot.swap : Slot A B T → Slot B A T
  | .first => .second
  | .second => .first

def Slot.env (a : A) (b : B) : Slot A B T → T
  | .first => a
  | .second => b

/-- Primitive names are syntax, separate from their interpretation. -/
inductive Expr (P : Type u → Type u → Type (u+1))
    (V : Type u → Type (u+1)) : Type u → Type (u+1)
  | var : V A → Expr P V A
  | prim : P A B → Expr P V A → Expr P V B
  | pair : Expr P V A → Expr P V B → Expr P V (A × B)
  | fst : Expr P V (A × B) → Expr P V A
  | snd : Expr P V (A × B) → Expr P V B

namespace Expr
variable {P : Type u → Type u → Type (u+1)}
variable {V W X : Type u → Type (u+1)}

def rename (r : ∀ {A}, V A → W A) : Expr P V A → Expr P W A
  | .var x => .var (r x)
  | .prim p e => .prim p (rename r e)
  | .pair e f => .pair (rename r e) (rename r f)
  | .fst e => .fst (rename r e)
  | .snd e => .snd (rename r e)

theorem rename_id (e : Expr P V A) : rename (fun x => x) e = e := by
  induction e <;> simp_all [rename]

theorem rename_comp (r : ∀ {A}, V A → W A) (s : ∀ {A}, W A → X A)
    (e : Expr P V A) : rename s (rename r e) = rename (fun x => s (r x)) e := by
  induction e <;> simp_all [rename]

def eval (m : ∀ {A B}, P A B → A → B) (ρ : ∀ {A}, V A → A) : Expr P V A → A
  | .var x => ρ x
  | .prim p e => m p (eval m ρ e)
  | .pair e f => (eval m ρ e, eval m ρ f)
  | .fst e => (eval m ρ e).1
  | .snd e => (eval m ρ e).2

theorem eval_rename (m : ∀ {A B}, P A B → A → B)
    (ρ : ∀ {A}, W A → A) (r : ∀ {A}, V A → W A) (e : Expr P V A) :
    eval m ρ (rename r e) = eval m (fun x => ρ (r x)) e := by
  induction e <;> simp_all [rename, eval]

def swap (e : Expr P (Slot A B) T) : Expr P (Slot B A) T := rename Slot.swap e

theorem swap_swap (e : Expr P (Slot A B) T) : e.swap.swap = e := by
  rw [swap, swap, rename_comp]
  have h : (fun {T} (x : Slot A B T) => x.swap.swap) = (fun {T} (x : Slot A B T) => x) := by
    funext T x; cases x <;> rfl
  rw [h, rename_id]

theorem eval_swap (m : ∀ {A B}, P A B → A → B)
    (e : Expr P (Slot A B) T) (a : A) (b : B) :
    eval m (Slot.env b a) e.swap = eval m (Slot.env a b) e := by
  rw [swap, eval_rename]
  have h : (fun {T} (x : Slot A B T) => Slot.env b a x.swap) = (fun {T} (x : Slot A B T) => Slot.env a b x) := by
    funext T x; cases x <;> rfl
  rw [h]
end Expr

/-- Indices constrain which constructors and observations can meet.
Parameter blocks may themselves contain dependent pairs or vectors. -/
structure Signature (I : Type v) where
  Constructor : I → Type w
  Observer : I → Type w
  fields : {i : I} → Constructor i → Type u
  arguments : {i : I} → Observer i → Type u
  result : {i : I} → Observer i → Type u

variable {I : Type v} {S : Signature.{u,v,w} I}
variable {P : Type u → Type u → Type (u+1)}

/-- Data declaration plus exhaustive observer definitions (columns). -/
structure DataProgram (S : Signature.{u,v,w} I) (P : Type u → Type u → Type (u+1)) where
  body : ∀ i (d : S.Observer i) (c : S.Constructor i),
    Expr P (Slot (S.fields c) (S.arguments d)) (S.result d)

/-- Codata declaration plus exhaustive constructor definitions (rows). -/
structure CodataProgram (S : Signature.{u,v,w} I) (P : Type u → Type u → Type (u+1)) where
  body : ∀ i (c : S.Constructor i) (d : S.Observer i),
    Expr P (Slot (S.arguments d) (S.fields c)) (S.result d)

def transpose (p : DataProgram S P) : CodataProgram S P :=
  ⟨fun i c d => (p.body i d c).swap⟩

def untranspose (p : CodataProgram S P) : DataProgram S P :=
  ⟨fun i d c => (p.body i c d).swap⟩

theorem untranspose_transpose (p : DataProgram S P) : untranspose (transpose p) = p := by
  cases p with
  | mk body =>
    simp only [untranspose, transpose]
    congr 1
    funext i d c
    exact Expr.swap_swap _

theorem transpose_untranspose (p : CodataProgram S P) : transpose (untranspose p) = p := by
  cases p with
  | mk body =>
    simp only [untranspose, transpose]
    congr 1
    funext i c d
    exact Expr.swap_swap _

abbrev DataValue (S : Signature.{u,v,w} I) (i : I) := (c : S.Constructor i) × S.fields c
abbrev CodataValue (S : Signature.{u,v,w} I) (i : I) :=
  (d : S.Observer i) → S.arguments d → S.result d

def DataProgram.observe (p : DataProgram S P) (m : ∀ {A B}, P A B → A → B)
    (d : S.Observer i) (x : DataValue S i) (a : S.arguments d) : S.result d :=
  (p.body i d x.1).eval m (Slot.env x.2 a)

def CodataProgram.construct (p : CodataProgram S P) (m : ∀ {A B}, P A B → A → B)
    (c : S.Constructor i) (x : S.fields c) : CodataValue S i :=
  fun d a => (p.body i c d).eval m (Slot.env a x)

/-- Equality of all selected observations, not an isomorphism of all data/codata values. -/
theorem transpose_preserves (p : DataProgram S P) (m : ∀ {A B}, P A B → A → B)
    (c : S.Constructor i) (x : S.fields c) (d : S.Observer i) (a : S.arguments d) :
    (transpose p).construct m c x d a = p.observe m d ⟨c,x⟩ a :=
  Expr.eval_swap _ _ _ _

/-- Restriction makes the extension boundary explicit: existing cells are retained. -/
def restrictConstructors (p : DataProgram S P) (C : I → Type w)
    (f : ∀ i, C i → S.Constructor i) :
    DataProgram { S with Constructor := C, fields := fun {i} c => S.fields (f i c) } P :=
  ⟨fun i d c => p.body i d (f i c)⟩

def restrictObservers (p : DataProgram S P) (D : I → Type w)
    (f : ∀ i, D i → S.Observer i) :
    DataProgram { S with
      Observer := D
      arguments := fun {i} d => S.arguments (f i d)
      result := fun {i} d => S.result (f i d) } P :=
  ⟨fun i d c => p.body i (f i d) c⟩

theorem restrict_constructor_cell (p : DataProgram S P) (C : I → Type w)
    (f : ∀ i, C i → S.Constructor i) (i) (c : C i) (d : S.Observer i) :
    (transpose (restrictConstructors p C f)).body i c d = (transpose p).body i (f i c) d := rfl

theorem restrict_observer_cell (p : DataProgram S P) (D : I → Type w)
    (f : ∀ i, D i → S.Observer i) (i) (c : S.Constructor i) (d : D i) :
    (transpose (restrictObservers p D f)).body i c d = (transpose p).body i c (f i d) := rfl
end SquareKit.EquationTranspose
