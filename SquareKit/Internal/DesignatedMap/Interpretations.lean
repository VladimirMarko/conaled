import SquareKit.Internal.DesignatedMap.Extensional
import SquareKit.GuardedTheory
import SquareKit.LocalUniverses
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! Two interpretations of the explicit map/action fragment of #366. This is
an attempted comparison at a smaller, externally indexed signature: it has no
source Π/Σ/Id binders or universe quantifier. Alongside a direct recursive
interpreter we construct Type-family comprehension; the second interpreter uses
guarded derivations. The source does not yet connect its own binders to that
comprehension. -/
namespace SquareKit.Internal.DesignatedMap
set_option backward.isDefEq.respectTransparency false
open Extensional
universe u

namespace Represented
/-- Codes are small native types; the code object lives one level higher. -/
structure Code where
  carrier : Type u

def pi (A : Code) (B : A.carrier → Code) : Code := ⟨(a : A.carrier) → (B a).carrier⟩
def sigma (A : Code) (B : A.carrier → Code) : Code := ⟨(a : A.carrier) × (B a).carrier⟩
def identity (A : Code) (a b : A.carrier) : Code := ⟨ULift (PLift (a = b))⟩

abbrev Ty (Γ : Type u) := Γ → Code.{u}
abbrev Tm {Γ : Type u} (A : Ty Γ) := (γ : Γ) → (A γ).carrier
abbrev Ext {Γ : Type u} (A : Ty Γ) := (γ : Γ) × (A γ).carrier

def reindex {Γ Δ : Type u} (A : Ty Γ) (σ : Δ → Γ) : Ty Δ := A ∘ σ

def pair {Γ Δ : Type u} {A : Ty Γ} (σ : Δ → Γ) (t : Tm (reindex A σ)) : Δ → Ext A :=
  fun δ => ⟨σ δ, t δ⟩

/-- Representing bijection, with arbitrary base maps, constructed by dependent
pair elimination. These are the elements of the pullback of the term projection. -/
def represent {Γ Δ : Type u} (A : Ty Γ) :
    (Δ → Ext A) ≃ ((σ : Δ → Γ) × Tm (reindex A σ)) :=
  SquareKit.LocalUniverses.Family.comprehensionEquiv
    (SquareKit.LocalUniverses.Family.present (fun γ => (A γ).carrier))

theorem represent_natural {Γ Δ Θ : Type u} (A : Ty Γ) (f : Δ → Ext A) (τ : Θ → Δ) :
    represent A (f ∘ τ) =
      ⟨(represent A f).1 ∘ τ, fun θ => (represent A f).2 (τ θ)⟩ := rfl

/-- The pullback universal property includes uniqueness of the mediating map. -/
theorem pair_unique {Γ Δ : Type u} {A : Ty Γ} (σ : Δ → Γ)
    (t : Tm (reindex A σ)) (f : Δ → Ext A)
    (h : represent A f = ⟨σ, t⟩) : f = pair σ t :=
  (represent A).injective h
/-- Closure under Σ and native Id reconstructs the extensional fiber's carrier.
The map keeps the selected preimage. It cannot retain higher identity labels. -/
def fiberCode (A B : Code) (f : A.carrier → B.carrier) (b : B.carrier) : Code :=
  sigma A (fun a => identity B (f a) b)

def fiberCodeEquiv (A B : Code) (f : A.carrier → B.carrier) (b : B.carrier) :
    (fiberCode A B f b).carrier ≃ Extensional.Fiber f b where
  toFun a := ⟨a.1, a.2.down.down⟩
  invFun a := ⟨a.val, ⟨⟨a.property⟩⟩⟩
  left_inv a := by rcases a with ⟨a, ⟨⟨p⟩⟩⟩; rfl
  right_inv a := by cases a; rfl

/-- Dependent application for the native code operation. This is semantic
closure, not formation or elimination in an object-language universe. -/
def applyPi {A : Code} {B : A.carrier → Code} (f : (pi A B).carrier)
    (a : A.carrier) : (B a).carrier := f a

end Represented

namespace ActionSource
inductive Kind where | map | cone
inductive Expr (V : Kind → Type) : Kind → Type where
  | var {s} : V s → Expr V s
  | comp : Expr V .map → Expr V .map → Expr V .map
  | post : Expr V .map → Expr V .cone → Expr V .cone

def Expr.subst {V W : Kind → Type} (σ : ∀ s, V s → Expr W s) :
    {s : Kind} → Expr V s → Expr W s
  | _, .var v => σ _ v
  | _, .comp g f => .comp (g.subst σ) (f.subst σ)
  | _, .post h c => .post (h.subst σ) (c.subst σ)

inductive Equal {V : Kind → Type} : {s : Kind} → Expr V s → Expr V s → Type where
  | refl (t : Expr V s) : Equal t t
  | symm : Equal s t → Equal t s
  | trans : Equal r s → Equal s t → Equal r t
  | postComp (g f : Expr V .map) (c : Expr V .cone) :
      Equal (.post g (.post f c)) (.post (.comp g f) c)

variable {N L R Z : Type u} (north : N → L) (west : N → R)
def Value : Kind → Type u
  | .map => Z → Z
  | .cone => Cocone north west Z

/-- Direct interpretation of local source operations. No guarded model or
soundness theorem occurs in this definition or its structural proofs. -/
def direct {V : Kind → Type} (ρ : ∀ s, V s → Value (Z := Z) north west s) :
    {s : Kind} → Expr V s → Value (Z := Z) north west s
  | _, .var v => ρ _ v
  | _, .comp g f => direct ρ g ∘ direct ρ f
  | _, .post h c => Cocone.post (direct ρ h) (direct ρ c)

variable {north west}
theorem direct_subst {V W : Kind → Type}
    (ρ : ∀ s, W s → Value (Z := Z) north west s) (σ : ∀ s, V s → Expr W s)
    {s} (t : Expr V s) :
    direct north west ρ (t.subst σ) = direct north west (fun s v => direct north west ρ (σ s v)) t := by
  induction t with
  | var => rfl
  | comp g f ig iff => simp only [Expr.subst, direct, ig, iff]
  | post h c ih ic => simp only [Expr.subst, direct, ih, ic]

theorem direct_twice {V W X : Kind → Type}
    (ρ : ∀ s, X s → Value (Z := Z) north west s)
    (σ : ∀ s, V s → Expr W s) (τ : ∀ s, W s → Expr X s)
    {s} (t : Expr V s) :
    direct north west ρ ((t.subst σ).subst τ) =
      direct north west (fun s v => direct north west ρ ((σ s v).subst τ)) t := by
  rw [direct_subst, direct_subst]
  congr 1
  funext s v
  exact (direct_subst ρ τ (σ s v)).symm

theorem direct_sound {V : Kind → Type}
    (ρ : ∀ s, V s → Value (Z := Z) north west s) {s} {a b : Expr V s}
    (d : Equal a b) : direct north west ρ a = direct north west ρ b := by
  induction d with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | postComp g f c => exact Cocone.post_comp _ _ _


end ActionSource

namespace GuardedAction
open GuardedTheory ActionSource
inductive Op where | comp | post
inductive Pred where | map | cone

abbrev signature : Signature where
  Operation := Op
  arity _ := 2
  Predicate := Pred
  arguments _ := 1

abbrev binary (op : Op) (a b : Term signature V) : Term signature V := .app op ![a,b]
abbrev unary (p : Pred) (a : Term signature V) : Atom signature V := .pred p ![a]

abbrev postCompRule : Rule signature where
  parameterCount := 3
  hypotheses := 3
  premise := ![unary .map (.var 0), unary .map (.var 1), unary .cone (.var 2)]
  conclusion := .eq (binary .post (.var 0) (binary .post (.var 1) (.var 2)))
    (binary .post (binary .comp (.var 0) (.var 1)) (.var 2))

abbrev theory : Theory signature where
  Axiom := Unit
  rule _ := postCompRule

inductive Value {N L R Z : Type u} (north : N → L) (west : N → R) where
  | map : (Z → Z) → Value north west
  | cone : Cocone north west Z → Value north west
  | invalid : Value north west

variable {N L R Z : Type u} (north : N → L) (west : N → R)
def operate : Op → Value (Z := Z) north west → Value (Z := Z) north west → Value (Z := Z) north west
  | .comp, .map g, .map f => .map (g ∘ f)
  | .post, .map h, .cone c => .cone (c.post h)
  | _, _, _ => .invalid

def holds : Pred → Value (Z := Z) north west → Prop
  | .map, .map _ => True
  | .cone, .cone _ => True
  | _, _ => False

abbrev algebra : Algebra signature where
  Carrier := Value (Z := Z) north west
  operation op a := operate north west op (a 0) (a 1)
  predicate p a := holds north west p (a 0)

theorem rule_valid : Satisfies (algebra (Z := Z) north west) postCompRule := by
  intro ρ h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp [postCompRule, unary, Atom.eval, Term.eval, algebra, holds] at h0 h1 h2
  generalize e0 : ρ 0 = v0 at *
  generalize e1 : ρ 1 = v1 at *
  generalize e2 : ρ 2 = v2 at *
  cases v0 <;> dsimp only at h0
  cases v1 <;> dsimp only at h1
  cases v2 <;> dsimp only at h2
  simp only [postCompRule, Atom.eval, Term.eval, FinitaryTerm.fold, algebra,
    binary, Matrix.cons_val_zero, Matrix.cons_val_one, e0, e1, e2, operate]
  exact congrArg Value.cone (Cocone.post_comp _ _ _)

abbrev model : Model theory := ⟨algebra (Z := Z) north west, fun _ => rule_valid (Z := Z) north west⟩

def inject {s} : ActionSource.Value (Z := Z) north west s → Value (Z := Z) north west
  := match s with | .map => .map | .cone => .cone

def encode {V : Kind → Type} : {s : Kind} → Expr V s → Term signature (Sigma V)
  | _, .var v => .var ⟨_,v⟩
  | _, .comp g f => binary .comp (encode g) (encode f)
  | _, .post h c => binary .post (encode h) (encode c)

theorem encode_eval {V : Kind → Type}
    (ρ : ∀ s, V s → ActionSource.Value (Z := Z) north west s) {s} (t : Expr V s) :
    (encode t).eval (algebra north west) (fun v => inject north west (ρ v.1 v.2)) =
      inject north west (ActionSource.direct north west ρ t) := by
  induction t with
  | var => rfl
  | comp g f ihg ihf =>
    simp only [encode, binary, Term.eval, FinitaryTerm.fold] at *
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [ihg, ihf]
    rfl
  | post h c ihh ihc =>
    simp only [encode, binary, Term.eval, FinitaryTerm.fold] at *
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [ihh, ihc]
    rfl

/-- A genuine guarded derivation of the local computation, from typed guards. -/
def postCompDerivation : Derivation theory (List.ofFn postCompRule.premise)
    postCompRule.conclusion := by
  have d := Derivation.rule (T := theory) () Term.var
    (fun i => Derivation.hypothesis (List.mem_ofFn.mpr ⟨i,rfl⟩))
  simpa only [Atom.subst_id, theory] using d

/-- The guarded route invokes engine soundness, independently of direct_sound. -/
theorem guarded_sound (g f : Z → Z) (c : Cocone north west Z) :
    (c.post f).post g = c.post (g ∘ f) := by
  have h := postCompDerivation.sound (model north west)
    ![Value.map g, Value.map f, Value.cone c] (by
      intro p hp
      rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
      change Fin 3 at i
      fin_cases i <;> trivial)
  exact Value.cone.inj h

/-- Arbitrary typed source substitutions agree through the actual guarded
translation and the independent direct interpreter. -/
theorem compare_twice {V W X : Kind → Type}
    (ρ : ∀ s, X s → ActionSource.Value (Z := Z) north west s)
    (σ : ∀ s, V s → Expr W s) (τ : ∀ s, W s → Expr X s)
    {s} (t : Expr V s) :
    (encode ((t.subst σ).subst τ)).eval (algebra north west)
      (fun v => inject north west (ρ v.1 v.2)) =
    inject north west (ActionSource.direct north west
      (fun s v => ActionSource.direct north west ρ ((σ s v).subst τ)) t) := by
  rw [encode_eval, ActionSource.direct_twice]
end GuardedAction
end SquareKit.Internal.DesignatedMap
