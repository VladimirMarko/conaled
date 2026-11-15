import SquareKit.FirstOrderSubstitution
import SquareKit.STLCSubstitution

/-! Finite staged applications of supplied first-order bodies. The static phase
eliminates their binders by the existing capture-avoiding substitution. -/
namespace StaticFunction
open FirstOrderCompiler

@[reducible] def sourceTy : Ty → CategoricalCompiler.Ty
  | .base => .base
  | .unit => .unit
  | .prod a b => .prod (sourceTy a) (sourceTy b)

inductive SourcePrim (P : Ty → Ty → Type) : CategoricalCompiler.Ty → CategoricalCompiler.Ty → Type where
  | op : P a b → SourcePrim P (sourceTy a) (sourceTy b)

def encode {B : Type} : (a : Ty) → Val B a → CategoricalCompiler.Val B (sourceTy a)
  | .base, x => x
  | .unit, _ => ()
  | .prod a b, (x,y) => (encode a x,encode b y)
def decode {B : Type} : (a : Ty) → CategoricalCompiler.Val B (sourceTy a) → Val B a
  | .base, x => x
  | .unit, _ => ()
  | .prod a b, (x,y) => (decode a x,decode b y)
@[simp] theorem decode_encode {B : Type} (a : Ty) (x : Val B a) : decode a (encode a x) = x := by
  induction a with
  | base => rfl
  | unit => cases x; rfl
  | prod a b ha hb => cases x; simp [encode, decode, ha, hb]

def sourceMeaning {B : Type} (m : {a b : Ty} → P a b → Val B a → Val B b) :
    {a b : CategoricalCompiler.Ty} → SourcePrim P a b → CategoricalCompiler.Val B a → CategoricalCompiler.Val B b
  | _, _, .op (a := a) (b := b) p, x => encode b (m p (decode a x))

abbrev sourceCtx (Γ : Ctx) := Γ.map sourceTy

def encodeEnv {B : Type} : {Γ : Ctx} → Val B (context Γ) →
    CategoricalCompiler.Val B (CategoricalCompiler.context (sourceCtx Γ))
  | [], _ => ()
  | _ :: _, (ρ,x) => (encodeEnv ρ,encode _ x)
def sourceVar : Var Γ a → CategoricalCompiler.Var (sourceCtx Γ) (sourceTy a)
  | .here => .here
  | .there v => .there (sourceVar v)
theorem lookup_source {B : Type} (v : Var Γ a) (ρ : Val B (context Γ)) :
    CategoricalCompiler.lookup (sourceVar v) (encodeEnv ρ) = encode a (lookup v ρ) := by
  induction v with
  | here => rfl
  | there v ih => exact ih ρ.1

def embed : Term P Γ a → CategoricalCompiler.Term (SourcePrim P) (sourceCtx Γ) (sourceTy a)
  | .var v => .var (sourceVar v)
  | .unit => .unit
  | .pair t u => .pair (embed t) (embed u)
  | .fst t => .fst (embed t)
  | .snd t => .snd (embed t)
  | .letE t u => .letE (embed t) (embed u)
  | .prim p t => .prim (.op p) (embed t)

theorem embed_correct {B : Type} (m : {a b : Ty} → P a b → Val B a → Val B b)
    (t : Term P Γ a) (ρ : Val B (context Γ)) :
    CategoricalCompiler.eval (sourceMeaning m) (embed t) (encodeEnv ρ) = encode a (eval m t ρ) := by
  induction t with
  | var v => exact lookup_source v ρ
  | unit => rfl
  | pair t u ht hu => simp only [embed, CategoricalCompiler.eval, eval, encode, ht, hu]
  | fst t ht => exact congrArg Prod.fst (ht ρ)
  | snd t ht => exact congrArg Prod.snd (ht ρ)
  | letE t u ht hu =>
    simp only [embed, CategoricalCompiler.eval, ht]
    exact hu (ρ,eval m t ρ)
  | prim p t ht => simp only [embed, CategoricalCompiler.eval, ht, sourceMeaning, decode_encode, eval]

/-- Static bodies may mention surrounding first-order variables. Functions
cannot themselves occur in the runtime context or residual value type. -/
inductive Expr (P : Ty → Ty → Type) : Ctx → Ty → Type where
  | value : Term P Γ a → Expr P Γ a
  | apply : Term P (a :: Γ) b → Expr P Γ a → Expr P Γ b
  | pair : Expr P Γ a → Expr P Γ b → Expr P Γ (.prod a b)
  | fst : Expr P Γ (.prod a b) → Expr P Γ a
  | snd : Expr P Γ (.prod a b) → Expr P Γ b
  | mapPair : Term P (a :: Γ) b → Expr P Γ (.prod a a) → Expr P Γ (.prod b b)

namespace Expr
/-- This total structural recursion does not run an evaluator or use fuel. -/
def residual : Expr P Γ a → Term P Γ a
  | .value t => t
  | .apply body arg => Term.subst (Term.single (residual arg)) body
  | .pair t u => .pair (residual t) (residual u)
  | .fst t => .fst (residual t)
  | .snd t => .snd (residual t)
  | .mapPair body arg => .pair
      (Term.subst (Term.single (.fst (residual arg))) body)
      (Term.subst (Term.single (.snd (residual arg))) body)

def meaning {B : Type} (m : {a b : Ty} → P a b → Val B a → Val B b) :
    Expr P Γ a → Val B (context Γ) → Val B a
  | .value t, ρ => eval m t ρ
  | .apply body arg, ρ => (fun x => eval m body (ρ,x)) (meaning m arg ρ)
  | .pair t u, ρ => (meaning m t ρ,meaning m u ρ)
  | .fst t, ρ => (meaning m t ρ).1
  | .snd t, ρ => (meaning m t ρ).2
  | .mapPair body arg, ρ =>
      let f := fun x => eval m body (ρ,x)
      (f (meaning m arg ρ).1,f (meaning m arg ρ).2)

def source : Expr P Γ a → CategoricalCompiler.Term (SourcePrim P) (sourceCtx Γ) (sourceTy a)
  | .value t => embed t
  | .apply body arg => .app (.lam (embed body)) (source arg)
  | .pair t u => .pair (source t) (source u)
  | .fst t => .fst (source t)
  | .snd t => .snd (source t)
  | .mapPair body arg =>
      .app (.lam (.pair
        (.app (.var .here) (.fst (CategoricalCompiler.Term.rename (fun v => .there v) (source arg))))
        (.app (.var .here) (.snd (CategoricalCompiler.Term.rename (fun v => .there v) (source arg))))))
        (.lam (embed body))

theorem eval_weaken {B : Type} {Q : CategoricalCompiler.Ty → CategoricalCompiler.Ty → Type}
    (m : {a b : CategoricalCompiler.Ty} → Q a b → CategoricalCompiler.Val B a → CategoricalCompiler.Val B b)
    (t : CategoricalCompiler.Term Q Δ a) (ρ : CategoricalCompiler.Val B (CategoricalCompiler.context Δ))
    (x : CategoricalCompiler.Val B b) :
    CategoricalCompiler.eval m (CategoricalCompiler.Term.rename (fun v => .there v) t) (ρ,x) =
      CategoricalCompiler.eval m t ρ :=
  CategoricalCompiler.Term.eval_rename (Γ := Δ) (Δ := b :: Δ) m t
    (fun v => .there v) ρ (ρ,x) (fun _ => rfl)

theorem source_correct {B : Type} (m : {a b : Ty} → P a b → Val B a → Val B b)
    (e : Expr P Γ a) (ρ : Val B (context Γ)) :
    CategoricalCompiler.eval (sourceMeaning m) e.source (encodeEnv ρ) = encode a (e.meaning m ρ) := by
  induction e with
  | value t => exact embed_correct m t ρ
  | apply body arg ih =>
    simp only [source, CategoricalCompiler.eval, ih]
    exact embed_correct m body (ρ,arg.meaning m ρ)
  | pair t u ht hu => simp only [source, CategoricalCompiler.eval, meaning, encode, ht, hu]
  | fst t ht => exact congrArg Prod.fst (ht ρ)
  | snd t ht => exact congrArg Prod.snd (ht ρ)
  | mapPair body arg ih =>
    simp only [source, CategoricalCompiler.eval, CategoricalCompiler.lookup]
    rw [eval_weaken (b := .arr (sourceTy _) (sourceTy _)), ih]
    apply Prod.ext
    · exact embed_correct m body (ρ,(arg.meaning m ρ).1)
    · exact embed_correct m body (ρ,(arg.meaning m ρ).2)

theorem residual_correct {B : Type} (m : {a b : Ty} → P a b → Val B a → Val B b)
    (e : Expr P Γ a) (ρ : Val B (context Γ)) : eval m e.residual ρ = e.meaning m ρ := by
  induction e with
  | value t => rfl
  | apply body arg ih => simp only [residual, Term.eval_single, ih, meaning]
  | pair t u ht hu => simp only [residual, eval, ht, hu, meaning]
  | fst t ht => exact congrArg Prod.fst (ht ρ)
  | snd t ht => exact congrArg Prod.snd (ht ρ)
  | mapPair body arg ih => simp only [residual, eval, Term.eval_single, ih, meaning]

/-- Arbitrary open substitution, including lifting beneath a fresh let binder. -/
theorem residual_substitution {B : Type} (m : {a b : Ty} → P a b → Val B a → Val B b)
    (e : Expr P Γ a) (s : Term.Sub P Γ Δ) (ρ : Val B (context Γ)) (τ : Val B (context Δ))
    (h : ∀ {a} (v : Var Γ a), eval m (s v) τ = lookup v ρ) :
    eval m (Term.subst s e.residual) τ = e.meaning m ρ :=
  (Term.eval_subst m _ s ρ τ h).trans (e.residual_correct m ρ)

theorem residual_renaming {B : Type} (m : {a b : Ty} → P a b → Val B a → Val B b)
    (e : Expr P Γ a) (r : Term.Ren Γ Δ) (ρ : Val B (context Γ)) (τ : Val B (context Δ))
    (h : ∀ {a} (v : Var Γ a), lookup (r v) τ = lookup v ρ) :
    eval m (Term.rename r e.residual) τ = e.meaning m ρ :=
  (Term.eval_rename m _ r ρ τ h).trans (e.residual_correct m ρ)

end Expr
end StaticFunction
