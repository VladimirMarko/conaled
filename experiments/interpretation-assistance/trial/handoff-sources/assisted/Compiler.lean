import Std

/-!
# Compiling a typed lambda calculus to certified categorical operations

An original, small reconstruction inspired by Conal Elliott's
*Compiling to Categories* (ICFP 2017), with semantic obligations explicit.
Lean 4.35.0; no Mathlib, `sorry`, or user-declared axioms.

The compiler is defined for any interpretation of the categorical signature.
Its correctness theorem is conditional on the separately supplied `Sound`
interface. In particular, raw syntax is not claimed to satisfy category laws
by syntactic equality. Those laws hold under semantic equivalence.
-/

namespace CategoricalCompiler

inductive Ty where
  | base | unit
  | prod : Ty → Ty → Ty
  | arr : Ty → Ty → Ty
  | sum : Ty → Ty → Ty
  deriving DecidableEq, Repr

@[reducible] def Val (B : Type) : Ty → Type
  | .base => B
  | .unit => Unit
  | .prod a b => Val B a × Val B b
  | .arr a b => Val B a → Val B b
  | .sum a b => Sum (Val B a) (Val B b)

abbrev Ctx := List Ty

/-- The newest variable is the right component of a context product. -/
abbrev context : Ctx → Ty
  | [] => .unit
  | a :: Γ => .prod (context Γ) a

inductive Var : Ctx → Ty → Type where
  | here : Var (a :: Γ) a
  | there : Var Γ a → Var (b :: Γ) a

inductive Term (Prim : Ty → Ty → Type) : Ctx → Ty → Type where
  | var : Var Γ a → Term Prim Γ a
  | unit : Term Prim Γ .unit
  | pair : Term Prim Γ a → Term Prim Γ b → Term Prim Γ (.prod a b)
  | fst : Term Prim Γ (.prod a b) → Term Prim Γ a
  | snd : Term Prim Γ (.prod a b) → Term Prim Γ b
  | lam : Term Prim (a :: Γ) b → Term Prim Γ (.arr a b)
  | app : Term Prim Γ (.arr a b) → Term Prim Γ a → Term Prim Γ b
  | letE : Term Prim Γ a → Term Prim (a :: Γ) b → Term Prim Γ b
  | inl : Term Prim Γ a → Term Prim Γ (.sum a b)
  | inr : Term Prim Γ b → Term Prim Γ (.sum a b)
  | caseE : Term Prim Γ (.sum a b) → Term Prim (a :: Γ) c →
      Term Prim (b :: Γ) c → Term Prim Γ c
  | prim : Prim a b → Term Prim Γ a → Term Prim Γ b

def lookup {B : Type} : Var Γ a → Val B (context Γ) → Val B a
  | .here, ρ => ρ.2
  | .there v, ρ => lookup v ρ.1

def eval {B : Type} {Prim : Ty → Ty → Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) :
    Term Prim Γ a → Val B (context Γ) → Val B a
  | .var v, ρ => lookup v ρ
  | .unit, _ => ()
  | .pair t u, ρ => (eval meaning t ρ, eval meaning u ρ)
  | .fst t, ρ => (eval meaning t ρ).1
  | .snd t, ρ => (eval meaning t ρ).2
  | .lam t, ρ => fun x => eval meaning t (ρ, x)
  | .app t u, ρ => eval meaning t ρ (eval meaning u ρ)
  | .letE t u, ρ => eval meaning u (ρ, eval meaning t ρ)
  | .inl t, ρ => .inl (eval meaning t ρ)
  | .inr t, ρ => .inr (eval meaning t ρ)
  | .caseE s l r, ρ =>
      match eval meaning s ρ with
      | .inl x => eval meaning l (ρ, x)
      | .inr y => eval meaning r (ρ, y)
  | .prim p t, ρ => meaning p (eval meaning t ρ)

/-- Operations, deliberately separated from their semantic laws. -/
structure Target (Prim : Ty → Ty → Type) where
  Hom : Ty → Ty → Type
  ident : {a : Ty} → Hom a a
  comp : {a b c : Ty} → Hom b c → Hom a b → Hom a c
  terminal : {a : Ty} → Hom a .unit
  fst : {a b : Ty} → Hom (.prod a b) a
  snd : {a b : Ty} → Hom (.prod a b) b
  pair : {a b c : Ty} → Hom a b → Hom a c → Hom a (.prod b c)
  curry : {a b c : Ty} → Hom (.prod a b) c → Hom a (.arr b c)
  apply : {a b : Ty} → Hom (.prod (.arr a b) a) b
  inl : {a b : Ty} → Hom a (.sum a b)
  inr : {a b : Ty} → Hom b (.sum a b)
  copair : {a b c : Ty} → Hom a c → Hom b c → Hom (.sum a b) c
  dist : {a b c : Ty} → Hom (.prod a (.sum b c)) (.sum (.prod a b) (.prod a c))
  primitive : {a b : Ty} → Prim a b → Hom a b

def compileVar (K : Target Prim) : Var Γ a → K.Hom (context Γ) a
  | .here => K.snd
  | .there v => K.comp (compileVar K v) K.fst

/-- The ordinary CCC translation, now a reusable target-parametric function. -/
def compile (K : Target Prim) : Term Prim Γ a → K.Hom (context Γ) a
  | .var v => compileVar K v
  | .unit => K.terminal
  | .pair t u => K.pair (compile K t) (compile K u)
  | .fst t => K.comp K.fst (compile K t)
  | .snd t => K.comp K.snd (compile K t)
  | .lam t => K.curry (compile K t)
  | .app t u => K.comp K.apply (K.pair (compile K t) (compile K u))
  | .letE t u => K.comp (compile K u) (K.pair K.ident (compile K t))
  | .inl t => K.comp K.inl (compile K t)
  | .inr t => K.comp K.inr (compile K t)
  | .caseE s l r => K.comp (K.copair (compile K l) (compile K r))
      (K.comp K.dist (K.pair K.ident (compile K s)))
  | .prim p t => K.comp (K.primitive p) (compile K t)

def distribute : X × Sum Y Z → Sum (X × Y) (X × Z)
  | (x, .inl y) => .inl (x, y)
  | (x, .inr z) => .inr (x, z)

/-- A semantic interpretation of a backend. Every field is a local square.
This is a Set-valued soundness interface, not an assertion that every CCC
has a faithful or closed interpretation in Set. -/
structure Sound (B : Type) {Prim : Ty → Ty → Type} (K : Target Prim)
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) where
  denote : {a b : Ty} → K.Hom a b → Val B a → Val B b
  ident : ∀ {a} (x : Val B a), denote K.ident x = x
  comp : ∀ {a b c} (g : K.Hom b c) (f : K.Hom a b) x,
    denote (K.comp g f) x = denote g (denote f x)
  terminal : ∀ {a} (x : Val B a), denote K.terminal x = ()
  fst : ∀ {a b} (x : Val B (.prod a b)), denote K.fst x = x.1
  snd : ∀ {a b} (x : Val B (.prod a b)), denote K.snd x = x.2
  pair : ∀ {a b c} (f : K.Hom a b) (g : K.Hom a c) x,
    denote (K.pair f g) x = (denote f x, denote g x)
  curry : ∀ {a b c} (f : K.Hom (.prod a b) c) x y,
    denote (K.curry f) x y = denote f (x, y)
  apply : ∀ {a b} (x : Val B (.prod (.arr a b) a)), denote K.apply x = x.1 x.2
  inl : ∀ {a b} (x : Val B a), denote (@Target.inl _ K a b) x = .inl x
  inr : ∀ {a b} (x : Val B b), denote (@Target.inr _ K a b) x = .inr x
  copair : ∀ {a b c} (f : K.Hom a c) (g : K.Hom b c) x,
    denote (K.copair f g) x = Sum.elim (denote f) (denote g) x
  dist : ∀ {a b c} (x : Val B (.prod a (.sum b c))), denote K.dist x = distribute x
  primitive : ∀ {a b} (p : Prim a b) x, denote (K.primitive p) x = meaning p x

theorem compileVar_sound {B : Type} {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val B a → Val B b}
    (K : Target Prim) (S : Sound B K meaning)
    (v : Var Γ a) (ρ : Val B (context Γ)) :
    S.denote (compileVar K v) ρ = lookup v ρ := by
  induction v with
  | here => exact S.snd ρ
  | there v ih =>
    simp only [compileVar, lookup, S.comp, S.fst]
    exact ih ρ.1

/-- The fundamental theorem: structural compilation preserves meaning. -/
theorem compile_sound {B : Type} {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val B a → Val B b}
    (K : Target Prim) (S : Sound B K meaning)
    (t : Term Prim Γ a) (ρ : Val B (context Γ)) :
    S.denote (compile K t) ρ = eval meaning t ρ := by
  induction t with
  | var v => exact compileVar_sound K S v ρ
  | unit => exact S.terminal ρ
  | pair t u it iu => simp only [compile, eval, S.pair, it, iu]
  | fst t it => simp only [compile, eval, S.comp, S.fst, it]
  | snd t it => simp only [compile, eval, S.comp, S.snd, it]
  | lam t it =>
    funext x
    simp only [compile, eval, S.curry, it]
  | app t u it iu => simp only [compile, eval, S.comp, S.pair, S.apply, it, iu]
  | letE t u it iu => simp only [compile, eval, S.comp, S.pair, S.ident, it, iu]
  | inl t it => simp only [compile, eval, S.comp, S.inl, it]
  | inr t it => simp only [compile, eval, S.comp, S.inr, it]
  | caseE s l r is il ir =>
    simp only [compile, S.comp, S.copair, S.dist, S.pair, S.ident, is, eval]
    cases h : eval meaning s ρ with
    | inl x => exact il (ρ, x)
    | inr y => exact ir (ρ, y)
  | prim p t it => simp only [compile, eval, S.comp, S.primitive, it]

structure Certified {B : Type} {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val B a → Val B b}
    (K : Target Prim) (S : Sound B K meaning)
    {a b : Ty} (spec : Val B a → Val B b) where
  code : K.Hom a b
  correct : ∀ x, S.denote code x = spec x

/-- Compilation returns a program and its semantic certificate together. -/
def compileCertified {B : Type} {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val B a → Val B b}
    (K : Target Prim) (S : Sound B K meaning)
    (t : Term Prim Γ a) : Certified K S (eval meaning t) :=
  ⟨compile K t, compile_sound K S t⟩

/-- A free *raw* categorical IR, intentionally not quotiented by laws. -/
inductive Code (Prim : Ty → Ty → Type) : Ty → Ty → Type where
  | ident : Code Prim a a
  | comp : Code Prim b c → Code Prim a b → Code Prim a c
  | terminal : Code Prim a .unit
  | fst : Code Prim (.prod a b) a
  | snd : Code Prim (.prod a b) b
  | pair : Code Prim a b → Code Prim a c → Code Prim a (.prod b c)
  | curry : Code Prim (.prod a b) c → Code Prim a (.arr b c)
  | apply : Code Prim (.prod (.arr a b) a) b
  | inl : Code Prim a (.sum a b)
  | inr : Code Prim b (.sum a b)
  | copair : Code Prim a c → Code Prim b c → Code Prim (.sum a b) c
  | dist : Code Prim (.prod a (.sum b c)) (.sum (.prod a b) (.prod a c))
  | primitive : Prim a b → Code Prim a b

def rawTarget (Prim : Ty → Ty → Type) : Target Prim where
  Hom := Code Prim
  ident := .ident
  comp := .comp
  terminal := .terminal
  fst := .fst
  snd := .snd
  pair := .pair
  curry := .curry
  apply := .apply
  inl := .inl
  inr := .inr
  copair := .copair
  dist := .dist
  primitive := .primitive

def run {B : Type} (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) :
    Code Prim a b → Val B a → Val B b
  | .ident, x => x
  | .comp g f, x => run meaning g (run meaning f x)
  | .terminal, _ => ()
  | .fst, x => x.1
  | .snd, x => x.2
  | .pair f g, x => (run meaning f x, run meaning g x)
  | .curry f, x => fun y => run meaning f (x, y)
  | .apply, x => x.1 x.2
  | .inl, x => .inl x
  | .inr, x => .inr x
  | .copair f g, x => Sum.elim (run meaning f) (run meaning g) x
  | .dist, x => distribute x
  | .primitive p, x => meaning p x

def rawSound {B : Type} (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) :
    Sound B (rawTarget Prim) meaning where
  denote := run meaning
  ident := fun _ => rfl
  comp := fun _ _ _ => rfl
  terminal := fun _ => rfl
  fst := fun _ => rfl
  snd := fun _ => rfl
  pair := fun _ _ _ => rfl
  curry := fun _ _ _ => rfl
  apply := fun _ => rfl
  inl := fun _ => rfl
  inr := fun _ => rfl
  copair := fun _ _ _ => rfl
  dist := fun _ => rfl
  primitive := fun _ _ => rfl

/-- Observational equality is the right equality for raw syntax. -/
def Equivalent {B : Type} (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (f g : Code Prim a b) : Prop := ∀ x, run meaning f x = run meaning g x

theorem category_assoc {B : Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (h : Code Prim c d) (g : Code Prim b c) (f : Code Prim a b) :
    Equivalent meaning (.comp (.comp h g) f) (.comp h (.comp g f)) := fun _ => rfl

theorem product_beta {B : Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (f : Code Prim a b) (g : Code Prim a c) :
    Equivalent meaning (.comp .fst (.pair f g)) f := fun _ => rfl

theorem product_eta {B : Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (f : Code Prim a (.prod b c)) :
    Equivalent meaning (.pair (.comp .fst f) (.comp .snd f)) f := fun _ => rfl

/-- A certified optimization eliminating a closure immediately applied. -/
theorem closed_beta {B : Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (f : Code Prim (.prod a b) c) (g : Code Prim a b) :
    Equivalent meaning (.comp .apply (.pair (.curry f) g))
      (.comp f (.pair .ident g)) := fun _ => rfl

theorem closed_eta {B : Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (f : Code Prim a (.arr b c)) :
    Equivalent meaning (.curry (.comp .apply (.pair (.comp f .fst) .snd))) f :=
  fun _ => rfl

/-! A concrete numerical signature and examples. -/

inductive Arithmetic : Ty → Ty → Type where
  | lit : Nat → Arithmetic .unit .base
  | add : Arithmetic (.prod .base .base) .base
  | mul : Arithmetic (.prod .base .base) .base

def arithmeticMeaning : Arithmetic a b → Val Nat a → Val Nat b
  | .lit n, _ => n
  | .add, (x, y) => x + y
  | .mul, (x, y) => x * y

abbrev N : Ty := .base

def square : Term Arithmetic [N] N :=
  .prim .mul (.pair (.var .here) (.var .here))

def magSqr : Term Arithmetic [.prod N N] N :=
  let x : Term Arithmetic [.prod N N] N := .fst (.var .here)
  let y : Term Arithmetic [.prod N N] N := .snd (.var .here)
  .prim .add (.pair (.prim .mul (.pair x x)) (.prim .mul (.pair y y)))

def higherOrder : Term Arithmetic [.arr N N, N] N :=
  .app (.var .here) (.var (.there .here))

def lambdaExample : Term Arithmetic [N] (.arr N N) :=
  .lam (.prim .add (.pair (.var (.there .here)) (.var .here)))

/-- A sum elimination whose branches both capture the outer numeric value. -/
def capturedCase : Term Arithmetic [.sum N N, N] N :=
  .caseE (.var .here)
    (.prim .add (.pair (.var (.there (.there .here))) (.var .here)))
    (.prim .mul (.pair (.var (.there (.there .here))) (.var .here)))

def letExample : Term Arithmetic [N] N :=
  .letE square (.prim .add (.pair (.var .here) (.var .here)))

example : run arithmeticMeaning (compile (rawTarget Arithmetic) square) ((), 7) = 49 := rfl
theorem magSqr_correct (x y : Nat) :
    run arithmeticMeaning (compile (rawTarget Arithmetic) magSqr) ((), (x, y)) =
      x * x + y * y := rfl
example : run arithmeticMeaning (compile (rawTarget Arithmetic) higherOrder)
    (((), 7), fun n => n + 2) = 9 := rfl
example : run arithmeticMeaning (compile (rawTarget Arithmetic) lambdaExample) ((), 7) 5 = 12 := rfl
example : run arithmeticMeaning (compile (rawTarget Arithmetic) capturedCase)
    (((), 7), .inl 3) = 10 := rfl
example : run arithmeticMeaning (compile (rawTarget Arithmetic) capturedCase)
    (((), 7), .inr 3) = 21 := rfl
example : run arithmeticMeaning (compile (rawTarget Arithmetic) letExample) ((), 7) = 98 := rfl

end CategoricalCompiler
