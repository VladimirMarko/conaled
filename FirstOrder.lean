import Std

/-!
# First-order compilation needs only cartesian operations

This independent module has its own intrinsically typed source language.
Types contain a ground type, unit, and products; there are no function types,
lambda abstractions, applications, or sums. Source terms do contain variables,
pairing, projections, let bindings, and a parameterized primitive vocabulary.

The compiler requires only cartesian target operations. Local denotation laws
give a theorem for every term in every context and every environment. The
additive-map backend below is a genuine example without cartesian closure:
it preserves zero and addition, and `no_exponential` proves that an exponential
of the natural-number object by itself cannot exist in this category.

Lean 4.19.0, core/Std only; no `sorry` or user-declared axioms.
-/

namespace FirstOrderCompiler

inductive Ty where
  | base | unit
  | prod : Ty → Ty → Ty
  deriving DecidableEq, Repr

@[reducible] def Val (B : Type) : Ty → Type
  | .base => B
  | .unit => Unit
  | .prod a b => Val B a × Val B b

abbrev Ctx := List Ty

def context : Ctx → Ty
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
  | letE : Term Prim Γ a → Term Prim (a :: Γ) b → Term Prim Γ b
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
  | .letE t u, ρ => eval meaning u (ρ, eval meaning t ρ)
  | .prim p t, ρ => meaning p (eval meaning t ρ)

/-- No exponential, coproduct, or application operation is required. -/
structure Target (Prim : Ty → Ty → Type) where
  Hom : Ty → Ty → Type
  ident : {a : Ty} → Hom a a
  comp : {a b c : Ty} → Hom b c → Hom a b → Hom a c
  terminal : {a : Ty} → Hom a .unit
  fst : {a b : Ty} → Hom (.prod a b) a
  snd : {a b : Ty} → Hom (.prod a b) b
  pair : {a b c : Ty} → Hom a b → Hom a c → Hom a (.prod b c)
  primitive : {a b : Ty} → Prim a b → Hom a b

def compileVar (K : Target Prim) : Var Γ a → K.Hom (context Γ) a
  | .here => K.snd
  | .there v => K.comp (compileVar K v) K.fst

def compile (K : Target Prim) : Term Prim Γ a → K.Hom (context Γ) a
  | .var v => compileVar K v
  | .unit => K.terminal
  | .pair t u => K.pair (compile K t) (compile K u)
  | .fst t => K.comp K.fst (compile K t)
  | .snd t => K.comp K.snd (compile K t)
  | .letE t u => K.comp (compile K u) (K.pair K.ident (compile K t))
  | .prim p t => K.comp (K.primitive p) (compile K t)

/-- Local commuting-square laws, separate from the raw target operations. -/
structure Sound (B : Type) {Prim : Ty → Ty → Type} (K : Target Prim)
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) where
  denote : {a b : Ty} → K.Hom a b → Val B a → Val B b
  ident : ∀ {a : Ty} (x : Val B a), denote K.ident x = x
  comp : ∀ {a b c : Ty} (g : K.Hom b c) (f : K.Hom a b) x,
    denote (K.comp g f) x = denote g (denote f x)
  terminal : ∀ {a : Ty} (x : Val B a), denote K.terminal x = ()
  fst : ∀ {a b : Ty} (x : Val B (.prod a b)), denote K.fst x = x.1
  snd : ∀ {a b : Ty} (x : Val B (.prod a b)), denote K.snd x = x.2
  pair : ∀ {a b c : Ty} (f : K.Hom a b) (g : K.Hom a c) x,
    denote (K.pair f g) x = (denote f x, denote g x)
  primitive : ∀ {a b : Ty} (p : Prim a b) x,
    denote (K.primitive p) x = meaning p x

section Correctness

variable {B : Type} {Prim : Ty → Ty → Type}
variable {meaning : {a b : Ty} → Prim a b → Val B a → Val B b}

theorem compileVar_sound (K : Target Prim) (S : Sound B K meaning)
    (v : Var Γ a) : ∀ ρ, S.denote (compileVar K v) ρ = lookup v ρ := by
  induction v with
  | here => intro ρ; exact S.snd ρ
  | there v ih =>
    intro ρ
    simp only [compileVar, lookup, S.comp, S.fst, ih]

/-- Soundness for all source terms and all values of all free variables. -/
theorem compile_sound (K : Target Prim) (S : Sound B K meaning)
    (t : Term Prim Γ a) : ∀ ρ,
    S.denote (compile K t) ρ = eval meaning t ρ := by
  induction t with
  | var v => exact compileVar_sound K S v
  | unit => intro ρ; exact S.terminal ρ
  | pair t u it iu => intro ρ; simp only [compile, eval, S.pair, it, iu]
  | fst t it => intro ρ; simp only [compile, eval, S.comp, S.fst, it]
  | snd t it => intro ρ; simp only [compile, eval, S.comp, S.snd, it]
  | letE t u it iu =>
    intro ρ
    simp only [compile, eval, S.comp, S.pair, S.ident, it, iu]
  | prim p t it => intro ρ; simp only [compile, eval, S.comp, S.primitive, it]

structure Certified (K : Target Prim) (S : Sound B K meaning)
    {a b : Ty} (spec : Val B a → Val B b) where
  code : K.Hom a b
  correct : ∀ x, S.denote code x = spec x

def compileCertified (K : Target Prim) (S : Sound B K meaning)
    (t : Term Prim Γ a) : Certified K S (eval meaning t) :=
  ⟨compile K t, compile_sound K S t⟩

end Correctness

/-! ## A backend of additive maps over natural-number products

These are homomorphisms of additive commutative monoids, not a claimed
formalization of real vector spaces. Nonzero constants and multiplication of
two variable inputs are deliberately absent from this primitive signature.
-/

def zero : (a : Ty) → Val Nat a
  | .base => 0
  | .unit => ()
  | .prod a b => (zero a, zero b)

def add : (a : Ty) → Val Nat a → Val Nat a → Val Nat a
  | .base, x, y => x + y
  | .unit, _, _ => ()
  | .prod a b, x, y => (add a x.1 y.1, add b x.2 y.2)

structure AddMap (a b : Ty) where
  run : Val Nat a → Val Nat b
  map_zero : run (zero a) = zero b
  map_add : ∀ x y, run (add a x y) = add b (run x) (run y)

namespace AddMap

@[ext] theorem ext {f g : AddMap a b} (h : ∀ x, f.run x = g.run x) : f = g := by
  cases f with
  | mk f fz fa =>
    cases g with
    | mk g gz ga =>
      have same : f = g := funext h
      cases same
      rfl

def ident (a : Ty) : AddMap a a where
  run := id
  map_zero := rfl
  map_add := by intros; rfl

def comp (g : AddMap b c) (f : AddMap a b) : AddMap a c where
  run x := g.run (f.run x)
  map_zero := by rw [f.map_zero, g.map_zero]
  map_add := by intro x y; rw [f.map_add, g.map_add]

def terminal (a : Ty) : AddMap a .unit where
  run _ := ()
  map_zero := rfl
  map_add := by intros; rfl

def fst (a b : Ty) : AddMap (.prod a b) a where
  run x := x.1
  map_zero := rfl
  map_add := by intros; rfl

def snd (a b : Ty) : AddMap (.prod a b) b where
  run x := x.2
  map_zero := rfl
  map_add := by intros; rfl

def pair (f : AddMap a b) (g : AddMap a c) : AddMap a (.prod b c) where
  run x := (f.run x, g.run x)
  map_zero := by change (f.run (zero a), g.run (zero a)) = _; rw [f.map_zero, g.map_zero]; rfl
  map_add := by
    intro x y
    change (f.run (add a x y), g.run (add a x y)) = _
    rw [f.map_add, g.map_add]
    rfl

/-- Extensional equality yields the category and cartesian laws. -/
theorem comp_assoc (h : AddMap c d) (g : AddMap b c) (f : AddMap a b) :
    comp h (comp g f) = comp (comp h g) f := by ext x; rfl

theorem ident_comp (f : AddMap a b) : comp (ident b) f = f := by ext x; rfl
theorem comp_ident (f : AddMap a b) : comp f (ident a) = f := by ext x; rfl

theorem fst_pair (f : AddMap a b) (g : AddMap a c) :
    comp (fst b c) (pair f g) = f := by ext x; rfl

theorem snd_pair (f : AddMap a b) (g : AddMap a c) :
    comp (snd b c) (pair f g) = g := by ext x; rfl

theorem pair_fst_snd (h : AddMap a (.prod b c)) :
    pair (comp (fst b c) h) (comp (snd b c) h) = h := by
  apply AddMap.ext
  intro x
  rfl

theorem terminal_unique (f : AddMap a .unit) : f = terminal a := by
  apply AddMap.ext
  intro x
  exact Unit.ext _ _

end AddMap

inductive AddPrim : Ty → Ty → Type where
  | zero : AddPrim .unit .base
  | plus : AddPrim (.prod .base .base) .base
  | scale : Nat → AddPrim .base .base

def addMeaning : {a b : Ty} → AddPrim a b → Val Nat a → Val Nat b
  | _, _, .zero, _ => 0
  | _, _, .plus, x => x.1 + x.2
  | _, _, .scale n, x => n * x

def additivePrimitive : {a b : Ty} → AddPrim a b → AddMap a b
  | _, _, .zero =>
    { run := fun _ => 0
      map_zero := rfl
      map_add := by intros; rfl }
  | _, _, .plus =>
    { run := fun x => x.1 + x.2
      map_zero := rfl
      map_add := by
        intro x y
        change (x.1 + y.1) + (x.2 + y.2) = (x.1 + x.2) + (y.1 + y.2)
        exact Nat.add_add_add_comm x.1 y.1 x.2 y.2 }
  | _, _, .scale n =>
    { run := fun x => n * x
      map_zero := Nat.mul_zero n
      map_add := fun x y => Nat.mul_add n x y }

def additiveTarget : Target AddPrim where
  Hom := AddMap
  ident := AddMap.ident _
  comp := AddMap.comp
  terminal := AddMap.terminal _
  fst := AddMap.fst _ _
  snd := AddMap.snd _ _
  pair := AddMap.pair
  primitive := additivePrimitive

def additiveSound : Sound Nat additiveTarget addMeaning where
  denote := AddMap.run
  ident := by intros; rfl
  comp := by intros; rfl
  terminal := by intros; rfl
  fst := by intros; rfl
  snd := by intros; rfl
  pair := by intros; rfl
  primitive := by intro a b p x; cases p <;> rfl

/-- Every source term in this signature denotes an additive map, in every
context, for all valuations of its free variables. -/
theorem everyTerm_additive (t : Term AddPrim Γ a)
    (ρ σ : Val Nat (context Γ)) :
    eval addMeaning t (add (context Γ) ρ σ) =
      add a (eval addMeaning t ρ) (eval addMeaning t σ) := by
  have h (x : Val Nat (context Γ)) :
      (compile additiveTarget t).run x = eval addMeaning t x :=
    compile_sound additiveTarget additiveSound t x
  calc
    eval addMeaning t (add (context Γ) ρ σ) =
        (compile additiveTarget t).run (add (context Γ) ρ σ) := (h _).symm
    _ = add a ((compile additiveTarget t).run ρ) ((compile additiveTarget t).run σ) :=
      (compile additiveTarget t).map_add ρ σ
    _ = add a (eval addMeaning t ρ) (eval addMeaning t σ) := by rw [h, h]

theorem everyTerm_zero (t : Term AddPrim Γ a) :
    eval addMeaning t (zero (context Γ)) = zero a := by
  rw [← compile_sound additiveTarget additiveSound t (zero (context Γ))]
  exact (compile additiveTarget t).map_zero

/-! A let-bound example retains two distinct free variables under the binder:
`let z = x + y in 2*z + x`. -/

def letExample : Term AddPrim [.base, .base] .base :=
  .letE
    (.prim .plus (.pair (.var .here) (.var (.there .here))))
    (.prim .plus
      (.pair (.prim (.scale 2) (.var .here)) (.var (.there .here))))

theorem letExample_all (x y : Nat) :
    (compile additiveTarget letExample).run (((), y), x) = 2 * (x + y) + x :=
  compile_sound additiveTarget additiveSound letExample (((), y), x)

def letExampleCertified :
    Certified additiveTarget additiveSound (eval addMeaning letExample) :=
  compileCertified additiveTarget additiveSound letExample

/-! ## This target really is not cartesian closed

Every additive map from the unit object is forced to send its sole element
to zero. Thus no object `e` can have a currying bijection between maps
`unit × base -> base` and maps `unit -> e`: the former include distinct
projection and zero maps, while the latter are all equal. An exponential
for `base -> base` would necessarily provide the impossible round trip below.
-/

theorem unit_maps_equal (f g : AddMap .unit a) : f = g := by
  apply AddMap.ext
  intro x
  cases x
  exact f.map_zero.trans g.map_zero.symm

theorem no_exponential (e : Ty)
    (curry : AddMap (.prod .unit .base) .base → AddMap .unit e)
    (uncurry : AddMap .unit e → AddMap (.prod .unit .base) .base)
    (roundTrip : ∀ f, uncurry (curry f) = f) : False := by
  let p : AddMap (.prod .unit .base) .base := AddMap.snd _ _
  let z : AddMap (.prod .unit .base) .base :=
    AddMap.comp (additivePrimitive .zero) (AddMap.terminal _)
  have same : p = z := by
    have h := congrArg uncurry (unit_maps_equal (curry p) (curry z))
    simpa only [roundTrip] using h
  have impossible := congrArg (fun f : AddMap (.prod .unit .base) .base => f.run ((), 1)) same
  change (1 : Nat) = 0 at impossible
  omega

#print axioms compile_sound
#print axioms everyTerm_additive
#print axioms letExample_all
#print axioms no_exponential

end FirstOrderCompiler
