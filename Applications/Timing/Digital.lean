import Applications.Timing.Intervals
import FirstOrder
import SquareKit.RelationalCategory
import Applications.Linear.Matrix

/-!
# Stable signals, independent timing and values, and digital morphisms

Time is rational and signals need not be continuous or globally stable.
Stability is an all-times relation over a supplied interval.  Every digital
morphism has a signal transformation, a Boolean value function, a linear
timing function independent of those values, and its stability proof.

The relation has a literal commuting-square presentation through the existing
`Relational.witnessSquare` construction.  It never chooses a Boolean value
for an arbitrary signal or for an empty stability interval.
-/

namespace Applications.Timing

open FirstOrderCompiler
open scoped Matrix

abbrev Signal := Time → Bool

@[reducible] def Port : Ty → Type
  | .base => Fin 1
  | .unit => Fin 0
  | .prod a b => Sum (Port a) (Port b)

instance portFintype : (a : Ty) → Fintype (Port a)
  | .base => inferInstanceAs (Fintype (Fin 1))
  | .unit => inferInstanceAs (Fintype (Fin 0))
  | .prod a b => by
    letI := portFintype a
    letI := portFintype b
    exact inferInstanceAs (Fintype (Sum (Port a) (Port b)))

instance portDecidableEq : (a : Ty) → DecidableEq (Port a)
  | .base => inferInstanceAs (DecidableEq (Fin 1))
  | .unit => inferInstanceAs (DecidableEq (Fin 0))
  | .prod a b => @instDecidableEqSum (Port a) (Port b) (portDecidableEq a) (portDecidableEq b)

abbrev Times (a : Ty) := Port a → Interval

def Stable : (a : Ty) → Val Signal a → Times a → Val Bool a → Prop
  | .base, s, τ, v => ∀ t, (τ 0).Contains t → s t = v
  | .unit, _, _, _ => True
  | .prod a b, s, τ, v =>
      Stable a s.1 (fun i => τ (.inl i)) v.1 ∧
      Stable b s.2 (fun i => τ (.inr i)) v.2

structure Digital (a b : Ty) where
  analog : Val Signal a → Val Signal b
  value : Val Bool a → Val Bool b
  timing : Times a →ₗ[Interval] Times b
  correct : ∀ {s τ v}, Stable a s τ v → Stable b (analog s) (timing τ) (value v)

namespace Digital

@[ext] theorem ext {a b : Ty} {f g : Digital a b}
    (ha : ∀ s, f.analog s = g.analog s)
    (hv : ∀ v, f.value v = g.value v)
    (ht : ∀ τ, f.timing τ = g.timing τ) : f = g := by
  cases f with
  | mk fa fv ft fp =>
    cases g with
    | mk ga gv gt gp =>
      have ha' : fa = ga := funext ha
      have hv' : fv = gv := funext hv
      have ht' : ft = gt := LinearMap.ext ht
      cases ha'; cases hv'; cases ht'
      rfl

/-- The source and target of the stability relation. -/
def object (a : Ty) : Relational.RelRep where
  R := Val Signal a
  S := Times a × Val Bool a
  Rel s tv := Stable a s tv.1 tv.2

def relation {a b : Ty} (f : Digital a b) : Relational.RelSquare (object a) (object b) where
  impl := f.analog
  spec tv := (f.timing tv.1, f.value tv.2)
  preserves := f.correct

def identity (a : Ty) : Digital a a where
  analog := id
  value := id
  timing := LinearMap.id
  correct := id

def compose {a b c : Ty} (g : Digital b c) (f : Digital a b) : Digital a c where
  analog := g.analog ∘ f.analog
  value := g.value ∘ f.value
  timing := g.timing.comp f.timing
  correct {s τ v} h :=
    ((SquareKit.RelationalCategory.witnessMap.map
      (SquareKit.RelationalCategory.ops.comp g.relation f.relation)).left
        ⟨(s, (τ, v)), h⟩).property

def terminate (a : Ty) : Digital a .unit where
  analog _ := ()
  value _ := ()
  timing := 0
  correct _ := True.intro

def first (a b : Ty) : Digital (.prod a b) a where
  analog := Prod.fst
  value := Prod.fst
  timing :=
    { toFun := fun τ i => τ (.inl i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  correct := And.left

def second (a b : Ty) : Digital (.prod a b) b where
  analog := Prod.snd
  value := Prod.snd
  timing :=
    { toFun := fun τ i => τ (.inr i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  correct := And.right

def pair {a b c : Ty} (f : Digital a b) (g : Digital a c) : Digital a (.prod b c) where
  analog s := (f.analog s, g.analog s)
  value v := (f.value v, g.value v)
  timing :=
    { toFun := fun τ => Sum.elim (f.timing τ) (g.timing τ)
      map_add' := by
        intro x y
        funext i
        cases i <;> simp
      map_smul' := by
        intro r x
        funext i
        cases i <;> simp }
  correct h := ⟨f.correct h, g.correct h⟩

def productMap {a b c d : Ty} (f : Digital a c) (g : Digital b d) :
    Digital (.prod a b) (.prod c d) :=
  pair (compose f (first a b)) (compose g (second a b))

theorem compose_assoc {a b c d : Ty} (h : Digital c d) (g : Digital b c) (f : Digital a b) :
    compose h (compose g f) = compose (compose h g) f := by
  apply ext <;> intro x <;> rfl

theorem compose_identity {a b : Ty} (f : Digital a b) : compose f (identity a) = f := by
  apply ext <;> intro x <;> rfl

theorem identity_compose {a b : Ty} (f : Digital a b) : compose (identity b) f = f := by
  apply ext <;> intro x <;> rfl

theorem first_pair {a b c : Ty} (f : Digital a b) (g : Digital a c) :
    compose (first b c) (pair f g) = f := by
  apply ext <;> intro x <;> rfl

theorem second_pair {a b c : Ty} (f : Digital a b) (g : Digital a c) :
    compose (second b c) (pair f g) = g := by
  apply ext <;> intro x <;> rfl

theorem pair_eta {a b c : Ty} (f : Digital a (.prod b c)) :
    pair (compose (first b c) f) (compose (second b c) f) = f := by
  apply ext
  · intro x; rfl
  · intro x; rfl
  · intro x; funext i; cases i <;> rfl

theorem terminal_unique {a : Ty} (f : Digital a .unit) : f = terminate a := by
  apply ext
  · intro x; exact Subsingleton.elim _ _
  · intro x; exact Subsingleton.elim _ _
  · intro x; funext i; exact Fin.elim0 i

/-- Constant signals are correct throughout the universal interval (semiring zero). -/
def constant (v : Bool) : Digital .unit .base where
  analog _ _ := v
  value _ := v
  timing := 0
  correct _ _ _ := rfl

def unary (d : Time) (op : Bool → Bool) : Digital .base .base where
  analog s t := op (s (t - d))
  value := op
  timing :=
    { toFun := fun τ _ => Interval.point d * τ 0
      map_add' := by intro x y; funext i; simp [mul_add]
      map_smul' := by intro r x; funext i; simp [mul_assoc, mul_comm, mul_left_comm] }
  correct hs t ht := congrArg op (hs (t - d) ((Interval.contains_shift d _ t).mp ht))

def binary (d₁ d₂ : Time) (op : Bool × Bool → Bool) : Digital (.prod .base .base) .base where
  analog s t := op (s.1 (t - d₁), s.2 (t - d₂))
  value := op
  timing :=
    { toFun := fun τ _ => Interval.point d₁ * τ (.inl 0) + Interval.point d₂ * τ (.inr 0)
      map_add' := by
        intro x y; funext i
        simp only [Pi.add_apply, mul_add]
        ac_rfl
      map_smul' := by
        intro r x; funext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add]
        ac_rfl }
  correct hs t ht := by
    have h := (Interval.contains_add _ _ t).mp ht
    exact congrArg op (Prod.ext
      (hs.1 (t - d₁) ((Interval.contains_shift d₁ _ t).mp h.1))
      (hs.2 (t - d₂) ((Interval.contains_shift d₂ _ t).mp h.2)))

def square {a b : Ty} (f : Digital a b) :
    Squares.Square (Relational.witness (object a)) (Relational.witness (object b)) :=
  Relational.witnessSquare f.relation

theorem relation_compose {a b c : Ty} (g : Digital b c) (f : Digital a b) :
    (compose g f).relation = Relational.compose g.relation f.relation := by
  apply Relational.RelSquare.ext <;> intro x <;> rfl

theorem square_compose {a b c : Ty} (g : Digital b c) (f : Digital a b) :
    (compose g f).square = Squares.compose g.square f.square := by
  unfold square
  rw [relation_compose]
  exact congrArg (fun f => SquareKit.Comma.Exact.toSquare f)
    (SquareKit.RelationalCategory.witnessMap_laws.comp g.relation f.relation)

/-- Static timing is a matrix of retained setup/hold interval bounds. -/
def matrix {a b : Ty} (f : Digital a b) : Matrix (Port b) (Port a) Interval :=
  LinearMap.toMatrix' f.timing

/-- Forget signal/value behavior while retaining the exact timing semantics. -/
def timingRep (a b : Ty) : Squares.Rep where
  R := Digital a b
  S := Times a →ₗ[Interval] Times b
  decode := Digital.timing

/-- The shared generic matrix backend applies unchanged to timing intervals. -/
def timingMatrixSquare (a b : Ty) :
    Squares.Square (timingRep a b)
      (MatrixBackend.representation Interval (Port b) (Port a)) where
  impl := matrix
  spec := id
  commutes f := MatrixBackend.decode_encode Interval (Port b) (Port a) f.timing

theorem matrix_correct {a b : Ty} (f : Digital a b) (τ : Times a) :
    f.matrix *ᵥ τ = f.timing τ := by
  exact congrArg (fun h : Times a →ₗ[Interval] Times b => h τ)
    (Matrix.toLin'_toMatrix' f.timing)

theorem matrix_compose {a b c : Ty} (g : Digital b c) (f : Digital a b) :
    (compose g f).matrix = g.matrix * f.matrix :=
  LinearMap.toMatrix'_comp g.timing f.timing

theorem matrix_identity (a : Ty) : (identity a).matrix = 1 :=
  LinearMap.toMatrix'_id

theorem timing_add {a b : Ty} (f : Digital a b) (x y : Times a) :
    f.timing (x + y) = f.timing x + f.timing y := f.timing.map_add x y

theorem timing_scale {a b : Ty} (f : Digital a b) (r : Interval) (x : Times a) :
    f.timing (r • x) = r • f.timing x := f.timing.map_smul r x

theorem timing_zero {a b : Ty} (f : Digital a b) : f.timing 0 = 0 := f.timing.map_zero

theorem matrix_stable {a b : Ty} (f : Digital a b) {s τ v}
    (h : Stable a s τ v) : Stable b (f.analog s) (f.matrix *ᵥ τ) (f.value v) := by
  rw [matrix_correct]
  exact f.correct h

end Digital
end Applications.Timing
