import SquareKit.STLCRelations
import Applications.Intervals.Arithmetic

/-!
# Compiling higher-order interval programs

The same intrinsically typed frontend now compiles lambdas, higher-order
application, lexical capture, and case analysis into ordinary interval
functions. The generic logical-relation theorem provides enclosure for all
terms and all related environments. This module uses the rational interval
operations and their proved enclosure lemmas from `Arithmetic.lean`.

Sum representations retain a definite tag. This is not a join-based analysis
of an unknown conditional, nor a proof that interval arithmetic is exact.
-/

namespace IntervalAnalysis.HigherOrder

open CategoricalCompiler

inductive Prim : Ty → Ty → Type
  | literal : ℚ → Prim .unit .base
  | add : Prim (.prod .base .base) .base
  | mul : Prim (.prod .base .base) .base
  | neg : Prim .base .base

def meaning : {a b : Ty} → Prim a b → Val ℚ a → Val ℚ b
  | _, _, .literal r => fun _ => r
  | _, _, .add => fun p => p.1 + p.2
  | _, _, .mul => fun p => p.1 * p.2
  | _, _, .neg => Neg.neg

def primitives : STLCRelations.Primitives representation Prim meaning where
  impl := fun {a b} p => match p with
    | .literal r => fun _ => singleton r
    | .add => fun p => IntervalAnalysis.add p.1 p.2
    | .mul => fun p => IntervalAnalysis.mul p.1 p.2
    | .neg => IntervalAnalysis.neg
  correct := by
    intro a b p r s h
    cases p with
    | literal q => exact singleton_contains q
    | add => exact add_contains h.1 h.2
    | mul => exact mul_contains h.1 h.2
    | neg => exact neg_contains h

def compile {Γ a} (t : Term Prim Γ a) :=
  STLCRelations.compileRelation representation primitives t

theorem compile_contains {Γ a} (t : Term Prim Γ a)
    {box : (STLCRelations.encoding representation (context Γ)).R}
    {ρ : Val ℚ (context Γ)}
    (h : (STLCRelations.encoding representation (context Γ)).Rel box ρ) :
    (STLCRelations.encoding representation a).Rel ((compile t).impl box)
      (eval meaning t ρ) :=
  STLCRelations.compile_preserves representation primitives t h

/-- The first argument is a runtime interval function, not a chosen rational function. -/
def RepresentsFunction (F : Interval → Interval) (f : ℚ → ℚ) : Prop :=
  ∀ {I x}, Contains I x → Contains (F I) (f x)

def squareFunction : Term Prim [] (.arr .base .base) :=
  .lam (.prim .mul (.pair (.var .here) (.var .here)))

theorem squareFunction_contains {I : Interval} {x : ℚ} (h : Contains I x) :
    Contains (((compile squareFunction).impl ()) I) (x * x) :=
  compile_contains squareFunction (box := ()) (ρ := ()) True.intro h

/-- `λ f x. f (f x)`, with a genuinely higher-order argument. -/
def iterateTwice : Term Prim [] (.arr (.arr .base .base) (.arr .base .base)) :=
  .lam (.lam (.app (.var (.there .here))
    (.app (.var (.there .here)) (.var .here))))

theorem iterateTwice_contains {F : Interval → Interval} {f : ℚ → ℚ}
    (hf : RepresentsFunction F f) {I : Interval} {x : ℚ} (hx : Contains I x) :
    Contains ((((compile iterateTwice).impl ()) F) I) (f (f x)) :=
  compile_contains iterateTwice (box := ()) (ρ := ()) True.intro hf hx

/-- Higher-order application occurs in the source, before categorical compilation. -/
def fourthPower : Term Prim [] (.arr .base .base) := .app iterateTwice squareFunction

theorem fourthPower_contains {I : Interval} {x : ℚ} (hx : Contains I x) :
    Contains (((compile fourthPower).impl ()) I) ((x * x) * (x * x)) :=
  compile_contains fourthPower (box := ()) (ρ := ()) True.intro hx

/-- `λ x. x*x+c`, with `c` captured from the compilation environment. -/
def capturedLambda : Term Prim [.base] (.arr .base .base) :=
  .lam (.prim .add (.pair
    (.prim .mul (.pair (.var .here) (.var .here)))
    (.var (.there .here))))

theorem capturedLambda_contains {C I : Interval} {c x : ℚ}
    (hc : Contains C c) (hx : Contains I x) :
    Contains (((compile capturedLambda).impl ((), C)) I) (x * x + c) :=
  compile_contains capturedLambda (box := ((), C)) (ρ := ((), c)) ⟨True.intro, hc⟩ hx

/-- Both branches capture a function and a scalar; the right branch negates its payload. -/
def capturedCase : Term Prim [.base, .arr .base .base, .sum .base .base] .base :=
  .caseE (.var (.there (.there .here)))
    (.prim .add (.pair
      (.app (.var (.there (.there .here))) (.var .here))
      (.var (.there .here))))
    (.prim .add (.pair
      (.app (.var (.there (.there .here))) (.var (.there .here)))
      (.prim .neg (.var .here))))

theorem capturedCase_left_contains {F : Interval → Interval} {f : ℚ → ℚ}
    (hf : RepresentsFunction F f) {C I : Interval} {c x : ℚ}
    (hc : Contains C c) (hx : Contains I x) :
    Contains ((compile capturedCase).impl ((((), Sum.inl I), F), C)) (f x + c) :=
  compile_contains capturedCase (box := ((((), Sum.inl I), F), C))
    (ρ := ((((), Sum.inl x), f), c)) ⟨⟨⟨True.intro, hx⟩, hf⟩, hc⟩

theorem capturedCase_right_contains {F : Interval → Interval} {f : ℚ → ℚ}
    (hf : RepresentsFunction F f) {C I : Interval} {c x : ℚ}
    (hc : Contains C c) (hx : Contains I x) :
    Contains ((compile capturedCase).impl ((((), Sum.inr I), F), C)) (f c + -x) :=
  compile_contains capturedCase (box := ((((), Sum.inr I), F), C))
    (ρ := ((((), Sum.inr x), f), c)) ⟨⟨⟨True.intro, hx⟩, hf⟩, hc⟩

def increment (I : Interval) : Interval := IntervalAnalysis.add I (singleton 1)

theorem increment_represents : RepresentsFunction increment (fun x => x + 1) :=
  fun h => add_contains h (singleton_contains 1)

example : (compile capturedCase).impl
    ((((), Sum.inl (⟨-1, 2⟩ : Interval)), increment), ⟨10, 11⟩) = ⟨10, 14⟩ := by
  change IntervalAnalysis.add (increment ⟨-1, 2⟩) ⟨10, 11⟩ = _
  norm_num [IntervalAnalysis.add, increment, singleton]

example : (compile capturedCase).impl
    ((((), Sum.inr (⟨-1, 2⟩ : Interval)), increment), ⟨10, 11⟩) = ⟨9, 13⟩ := by
  change IntervalAnalysis.add (increment ⟨10, 11⟩) (IntervalAnalysis.neg ⟨-1, 2⟩) = _
  norm_num [IntervalAnalysis.add, IntervalAnalysis.neg, increment, singleton]

example : ((compile fourthPower).impl ()) (⟨-1, 2⟩ : Interval) = ⟨-8, 16⟩ := by
  change IntervalAnalysis.mul (IntervalAnalysis.mul ⟨-1, 2⟩ ⟨-1, 2⟩)
    (IntervalAnalysis.mul ⟨-1, 2⟩ ⟨-1, 2⟩) = _
  norm_num [IntervalAnalysis.mul]

end IntervalAnalysis.HigherOrder
