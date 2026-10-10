import Compiler
import SquareKit.Relations

/-!
# The full simply typed compiler over relational squares

This target supports every constructor of the existing source language:
products, functions, sums, lexical capture, let, and primitives. Function
representations are ordinary runtime functions. Their correctness relation
quantifies over every related input; no decoder from arbitrary runtime
functions to semantic functions is assumed or constructed.

Sums relate only matching tags. This makes categorical case analysis sound
while preserving the captured context through the distribution operation.
-/

namespace STLCRelations

open CategoricalCompiler Relational

structure Encoding (S : Type) where
  R : Type
  Rel : R → S → Prop

def Encoding.arrow {S T : Type} (A : Encoding S) (B : Encoding T) : Encoding (S → T) :=
  ⟨A.R → B.R, fun f g => ∀ {r s}, A.Rel r s → B.Rel (f r) (g s)⟩

def Encoding.sum {S T : Type} (A : Encoding S) (B : Encoding T) : Encoding (Sum S T) :=
  ⟨Sum A.R B.R, fun r s => match r, s with
    | .inl r, .inl s => A.Rel r s
    | .inr r, .inr s => B.Rel r s
    | _, _ => False⟩

@[reducible] def encoding (base : RelRep) : (a : Ty) → Encoding (Val base.S a)
  | .base => ⟨base.R, base.Rel⟩
  | .unit => ⟨Unit, fun _ _ => True⟩
  | .prod a b =>
    ⟨(encoding base a).R × (encoding base b).R,
      fun r s => (encoding base a).Rel r.1 s.1 ∧ (encoding base b).Rel r.2 s.2⟩
  | .arr a b => (encoding base a).arrow (encoding base b)
  | .sum a b => (encoding base a).sum (encoding base b)

@[reducible] def object (base : RelRep) (a : Ty) : RelRep :=
  ⟨(encoding base a).R, Val base.S a, (encoding base a).Rel⟩

structure Primitives (base : RelRep) (Prim : Ty → Ty → Type)
    (meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b) where
  impl : {a b : Ty} → Prim a b → (encoding base a).R → (encoding base b).R
  correct : ∀ {a b : Ty} (p : Prim a b) {r s},
    (encoding base a).Rel r s → (encoding base b).Rel (impl p r) (meaning p s)

def target (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning) : Target Prim where
  Hom a b := RelSquare (object base a) (object base b)
  ident := ⟨id, id, id⟩
  comp g f := Relational.compose g f
  terminal := ⟨fun _ => (), fun _ => (), fun _ => True.intro⟩
  fst := ⟨Prod.fst, Prod.fst, And.left⟩
  snd := ⟨Prod.snd, Prod.snd, And.right⟩
  pair f g := ⟨fun x => (f.impl x, g.impl x), fun x => (f.spec x, g.spec x),
    fun h => ⟨f.preserves h, g.preserves h⟩⟩
  curry f := ⟨fun x a => f.impl (x, a), fun x a => f.spec (x, a),
    fun hx _ _ ha => f.preserves ⟨hx, ha⟩⟩
  apply := ⟨fun p => p.1 p.2, fun p => p.1 p.2, fun h => h.1 h.2⟩
  inl := ⟨Sum.inl, Sum.inl, fun h => h⟩
  inr := ⟨Sum.inr, Sum.inr, fun h => h⟩
  copair f g := ⟨Sum.elim f.impl g.impl, Sum.elim f.spec g.spec, by
    intro r s h
    cases r <;> cases s
    · exact f.preserves h
    · exact False.elim h
    · exact False.elim h
    · exact g.preserves h⟩
  dist := ⟨fun p => Sum.elim (fun a => .inl (p.1, a)) (fun b => .inr (p.1, b)) p.2,
    fun p => Sum.elim (fun a => .inl (p.1, a)) (fun b => .inr (p.1, b)) p.2, by
      intro r s h
      rcases r with ⟨rx, ry⟩
      rcases s with ⟨sx, sy⟩
      rcases h with ⟨hx, hy⟩
      cases ry <;> cases sy
      · exact ⟨hx, hy⟩
      · exact False.elim hy
      · exact False.elim hy
      · exact ⟨hx, hy⟩⟩
  primitive p := ⟨P.impl p, meaning p, P.correct p⟩

def sound (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning) : Sound base.S (target base P) meaning where
  denote f := f.spec
  ident _ := rfl
  comp _ _ _ := rfl
  terminal _ := rfl
  fst _ := rfl
  snd _ := rfl
  pair _ _ _ := rfl
  curry _ _ _ := rfl
  apply _ := rfl
  inl _ := rfl
  inr _ := rfl
  copair _ _ _ := rfl
  dist x := by rcases x with ⟨x, y⟩; cases y <;> rfl
  primitive _ _ := rfl

theorem compile_spec (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning) (t : Term Prim Γ a)
    (ρ : Val base.S (context Γ)) :
    (compile (target base P) t).spec ρ = eval meaning t ρ :=
  compile_sound (target base P) (sound base P) t ρ

/-- The fundamental logical-relation theorem for every source term. -/
theorem compile_preserves (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning) (t : Term Prim Γ a)
    {r : (encoding base (context Γ)).R} {s : Val base.S (context Γ)}
    (h : (encoding base (context Γ)).Rel r s) :
    (encoding base a).Rel ((compile (target base P) t).impl r) (eval meaning t s) := by
  rw [← compile_spec base P t s]
  exact (compile (target base P) t).preserves h

/-- A compiled lambda can be applied to any related runtime/semantic argument. -/
theorem compile_apply_preserves (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning) (t : Term Prim Γ (.arr a b))
    {r : (encoding base (context Γ)).R} {s : Val base.S (context Γ)}
    (h : (encoding base (context Γ)).Rel r s)
    {x : (encoding base a).R} {y : Val base.S a}
    (hxy : (encoding base a).Rel x y) :
    (encoding base b).Rel (((compile (target base P) t).impl r) x) ((eval meaning t s) y) :=
  compile_preserves base P t h hxy

def compileRelation (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning) (t : Term Prim Γ a) :
    RelSquare (object base (context Γ)) (object base a) where
  impl := (compile (target base P) t).impl
  spec := eval meaning t
  preserves := compile_preserves base P t

/-- The relational compiler can also be presented as a square on total witnesses. -/
def compileWitnessSquare (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning) (t : Term Prim Γ a) :
    Squares.Square (Relational.witness (object base (context Γ)))
      (Relational.witness (object base a)) :=
  Relational.witnessSquare (compileRelation base P t)

end STLCRelations
