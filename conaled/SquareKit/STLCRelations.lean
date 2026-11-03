import Compiler
import SquareKit.RelationalCategory
import SquareKit.STLCNaturality

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

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
  fst := SquareKit.RelationalCategory.products.fst (a := object base _) (b := object base _)
  snd := SquareKit.RelationalCategory.products.snd (a := object base _) (b := object base _)
  pair f g := SquareKit.RelationalCategory.products.pair f g
  curry {x a b} f := SquareKit.RelationalCategory.closed.curry
    (x := object base x) (a := object base a) (b := object base b) f
  apply := SquareKit.RelationalCategory.closed.evaluation (a := object base _) (b := object base _)
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

open SquareKit

section Interpretation
variable (base : RelRep) {Prim : Ty → Ty → Type}
variable {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
variable (P : Primitives base Prim meaning)

/-- The typed target enters the relational category without discarding either map. -/
def inclusion : RawMap (STLCCategory.ops (target base P)) RelationalCategory.ops where
  obj := object base
  map f := f

theorem inclusion_laws : MapLaws (inclusion base P) (equality _) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := rfl
  comp _ _ := rfl

/-- Projection selects the semantic horizontal arrow, not a decoder of runtime values. -/
def interpretation := (inclusion base P).comp RelationalCategory.semantics

theorem interpretation_laws : MapLaws (interpretation base P) (equality _) (equality _) :=
  RawMap.comp_laws (inclusion_laws base P) RelationalCategory.semantics_laws

/-- The full-source preservation package records only local operation compatibility. -/
theorem interpretation_preserves : STLCNaturality.Preserves (interpretation base P)
    (equality _) (STLCNaturality.ofTarget (target base P))
    (STLCNaturality.semantics base.S meaning) where
  terminal := rfl
  fst := rfl
  snd := rfl
  pair _ _ := rfl
  inl := rfl
  inr := rfl
  copair _ _ := rfl
  dist := funext (fun ⟨_, y⟩ => by cases y <;> rfl)
  curry _ := rfl
  apply := rfl
  primitive _ := rfl

/-- Compatibility with the original API uses the same map and preservation package. -/
def sound : Sound base.S (target base P) meaning where
  denote := (interpretation base P).map
  ident x := congrFun (interpretation_laws base P).ident x
  comp g f x := congrFun ((interpretation_laws base P).comp g f) x
  terminal x := congrFun (interpretation_preserves base P).terminal x
  fst x := congrFun (interpretation_preserves base P).fst x
  snd x := congrFun (interpretation_preserves base P).snd x
  pair f g x := congrFun ((interpretation_preserves base P).pair f g) x
  curry f x a := congrFun (congrFun ((interpretation_preserves base P).curry f) x) a
  apply x := congrFun (interpretation_preserves base P).apply x
  inl x := congrFun (interpretation_preserves base P).inl x
  inr x := congrFun (interpretation_preserves base P).inr x
  copair f g x := congrFun ((interpretation_preserves base P).copair f g) x
  dist x := congrFun (interpretation_preserves base P).dist x
  primitive p x := congrFun ((interpretation_preserves base P).primitive p) x

end Interpretation

theorem compile_spec (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning) (t : Term Prim Γ a)
    (ρ : Val base.S (context Γ)) :
    (compile (target base P) t).spec ρ = eval meaning t ρ := by
  have h := STLCNaturality.naturality (interpretation_laws base P) (equalityCongr _)
    (show STLCNaturality.ModelCongr (equality _) (STLCNaturality.semantics base.S meaning) from
      ⟨by intros; subst_vars; rfl, by intros; subst_vars; rfl, by intros; subst_vars; rfl⟩)
    (interpretation_preserves base P) t
  have hp := congrFun h ρ
  change (STLCNaturality.compile (STLCNaturality.ofTarget (target base P)) t).spec ρ =
    STLCNaturality.compile (STLCNaturality.semantics base.S meaning) t ρ at hp
  rw [STLCNaturality.compile_ofTarget, STLCNaturality.semantics_compile] at hp
  exact hp

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
