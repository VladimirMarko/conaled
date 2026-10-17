import FirstOrder
import SquareKit.RelationalCategory
import SquareKit.FirstOrderNaturality

/-!
# One first-order compiler for relation-preserving implementations

The frontend is unchanged. Its target is now a category of relational squares.
Local primitive certificates imply a theorem for *all* source terms, including
sharing through let. Exact decoding is the graph-relation special case.
-/
namespace FirstOrderRelations
open FirstOrderCompiler Relational

structure Encoding (S : Type) where
  R : Type
  Rel : R → S → Prop

def encoding (base : RelRep) : (a : Ty) → Encoding (Val base.S a)
  | .base => ⟨base.R, base.Rel⟩
  | .unit => ⟨Unit, fun _ _ => True⟩
  | .prod a b =>
    ⟨(encoding base a).R × (encoding base b).R,
      fun r s => (encoding base a).Rel r.1 s.1 ∧ (encoding base b).Rel r.2 s.2⟩

def object (base : RelRep) (a : Ty) : RelRep :=
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
  primitive p := ⟨P.impl p, meaning p, P.correct p⟩

/-- The legacy target only selects the relational objects; arrows are unchanged. -/
def interpretation (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning) :
    SquareKit.RawMap (SquareKit.FirstOrderCategory.ops (target base P))
      SquareKit.RelationalCategory.ops where
  obj := object base
  map f := f

theorem interpretation_laws (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning) :
    SquareKit.MapLaws (interpretation base P) (SquareKit.equality _) (SquareKit.equality _) :=
  ⟨by intros; subst_vars; rfl, rfl, fun _ _ => rfl⟩

/-- Restrict semantic product preservation to the objects selected by the frontend. -/
def semanticProducts (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning) :
    SquareKit.ProductMap ((interpretation base P).comp SquareKit.RelationalCategory.semantics)
      (SquareKit.FirstOrderCategory.products (target base P)) SquareKit.FunctionCategory.products :=
  fun a b => SquareKit.RelationalCategory.semanticsProducts (object base a) (object base b)

theorem semanticProducts_laws (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning) :
    SquareKit.ProductMapLaws (SquareKit.equality _) (semanticProducts base P) where
  fst {a b} := SquareKit.RelationalCategory.semanticsProducts_laws.fst
    (a := object base a) (b := object base b)
  snd {a b} := SquareKit.RelationalCategory.semanticsProducts_laws.snd
    (a := object base a) (b := object base b)
  pair f g := SquareKit.RelationalCategory.semanticsProducts_laws.pair f g

def sound (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning) : Sound base.S (target base P) meaning :=
  SquareKit.FirstOrderNaturality.soundOfProducts (target base P) base.S
    ((interpretation base P).comp SquareKit.RelationalCategory.semantics).map
    (SquareKit.RawMap.comp_laws (interpretation_laws base P)
      SquareKit.RelationalCategory.semantics_laws)
    (semanticProducts base P) (semanticProducts_laws base P)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)

theorem compile_spec (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning)
    (t : Term Prim Γ a) (ρ : Val base.S (context Γ)) :
    (compile (target base P) t).spec ρ = eval meaning t ρ :=
  SquareKit.FirstOrderNaturality.compile_sound (target base P) (sound base P) t ρ

theorem compile_preserves (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning)
    (t : Term Prim Γ a) {r : (encoding base (context Γ)).R}
    {s : Val base.S (context Γ)} (h : (encoding base (context Γ)).Rel r s) :
    (encoding base a).Rel ((compile (target base P) t).impl r) (eval meaning t s) := by
  rw [← compile_spec base P t s]
  exact (compile (target base P) t).preserves h

def compileRelation (base : RelRep) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : Primitives base Prim meaning)
    (t : Term Prim Γ a) : RelSquare (object base (context Γ)) (object base a) where
  impl := (compile (target base P) t).impl
  spec := eval meaning t
  preserves := compile_preserves base P t

end FirstOrderRelations
