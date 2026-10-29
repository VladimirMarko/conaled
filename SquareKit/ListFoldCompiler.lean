import FirstOrder
import SquareKit.ListFusion

/-! Finite list recursion outside the existing first-order body language.
Compilation traverses syntax only; evaluation consumes the runtime list. -/
namespace ListFoldCompiler
open FirstOrderCompiler
variable {Prim : Ty → Ty → Type}

inductive Program (Prim : Ty → Ty → Type) : Ty → Ty → Type where
  | fold : Term Prim [] b → Term Prim [a,b] b → Program Prim a b
  | post : Program Prim a b → Term Prim [b] c → Program Prim a c

/-- Source recursion: the tail strictly decreases, independently of compilation. -/
def iterate {B : Type} (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (body : Term Prim [a,b] b) (acc : Val B b) : List (Val B a) → Val B b
  | [] => acc
  | x::xs => iterate meaning body (FirstOrderCompiler.eval meaning body (((),acc),x)) xs

def eval {B : Type} (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) :
    Program Prim a b → List (Val B a) → Val B b
  | .fold seed body, xs => iterate meaning body (FirstOrderCompiler.eval meaning seed ()) xs
  | .post p body, xs => FirstOrderCompiler.eval meaning body ((),eval meaning p xs)

/-- Finite source executions count body visits, not primitive execution cost. -/
inductive Executes {B : Type} (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (body : Term Prim [a,b] b) : List (Val B a) → Val B b → Val B b → Nat → Prop where
  | nil : Executes meaning body [] s s 0
  | cons : Executes meaning body xs (FirstOrderCompiler.eval meaning body (((),s),x)) r n →
      Executes meaning body (x::xs) s r (n+1)

theorem iterate_executes {B : Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (body : Term Prim [a,b] b) (xs : List (Val B a)) (s : Val B b) :
    Executes meaning body xs s (iterate meaning body s xs) xs.length := by
  induction xs generalizing s with
  | nil => exact .nil
  | cons x xs ih => exact .cons (ih _)

theorem iterate_eq_foldl {B : Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (body : Term Prim [a,b] b) (xs : List (Val B a)) (s : Val B b) :
    iterate meaning body s xs = xs.foldl (fun acc x => FirstOrderCompiler.eval meaning body (((),acc),x)) s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih _

structure Target (Prim : Ty → Ty → Type) where
  scalar : FirstOrderCompiler.Target Prim
  Hom : Ty → Ty → Type
  fold : scalar.Hom .unit b → scalar.Hom (context [a,b]) b → Hom a b
  post : scalar.Hom (context [b]) c → Hom a b → Hom a c

/-- This definition receives no runtime list. Each seed/body is compiled once. -/
def compile (K : Target Prim) : Program Prim a b → K.Hom a b
  | .fold seed body => K.fold (FirstOrderCompiler.compile K.scalar seed)
      (FirstOrderCompiler.compile K.scalar body)
  | .post p body => K.post (FirstOrderCompiler.compile K.scalar body) (compile K p)

@[simp] theorem compile_fold (K : Target Prim) (seed : Term Prim [] b)
    (body : Term Prim [a,b] b) :
    compile K (.fold seed body) = K.fold (FirstOrderCompiler.compile K.scalar seed)
      (FirstOrderCompiler.compile K.scalar body) := rfl

/-- The fold equation is extra preservation structure, not a cartesian law. -/
structure Sound (B : Type) (K : Target Prim)
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) where
  scalar : FirstOrderCompiler.Sound B K.scalar meaning
  denote : K.Hom a b → List (Val B a) → Val B b
  fold : ∀ (seed : K.scalar.Hom .unit b) (body : K.scalar.Hom (context [a,b]) b) xs,
    denote (K.fold seed body) xs = xs.foldl (fun s x => scalar.denote body (((),s),x)) (scalar.denote seed ())
  post : ∀ (body : K.scalar.Hom (context [b]) c) (p : K.Hom a b) xs,
    denote (K.post body p) xs = scalar.denote body ((),denote p xs)

theorem compile_sound {B : Type} (K : Target Prim)
    {meaning : {a b : Ty} → Prim a b → Val B a → Val B b}
    (S : Sound B K meaning) (p : Program Prim a b) (xs : List (Val B a)) :
    S.denote (compile K p) xs = eval meaning p xs := by
  induction p with
  | fold seed body =>
    simp only [compile, S.fold, FirstOrderCompiler.compile_sound K.scalar S.scalar,
      eval,iterate_eq_foldl]
  | post p body ih =>
    simp only [compile, S.post, FirstOrderCompiler.compile_sound K.scalar S.scalar,ih,eval]

def functionScalar {B : Type} (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) :
    FirstOrderCompiler.Target Prim where
  Hom a b := Val B a → Val B b
  ident := id
  comp := Function.comp
  terminal _ := ()
  fst := Prod.fst
  snd := Prod.snd
  pair f g x := (f x,g x)
  primitive := meaning

def functionScalarSound {B : Type} (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) :
    FirstOrderCompiler.Sound B (functionScalar meaning) meaning where
  denote := id
  ident _ := rfl
  comp _ _ _ := rfl
  terminal _ := rfl
  fst _ := rfl
  snd _ := rfl
  pair _ _ _ := rfl
  primitive _ _ := rfl

def functionTarget {B : Type} (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) : Target Prim where
  scalar := functionScalar meaning
  Hom a b := List (Val B a) → Val B b
  fold seed body xs := xs.foldl (fun s x => body (((),s),x)) (seed ())
  post body p xs := body ((),p xs)

def functionSound {B : Type} (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) :
    Sound B (functionTarget meaning) meaning where
  scalar := functionScalarSound meaning
  denote := id
  fold _ _ _ := rfl
  post _ _ _ := rfl

/-- Reachable-state fusion reuses the existing ADWH/list law. -/
theorem fold_fusion {B : Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (seed : Term Prim [] b) (body : Term Prim [a,b] b)
    (seed' : Term Prim [] c) (body' : Term Prim [a,c] c)
    (h : Val B b → Val B c) (P : Val B b → Prop)
    (base : P (FirstOrderCompiler.eval meaning seed ()))
    (closed : ∀ s x, P s → P (FirstOrderCompiler.eval meaning body (((),s),x)))
    (initial : h (FirstOrderCompiler.eval meaning seed ()) = FirstOrderCompiler.eval meaning seed' ())
    (law : ∀ s x, P s → h (FirstOrderCompiler.eval meaning body (((),s),x)) =
      FirstOrderCompiler.eval meaning body' (((),h s),x)) (xs : List (Val B a)) :
    h (eval meaning (.fold seed body) xs) = eval meaning (.fold seed' body') xs := by
  simp only [eval,iterate_eq_foldl]
  rw [← initial]
  exact SquareKit.ListFusion.foldl_reachable _ _ h P _ base closed law xs

/-- The same source fusion crosses any two sound targets; counted targets expose
value denotation here, never an unjustified equality of costs. -/
theorem compiled_fusion {B : Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (K L : Target Prim) (SK : Sound B K meaning) (SL : Sound B L meaning)
    (seed : Term Prim [] b) (body : Term Prim [a,b] b) (finish : Term Prim [b] c)
    (seed' : Term Prim [] c) (body' : Term Prim [a,c] c)
    (P : Val B b → Prop)
    (base : P (FirstOrderCompiler.eval meaning seed ()))
    (closed : ∀ s x, P s → P (FirstOrderCompiler.eval meaning body (((),s),x)))
    (initial : FirstOrderCompiler.eval meaning finish ((),FirstOrderCompiler.eval meaning seed ()) =
      FirstOrderCompiler.eval meaning seed' ())
    (law : ∀ s x, P s →
      FirstOrderCompiler.eval meaning finish ((),FirstOrderCompiler.eval meaning body (((),s),x)) =
      FirstOrderCompiler.eval meaning body'
        (((),FirstOrderCompiler.eval meaning finish ((),s)),x)) (xs : List (Val B a)) :
    SK.denote (compile K (.post (.fold seed body) finish)) xs =
      SL.denote (compile L (.fold seed' body')) xs := by
  rw [compile_sound,compile_sound]
  exact fold_fusion meaning seed body seed' body'
    (fun s => FirstOrderCompiler.eval meaning finish ((),s)) P base closed initial law xs

end ListFoldCompiler
