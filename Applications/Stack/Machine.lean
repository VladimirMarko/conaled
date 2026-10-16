import FirstOrder
import SquareKit.Combinators

/-!
# Calculating a typed stack-machine backend

This reconstructs the completed first-order stack-program development in
Elliott's 2018 draft and 2020 talk. Products are sequentialized using explicit
push/pop/swap instructions. The semantic contract quantifies over every stack
tail, rather than relying on an unformalized parametricity argument for Lean.

The instruction language contains no arbitrary function instruction. Only the
supplied typed primitive vocabulary and structural operations are executable.
The returned `.code` is an inspectable typed sequence, independently of its
semantic certificate. Exponentials/closures and branching bytecode are not
claimed by this first-order module.
-/

namespace StackMachine
open FirstOrderCompiler

abbrev Stack (B : Type) : List Ty → Type
  | [] => Unit
  | a :: s => Val B a × Stack B s

inductive Instr (Prim : Ty → Ty → Type) : Ty → List Ty → Ty → List Ty → Type where
  | primitive : Prim a b → Instr Prim a s b s
  | terminal : Instr Prim a s .unit s
  | dup : Instr Prim a s (.prod a a) s
  | fst : Instr Prim (.prod a b) s a s
  | snd : Instr Prim (.prod a b) s b s
  | swap : Instr Prim (.prod a b) s (.prod b a) s
  | push : Instr Prim (.prod a b) s a (b :: s)
  | pop : Instr Prim a (b :: s) (.prod a b) s

inductive Program (Prim : Ty → Ty → Type) : Ty → List Ty → Ty → List Ty → Type where
  | nil : Program Prim a s a s
  | cons : Instr Prim a s b t → Program Prim b t c u → Program Prim a s c u

def Program.append : Program Prim a s b t → Program Prim b t c u → Program Prim a s c u
  | .nil, q => q
  | .cons i p, q => .cons i (p.append q)

variable {Prim : Ty → Ty → Type}

def runInstr {B : Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) :
    Instr Prim a s b t → Val B a × Stack B s → Val B b × Stack B t
  | .primitive p, (x, z) => (meaning p x, z)
  | .terminal, (_, z) => ((), z)
  | .dup, (x, z) => ((x, x), z)
  | .fst, ((x, _), z) => (x, z)
  | .snd, ((_, y), z) => (y, z)
  | .swap, ((x, y), z) => ((y, x), z)
  | .push, ((x, y), z) => (x, (y, z))
  | .pop, (x, (y, z)) => ((x, y), z)

def run {B : Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) :
    Program Prim a s b t → Val B a × Stack B s → Val B b × Stack B t
  | .nil, x => x
  | .cons i p, x => run meaning p (runInstr meaning i x)

theorem run_append {B : Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (p : Program Prim a s b t) (q : Program Prim b t c u) (x) :
    run meaning (p.append q) x = run meaning q (run meaning p x) := by
  induction p with
  | nil => rfl
  | cons i p ih => exact ih q (runInstr meaning i x)

theorem push_pop {B : Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (x : Val B (.prod a b) × Stack B s) :
    run meaning (.cons .push (.cons .pop .nil)) x = x := rfl

theorem swap_swap {B : Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (x : Val B (.prod a b) × Stack B s) :
    run meaning (.cons .swap (.cons .swap .nil)) x = x := rfl

structure Certified {B : Type} (Prim : Ty → Ty → Type)
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) (a b : Ty) where
  code : ∀ s, Program Prim a s b s
  spec : Val B a → Val B b
  correct : ∀ s x (z : Stack B s), run meaning (code s) (x, z) = (spec x, z)

namespace Certified
variable {B : Type} {Prim : Ty → Ty → Type}
variable {meaning : {a b : Ty} → Prim a b → Val B a → Val B b}

def ident (a : Ty) : Certified Prim meaning a a :=
  ⟨fun _ => .nil, id, fun _ _ _ => rfl⟩

def comp (g : Certified Prim meaning b c) (f : Certified Prim meaning a b) :
    Certified Prim meaning a c where
  code s := (f.code s).append (g.code s)
  spec x := g.spec (f.spec x)
  correct s x z := by rw [run_append, f.correct, g.correct]

def primitive (p : Prim a b) : Certified Prim meaning a b :=
  ⟨fun _ => .cons (.primitive p) .nil, meaning p, fun _ _ _ => rfl⟩

def terminal (a : Ty) : Certified Prim meaning a .unit :=
  ⟨fun _ => .cons .terminal .nil, fun _ => (), fun _ _ _ => rfl⟩

def dup (a : Ty) : Certified Prim meaning a (.prod a a) :=
  ⟨fun _ => .cons .dup .nil, fun x => (x, x), fun _ _ _ => rfl⟩

def fst (a b : Ty) : Certified Prim meaning (.prod a b) a :=
  ⟨fun _ => .cons .fst .nil, Prod.fst, fun _ _ _ => rfl⟩

def snd (a b : Ty) : Certified Prim meaning (.prod a b) b :=
  ⟨fun _ => .cons .snd .nil, Prod.snd, fun _ _ _ => rfl⟩

def swap (a b : Ty) : Certified Prim meaning (.prod a b) (.prod b a) :=
  ⟨fun _ => .cons .swap .nil, Prod.swap, fun _ _ _ => rfl⟩

/-- The temporary right component is pushed while the left code executes. -/
def first (f : Certified Prim meaning a b) (c : Ty) :
    Certified Prim meaning (.prod a c) (.prod b c) where
  code s := .cons .push ((f.code (c :: s)).append (.cons .pop .nil))
  spec p := (f.spec p.1, p.2)
  correct s x z := by
    change run meaning ((f.code (c :: s)).append (.cons .pop .nil))
      (x.1, (x.2, z)) = ((f.spec x.1, x.2), z)
    rw [run_append, f.correct]
    rfl

def second (f : Certified Prim meaning a b) (c : Ty) :
    Certified Prim meaning (.prod c a) (.prod c b) :=
  comp (swap b c) (comp (first f c) (swap c a))

/-- Right-to-left evaluation, matching the source calculation. -/
def pair (f : Certified Prim meaning a b) (g : Certified Prim meaning a c) :
    Certified Prim meaning a (.prod b c) :=
  comp (first f c) (comp (second g a) (dup a))

def square (f : Certified Prim meaning a b) (s : List Ty) :
    Squares.Square
      ⟨Val B a × Stack B s, Val B a, Prod.fst⟩
      ⟨Val B b × Stack B s, Val B b, Prod.fst⟩ where
  impl := run meaning (f.code s)
  spec := f.spec
  commutes x := congrArg Prod.fst (f.correct s x.1 x.2)

end Certified

def target {B : Type} (Prim : Ty → Ty → Type)
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) : Target Prim where
  Hom := Certified Prim meaning
  ident := Certified.ident _
  comp := Certified.comp
  terminal := Certified.terminal _
  fst := Certified.fst _ _
  snd := Certified.snd _ _
  pair := Certified.pair
  primitive := Certified.primitive

def sound {B : Type} (Prim : Ty → Ty → Type)
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) :
    Sound B (target Prim meaning) meaning where
  denote f := f.spec
  ident _ := rfl
  comp _ _ _ := rfl
  terminal _ := rfl
  fst _ := rfl
  snd _ := rfl
  pair _ _ _ := rfl
  primitive _ _ := rfl

/-- Source-to-bytecode correctness, including exact preservation of any tail. -/
theorem compile_correct {B : Type} {Prim : Ty → Ty → Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (t : Term Prim Γ a) (s : List Ty) (ρ : Val B (context Γ)) (z : Stack B s) :
    run meaning ((compile (target Prim meaning) t).code s) (ρ, z) =
      (eval meaning t ρ, z) := by
  rw [(compile (target Prim meaning) t).correct]
  exact congrArg (fun x => (x, z)) (compile_sound _ (sound Prim meaning) t ρ)

def compileSquare {B : Type} {Prim : Ty → Ty → Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)
    (t : Term Prim Γ a) (s : List Ty) :
    Squares.Square
      ⟨Val B (context Γ) × Stack B s, Val B (context Γ), Prod.fst⟩
      ⟨Val B a × Stack B s, Val B a, Prod.fst⟩ where
  impl := run meaning ((compile (target Prim meaning) t).code s)
  spec := eval meaning t
  commutes x := congrArg Prod.fst (compile_correct meaning t s x.1 x.2)

/-- Human-inspectable instruction sequence; stack effects remain in the types. -/
def listing (name : {a b : Ty} → Prim a b → String) :
    Program Prim a s b t → List String
  | .nil => []
  | .cons i p =>
    (match i with
    | .primitive p => name p
    | .terminal => "DROP"
    | .dup => "DUP"
    | .fst => "FST"
    | .snd => "SND"
    | .swap => "SWAP"
    | .push => "PUSH"
    | .pop => "POP") :: listing name p

end StackMachine
