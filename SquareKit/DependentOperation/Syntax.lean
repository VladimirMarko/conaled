import SquareKit.DependentBranchSemantics

/-! A small intrinsically indexed operation language. Contexts supply selected
values at each index; substitution grafts typed terms. Primitive compilation
certificates and local meaning laws use the existing indexed rule machinery. -/
namespace SquareKit.DependentOperation
open DependentBranchTheoryMaps

abbrev Signature := Nat → Nat → Type

structure Label (O : Signature) where
  input : Nat
  output : Nat
  op : O input output

def rules (O : Signature) : Rules Nat where
  Label := Label O
  Arity _ := Unit
  premise r _ := r.input
  conclusion r := r.output

abbrev Term (O : Signature) (V : Nat → Type) (n : Nat) := Derivation (rules O) V n

def app {O : Signature} {V : Nat → Type} {n m : Nat} (o : O n m)
    (t : Term O V n) : Term O V m := .rule (R := rules O) ⟨n,m,o⟩ (fun _ => t)

abbrev Substitution (O : Signature) (V W : Nat → Type) := ∀ n, V n → Term O W n

def model {O : Signature} (A : Nat → Type)
    (operate : ∀ {n m}, O n m → A n → A m) : Model (rules O) A where
  rule r xs := operate r.op (xs ())

def eval {O : Signature} {V : Nat → Type} {A : Nat → Type}
    (operate : ∀ {n m}, O n m → A n → A m) (ρ : ∀ n, V n → A n)
    {n} (t : Term O V n) : A n := t.interpret (model A @operate) ρ

/-- This is the existing certificate interface specialized to indexed unary
operations, not another whole-program preservation field. -/
abbrev Compiler (O P : Signature) := TheoryMap (rules O) (rules P) id

def compile {O P : Signature} (F : Compiler O P) {V : Nat → Type} {n}
    (t : Term O V n) : Term P V n := F.transport (fun _ => id) t

/-- A linear executable carrier, without a derivation tree. The variable is
loaded once; the instruction list is executed in source order. -/
@[ext] structure Code (I : Type) (V : Nat → Type) where
  load : Sigma V
  instructions : List I

def emit {O : Signature} {V : Nat → Type} {I : Type}
    (instruction : ∀ {n m}, O n m → List I) : {n : Nat} → Term O V n → Code I V
  | _, .hyp v => ⟨⟨_,v⟩, []⟩
  | _, .rule r ts =>
    let c := emit instruction (ts ())
    ⟨c.load, c.instructions ++ instruction r.op⟩

def Code.run {I : Type} {V : Nat → Type} {R : Type}
    (execute : I → R → R) (ρ : ∀ n, V n → R) (c : Code I V) : R :=
  c.instructions.foldl (fun s i => execute i s) (ρ c.load.1 c.load.2)

/-- Quotation exposes the exact generated instruction word, not only a
successful execution or an existential result. -/
def Code.lower {I J : Type} {V : Nat → Type} (f : I → List J) (c : Code I V) : Code J V :=
  ⟨c.load, c.instructions.flatMap f⟩

end SquareKit.DependentOperation
