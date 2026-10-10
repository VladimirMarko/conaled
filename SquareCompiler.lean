import Compiler
import Squares

/-!
# A compiler whose target arrows are actual commuting squares

`target` instantiates the generic compiler from `Compiler.lean` with the
arrow-category operations from `Squares.lean`. A base representation is an
arbitrary function from runtime data to semantic data. No encoder, inverse,
injectivity, or surjectivity is assumed.

`compile_commutes` is the end-to-end theorem: decoding the compiled runtime
result equals evaluating the source in the decoded runtime environment.
It applies to the whole source language, including lambdas and case splits.

At function types, the runtime carrier is the arrow-category exponential:
an implementation function, a specification function, and a compatibility
proof. Lean erases the proof, but does not thereby erase the specification
function. This construction proves correctness for that explicit enriched
representation; it does not claim a closure-conversion or erasure theorem.
-/

namespace SquareCompiler

open CategoricalCompiler

/-- A representation with its semantic carrier fixed in the index. -/
structure Encoding (S : Type) where
  R : Type
  decode : R → S

def Encoding.asRep {S : Type} (E : Encoding S) : Squares.Rep where
  R := E.R
  S := S
  decode := E.decode

/--
Indexing by `Val` makes semantic carriers definitionally equal to the source
interpretation while retaining arbitrary base decoding.
-/
def encoding (base : Squares.Rep.{0}) : (a : Ty) → Encoding (Val base.S a)
  | .base => ⟨base.R, base.decode⟩
  | .unit => ⟨Unit, fun x => x⟩
  | .prod a b =>
      ⟨(encoding base a).R × (encoding base b).R,
        fun p => ((encoding base a).decode p.1, (encoding base b).decode p.2)⟩
  | .arr a b =>
      ⟨Squares.FunctionRep (encoding base a).asRep (encoding base b).asRep,
        fun f => f.val.2⟩
  | .sum a b =>
      ⟨Sum (encoding base a).R (encoding base b).R,
        Sum.elim (fun x => .inl ((encoding base a).decode x))
          (fun y => .inr ((encoding base b).decode y))⟩

def objectInterp (base : Squares.Rep.{0}) (a : Ty) : Squares.Rep :=
  (encoding base a).asRep

theorem objectInterp_semantics (base : Squares.Rep.{0}) (a : Ty) :
    (objectInterp base a).S = Val base.S a := rfl

/-- All backend-specific work is localized to primitive runtime operations. -/
structure PrimitiveImpl (base : Squares.Rep.{0}) (Prim : Ty → Ty → Type)
    (meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b) where
  impl : {a b : Ty} → Prim a b → (objectInterp base a).R → (objectInterp base b).R
  correct : ∀ {a b} (p : Prim a b) x,
    (objectInterp base b).decode (impl p x) = meaning p ((objectInterp base a).decode x)

def primitiveSquare {base : Squares.Rep.{0}} {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : PrimitiveImpl base Prim meaning) {a b : Ty} (p : Prim a b) :
    Squares.Square (objectInterp base a) (objectInterp base b) where
  impl := P.impl p
  spec := meaning p
  commutes := P.correct p

/-- Products, exponentials, sums, and distribution, with their full squares. -/
def target (base : Squares.Rep.{0}) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : PrimitiveImpl base Prim meaning) : Target Prim where
  Hom := fun a b => Squares.Square (objectInterp base a) (objectInterp base b)
  ident := fun {a} => Squares.identity (objectInterp base a)
  comp := fun {a b c} => @Squares.compose (objectInterp base a)
    (objectInterp base b) (objectInterp base c)
  terminal := {
    impl := fun _ => ()
    spec := fun _ => ()
    commutes := fun _ => rfl }
  fst := fun {a b} => Squares.first (objectInterp base a) (objectInterp base b)
  snd := fun {a b} => Squares.second (objectInterp base a) (objectInterp base b)
  pair := fun {a b c} => @Squares.pair (objectInterp base a)
    (objectInterp base b) (objectInterp base c)
  curry := fun {a b c} => @Squares.curry (objectInterp base a)
    (objectInterp base b) (objectInterp base c)
  apply := fun {a b} => Squares.evaluation (objectInterp base a) (objectInterp base b)
  inl := fun {a b} => Squares.injectLeft (objectInterp base a) (objectInterp base b)
  inr := fun {a b} => Squares.injectRight (objectInterp base a) (objectInterp base b)
  copair := fun {a b c} => @Squares.copair (objectInterp base a)
    (objectInterp base b) (objectInterp base c)
  dist := fun {a b c} => Squares.distribution (objectInterp base a)
    (objectInterp base b) (objectInterp base c)
  primitive := primitiveSquare P

/-- The semantic edge of a square validates the generic compiler interface. -/
def sound (base : Squares.Rep.{0}) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : PrimitiveImpl base Prim meaning) : Sound base.S (target base P) meaning where
  denote := fun f => f.spec
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
  dist := fun x => by
    cases x with
    | mk a bc => cases bc <;> rfl
  primitive := fun _ _ => rfl

/-- The lower edge of the compiled square is the source denotation. -/
theorem compile_spec (base : Squares.Rep.{0}) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : PrimitiveImpl base Prim meaning) (t : Term Prim Γ a)
    (ρ : Val base.S (context Γ)) :
    (compile (target base P) t).spec ρ = eval meaning t ρ :=
  compile_sound (target base P) (sound base P) t ρ

/--
The actual decoder/implementation/source square commutes for every runtime
environment, for arbitrary base representations and every source term.
-/
theorem compile_commutes (base : Squares.Rep.{0}) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : PrimitiveImpl base Prim meaning) (t : Term Prim Γ a)
    (ρ : (objectInterp base (context Γ)).R) :
    (objectInterp base a).decode ((compile (target base P) t).impl ρ) =
      eval meaning t ((objectInterp base (context Γ)).decode ρ) :=
  ((compile (target base P) t).commutes ρ).trans
    (compile_spec base P t ((objectInterp base (context Γ)).decode ρ))

/-- Correctness also relates the actual application of a compiled function. -/
theorem compile_apply_commutes (base : Squares.Rep.{0}) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : PrimitiveImpl base Prim meaning) (t : Term Prim Γ (.arr a b))
    (ρ : (objectInterp base (context Γ)).R) (x : (objectInterp base a).R) :
    (objectInterp base b).decode (((compile (target base P) t).impl ρ).val.1 x) =
      eval meaning t ((objectInterp base (context Γ)).decode ρ)
        ((objectInterp base a).decode x) :=
  (((compile (target base P) t).impl ρ).property x).trans
    (congrArg (fun f => f ((objectInterp base a).decode x))
      (compile_commutes base P t ρ))

/-- Return the implementation and the source evaluator in one certified square. -/
def compileSquare (base : Squares.Rep.{0}) {Prim : Ty → Ty → Type}
    {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
    (P : PrimitiveImpl base Prim meaning) (t : Term Prim Γ a) :
    Squares.Square (objectInterp base (context Γ)) (objectInterp base a) where
  impl := (compile (target base P) t).impl
  spec := eval meaning t
  commutes := compile_commutes base P t

/-! ## A redundant representation, including a compiled lambda

Runtime naturals carry an extra Boolean tag. Decoding forgets the tag, while
the primitive increments the natural and flips the tag. The source has no
way to observe that flip. The representation is provably noninjective.
-/

def taggedNat : Squares.Rep where
  R := Nat × Bool
  S := Nat
  decode := Prod.fst

theorem taggedNat_redundant :
    ∃ x y : taggedNat.R, x ≠ y ∧ taggedNat.decode x = taggedNat.decode y := by
  refine ⟨(7, false), (7, true), ?_, rfl⟩
  intro h
  have impossible : false = true := congrArg Prod.snd h
  cases impossible

inductive Prim : Ty → Ty → Type where
  | increment : Prim .base .base

def meaning : {a b : Ty} → Prim a b → Val Nat a → Val Nat b
  | _, _, .increment => fun n => n + 1

def primitives : PrimitiveImpl taggedNat Prim meaning where
  impl := fun p => match p with
    | .increment => fun x => (x.1 + 1, !x.2)
  correct := fun p x => by cases p; rfl

def incrementOpen : Term Prim [.base] .base :=
  .prim .increment (.var .here)

def incrementTwice : Term Prim [] (.arr .base .base) :=
  .lam (.prim .increment (.prim .increment (.var .here)))

/-- The top edge really changes the hidden tag. -/
example : (compile (target taggedNat primitives) incrementOpen).impl ((), (41, false)) =
    (42, true) := rfl

/-- The end-to-end theorem still relates that runtime result to the source. -/
theorem incrementOpen_correct (n : Nat) (tag : Bool) :
    taggedNat.decode
        ((compile (target taggedNat primitives) incrementOpen).impl ((), (n, tag))) =
      n + 1 :=
  compile_commutes taggedNat primitives incrementOpen ((), (n, tag))

/-- Executing the compiled function retains its certified enriched carrier. -/
example : ((compile (target taggedNat primitives) incrementTwice).impl ()).val.1
    (41, false) = (43, false) := rfl

/-- Both the implementation and its specification compute the same natural. -/
theorem incrementTwice_correct (n : Nat) (tag : Bool) :
    taggedNat.decode
        (((compile (target taggedNat primitives) incrementTwice).impl ()).val.1 (n, tag)) =
      n + 1 + 1 :=
  compile_apply_commutes taggedNat primitives incrementTwice () (n, tag)

/-- Left increments its payload; right returns the captured outer variable. -/
def branchWithCapture : Term Prim [.base, .sum .base .base] .base :=
  .caseE (.var (.there .here))
    (.prim .increment (.var .here))
    (.var (.there .here))

example : (compile (target taggedNat primitives) branchWithCapture).impl
    (((), .inl (5, false)), (99, true)) = (6, true) := rfl

example : (compile (target taggedNat primitives) branchWithCapture).impl
    (((), .inr (5, false)), (99, true)) = (99, true) := rfl

end SquareCompiler
