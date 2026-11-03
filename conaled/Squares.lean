import Lean

/-!
# Correct computations as commutative squares

This file is independent of Felix and of the compiler in `Compiler.lean`.  It gives
the concrete arrow-category construction in Lean's category of types and
functions.  In Felix terminology, `Rep` is an object of the arrow category and
`Square` is one of its morphisms.

All input and output data interpretations may be arbitrary functions: they
need not be injective, surjective, or invertible.  Products are componentwise.
Exponentials are *not* componentwise: a represented function contains an
implementation function, a specification function, and their compatibility
proof.  Its data interpretation selects the specification function.

The specification function in this exponential is computational data in
`Type`, not a proof in `Prop`.  Lean erases the compatibility proof, but this
construction alone does not justify erasing the specification function.  A
practical compiler may use a different, separately justified representation
of functions (for example a closure representation with a logical relation).

There are no `sorry`s or additional axioms in this file.  Equality proofs use
Lean's ordinary function extensionality and proof irrelevance.
-/

universe u

namespace Squares

/-- A runtime carrier, an ideal carrier, and the meaning of runtime data. -/
structure Rep where
  R : Type u
  S : Type u
  decode : R → S

/-- A computation together with its purpose and its commuting square. -/
structure Square (A B : Rep.{u}) where
  impl : A.R → B.R
  spec : A.S → B.S
  commutes : ∀ x, B.decode (impl x) = spec (A.decode x)

/-- Square equality observes both horizontal arrows, not proof terms. -/
theorem Square.ext {A B : Rep.{u}} {f g : Square A B}
    (hi : ∀ x, f.impl x = g.impl x)
    (hs : ∀ x, f.spec x = g.spec x) : f = g := by
  cases f with
  | mk fi fs fp =>
    cases g with
    | mk gi gs gp =>
      have ei : fi = gi := funext hi
      have es : fs = gs := funext hs
      cases ei
      cases es
      rfl

def identity (A : Rep.{u}) : Square A A where
  impl := fun x => x
  spec := fun x => x
  commutes := fun _ => rfl

/-- Horizontal pasting: compose implementations and specifications together. -/
def compose {A B C : Rep.{u}} (g : Square B C) (f : Square A B) : Square A C where
  impl := fun x => g.impl (f.impl x)
  spec := fun x => g.spec (f.spec x)
  commutes := fun x =>
    (g.commutes (f.impl x)).trans (congrArg g.spec (f.commutes x))

theorem compose_identity {A B : Rep.{u}} (f : Square A B) :
    compose f (identity A) = f :=
  Square.ext (fun _ => rfl) (fun _ => rfl)

theorem identity_compose {A B : Rep.{u}} (f : Square A B) :
    compose (identity B) f = f :=
  Square.ext (fun _ => rfl) (fun _ => rfl)

theorem compose_assoc {A B C D : Rep.{u}}
    (h : Square C D) (g : Square B C) (f : Square A B) :
    compose h (compose g f) = compose (compose h g) f :=
  Square.ext (fun _ => rfl) (fun _ => rfl)

/-- Follow one data interpretation with another. -/
def Rep.after (A : Rep.{u}) {T : Type u} (d : A.S → T) : Rep.{u} where
  R := A.R
  S := T
  decode := fun x => d (A.decode x)

/--
Vertical pasting composes data interpretations.  The middle computation is
allowed to be extensionally equal, rather than definitionally identical.
-/
def vertical {A B : Rep.{u}} {AS BS : Type u}
    (da : A.S → AS) (db : B.S → BS)
    (f : Square A B)
    (g : Square (Rep.mk A.S AS da) (Rep.mk B.S BS db))
    (middle : ∀ x, f.spec x = g.impl x) :
    Square (A.after da) (B.after db) where
  impl := f.impl
  spec := g.spec
  commutes := fun x =>
    (congrArg db (f.commutes x)).trans
      ((congrArg db (middle (A.decode x))).trans (g.commutes (A.decode x)))

/-! ## Terminal object and products -/

def terminal : Rep.{u} where
  R := PUnit.{u + 1}
  S := PUnit.{u + 1}
  decode := fun _ => PUnit.unit

def terminate (A : Rep.{u}) : Square A terminal where
  impl := fun _ => PUnit.unit
  spec := fun _ => PUnit.unit
  commutes := fun _ => rfl

theorem terminal_unique {A : Rep.{u}} (f : Square A terminal) :
    f = terminate A := by
  apply Square.ext
  · intro x
    cases f.impl x
    rfl
  · intro x
    cases f.spec x
    rfl

def product (A B : Rep.{u}) : Rep.{u} where
  R := A.R × B.R
  S := A.S × B.S
  decode := fun p => (A.decode p.1, B.decode p.2)

def first (A B : Rep.{u}) : Square (product A B) A where
  impl := Prod.fst
  spec := Prod.fst
  commutes := fun _ => rfl

def second (A B : Rep.{u}) : Square (product A B) B where
  impl := Prod.snd
  spec := Prod.snd
  commutes := fun _ => rfl

def pair {X A B : Rep.{u}} (f : Square X A) (g : Square X B) :
    Square X (product A B) where
  impl := fun x => (f.impl x, g.impl x)
  spec := fun x => (f.spec x, g.spec x)
  commutes := fun x => Prod.ext (f.commutes x) (g.commutes x)

def productMap {A B C D : Rep.{u}} (f : Square A C) (g : Square B D) :
    Square (product A B) (product C D) :=
  pair (compose f (first A B)) (compose g (second A B))

theorem first_pair {X A B : Rep.{u}} (f : Square X A) (g : Square X B) :
    compose (first A B) (pair f g) = f :=
  Square.ext (fun _ => rfl) (fun _ => rfl)

theorem second_pair {X A B : Rep.{u}} (f : Square X A) (g : Square X B) :
    compose (second A B) (pair f g) = g :=
  Square.ext (fun _ => rfl) (fun _ => rfl)

theorem pair_eta {X A B : Rep.{u}} (f : Square X (product A B)) :
    pair (compose (first A B) f) (compose (second A B) f) = f :=
  Square.ext (fun _ => rfl) (fun _ => rfl)

/-! ## Coproducts and distribution

Sums, like products, are interpreted componentwise. Distribution is the
square used to compile a case split whose branches can use their environment.
-/

def coproduct (A B : Rep.{u}) : Rep.{u} where
  R := Sum A.R B.R
  S := Sum A.S B.S
  decode := Sum.elim (fun a => .inl (A.decode a)) (fun b => .inr (B.decode b))

def injectLeft (A B : Rep.{u}) : Square A (coproduct A B) where
  impl := Sum.inl
  spec := Sum.inl
  commutes := fun _ => rfl

def injectRight (A B : Rep.{u}) : Square B (coproduct A B) where
  impl := Sum.inr
  spec := Sum.inr
  commutes := fun _ => rfl

def copair {A B C : Rep.{u}} (f : Square A C) (g : Square B C) :
    Square (coproduct A B) C where
  impl := Sum.elim f.impl g.impl
  spec := Sum.elim f.spec g.spec
  commutes := fun x => by
    cases x with
    | inl a => exact f.commutes a
    | inr b => exact g.commutes b

theorem copair_left {A B C : Rep.{u}} (f : Square A C) (g : Square B C) :
    compose (copair f g) (injectLeft A B) = f :=
  Square.ext (fun _ => rfl) (fun _ => rfl)

theorem copair_right {A B C : Rep.{u}} (f : Square A C) (g : Square B C) :
    compose (copair f g) (injectRight A B) = g :=
  Square.ext (fun _ => rfl) (fun _ => rfl)

theorem copair_eta {A B C : Rep.{u}} (h : Square (coproduct A B) C) :
    copair (compose h (injectLeft A B)) (compose h (injectRight A B)) = h := by
  apply Square.ext
  · intro x
    cases x <;> rfl
  · intro x
    cases x <;> rfl

def distribution (A B C : Rep.{u}) :
    Square (product A (coproduct B C))
      (coproduct (product A B) (product A C)) where
  impl := fun p => match p.2 with
    | .inl b => .inl (p.1, b)
    | .inr c => .inr (p.1, c)
  spec := fun p => match p.2 with
    | .inl b => .inl (p.1, b)
    | .inr c => .inr (p.1, c)
  commutes := fun p => by
    cases p with
    | mk a bc => cases bc <;> rfl

/-! ## The exponential in the arrow category

For interpretations r : AR → AS and s : BR → BS, its runtime carrier is

  { (fR, fS) : (AR → BR) × (AS → BS) // ∀ a, s (fR a) = fS (r a) }.

This is the pullback of postcomposition with s and precomposition with r.
The ideal carrier is AS → BS, and decoding is projection to fS.
-/

def FunctionRep (A B : Rep.{u}) : Type u :=
  { p : (A.R → B.R) × (A.S → B.S) //
      ∀ a, B.decode (p.1 a) = p.2 (A.decode a) }

def exponential (A B : Rep.{u}) : Rep.{u} where
  R := FunctionRep A B
  S := A.S → B.S
  decode := fun f => f.val.2

def evaluation (A B : Rep.{u}) : Square (product (exponential A B) A) B where
  impl := fun p => p.1.val.1 p.2
  spec := fun p => p.1 p.2
  commutes := fun p => p.1.property p.2

/--
The implementation of currying packages its runtime function with the
specification specialized at the decoded environment.  The body's existing
square supplies the required compatibility proof.
-/
def curry {X A B : Rep.{u}} (h : Square (product X A) B) :
    Square X (exponential A B) where
  impl := fun x =>
    ⟨(fun a => h.impl (x, a), fun a => h.spec (X.decode x, a)),
      fun a => h.commutes (x, a)⟩
  spec := fun x a => h.spec (x, a)
  commutes := fun _ => rfl

def uncurry {X A B : Rep.{u}} (k : Square X (exponential A B)) :
    Square (product X A) B where
  impl := fun p => (k.impl p.1).val.1 p.2
  spec := fun p => k.spec p.1 p.2
  commutes := fun p =>
    ((k.impl p.1).property p.2).trans
      (congrArg (fun f => f (A.decode p.2)) (k.commutes p.1))

/-- Uncurrying is evaluation after applying the function-producing square. -/
theorem uncurry_evaluation {X A B : Rep.{u}}
    (k : Square X (exponential A B)) :
    uncurry k = compose (evaluation A B) (productMap k (identity A)) :=
  Square.ext (fun _ => rfl) (fun _ => rfl)

/-- The beta law holds for the entire square, including both computations. -/
theorem uncurry_curry {X A B : Rep.{u}} (h : Square (product X A) B) :
    uncurry (curry h) = h :=
  Square.ext (fun _ => rfl) (fun _ => rfl)

/--
The eta law uses the input square's correctness to identify the semantic
function repackaged by `curry` with the one already stored in the value.
-/
theorem curry_uncurry {X A B : Rep.{u}}
    (k : Square X (exponential A B)) : curry (uncurry k) = k := by
  apply Square.ext
  · intro x
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (k.commutes x).symm
  · intro x
    rfl

/-- The exponential universal property, with equality of complete squares. -/
theorem curry_unique {X A B : Rep.{u}} (h : Square (product X A) B)
    (k : Square X (exponential A B)) :
    uncurry k = h ↔ k = curry h := by
  constructor
  · intro e
    calc
      k = curry (uncurry k) := (curry_uncurry k).symm
      _ = curry h := congrArg curry e
  · intro e
    cases e
    exact uncurry_curry h

/-- Currying is natural in the environment, including noninvertible decoding. -/
theorem curry_natural {X Y A B : Rep.{u}} (h : Square (product X A) B)
    (f : Square Y X) :
    curry (compose h (productMap f (identity A))) = compose (curry h) f := by
  apply Square.ext
  · intro y
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply funext
      intro a
      exact congrArg (fun x => h.spec (x, a)) (f.commutes y).symm
  · intro y
    rfl

/-! ## Why ordinary runtime function spaces are insufficient

The input interpretation below forgets a Boolean entirely.  A correct
implementation must therefore be observationally constant.  In particular,
the runtime identity function cannot be the top edge of any square to the
exact Boolean representation.  This is a direct obstruction to a universal
decoder of *all* functions AR → BR when interpretations are arbitrary.
-/

def forgetBool : Rep where
  R := Bool
  S := Unit
  decode := fun _ => ()

def exactBool : Rep where
  R := Bool
  S := Bool
  decode := fun b => b

def constantBool (b : Bool) : Square forgetBool exactBool where
  impl := fun _ => b
  spec := fun _ => b
  commutes := fun _ => rfl

theorem no_boolean_identity_square (f : Square forgetBool exactBool)
    (h : ∀ b, f.impl b = b) : False := by
  have hf : false = f.spec () := (h false).symm.trans (f.commutes false)
  have ht : true = f.spec () := (h true).symm.trans (f.commutes true)
  have impossible : false = true := hf.trans ht.symm
  cases impossible

end Squares
