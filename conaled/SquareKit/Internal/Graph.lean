import SquareKit.Internal.Logic

/-! The graph theorem first as two derivations, then as Set validity.
Experimental Set graph slice of issue #38. Scope and remaining model work:
`docs/research/internal-languages-lean.md`, Implemented Set graph slice.
-/
namespace SquareKit.Internal.Graph
universe u v
variable {S : Type u} {F : S → S → Type u} {a b c : S}

def body (f : F a b) (g : F b c) : Formula F [b, a, c] :=
  .conj (.eq (.var .zero) (.app f (.var (.succ .zero))))
    (.eq (.var (.succ (.succ .zero))) (.app g (.var .zero)))

def composite (f : F a b) (g : F b c) : Formula F [a, c] := .ex (body f g)

def result (f : F a b) (g : F b c) : Formula F [a, c] :=
  .eq (.var (.succ .zero)) (.app g (.app f (.var .zero)))

theorem forward (f : F a b) (g : F b c) : Derives (composite f g) (result f g) :=
  Rules.existsElim (Rules.eqTrans Rules.andRight (Rules.eqCongr g Rules.andLeft))

theorem backward (f : F a b) (g : F b c) : Derives (result f g) (composite f g) :=
  Rules.cut (Rules.andIntro Rules.eqRefl Rules.hypothesis)
    (Rules.existsIntro (body f g) (.app f (.var .zero)))

/-- Three distinct syntactic sorts, even when their carriers coincide. -/
inductive GraphSort where | input | middle | output
inductive Arrow : GraphSort → GraphSort → Type where
  | first : Arrow .input .middle
  | second : Arrow .middle .output

def model {A B C : Type v} (f : A → B) (g : B → C) : Interpretation Arrow where
  Carrier | .input => A | .middle => B | .output => C
  arrow | .first => f | .second => g

def environment {A B C : Type v} (f : A → B) (g : B → C) (a : A) (c : C) :
    Env (model f g) [.input, .output] :=
  Env.extend a (Env.extend c (fun {_} (i : Var [] _) => nomatch i))

/-- No inhabited-carrier premise: the witness in the reverse sequent is f(a). -/
theorem inSet {A B C : Type v} (f : A → B) (g : B → C) (a : A) (c : C) :
    (∃ b, b = f a ∧ c = g b) ↔ c = g (f a) :=
  ⟨sound (model f g) (forward Arrow.first Arrow.second) (environment f g a c),
   sound (model f g) (backward Arrow.first Arrow.second) (environment f g a c)⟩
end SquareKit.Internal.Graph
