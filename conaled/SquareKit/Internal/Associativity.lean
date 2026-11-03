import SquareKit.Internal.Logic

/-! Existential relation composition: derivability and its Set interpretation. -/
namespace SquareKit.Internal.Associativity
universe u v
variable {S : Type u} {F P : S → S → Type u} {a b c d : S}

/-- First bind C, then B: (R ; S) ; T. -/
def left (r : P a b) (s : P b c) (t : P c d) : Formula F [a, d] P :=
  .ex (.conj
    (.ex (.conj (.atom r (.var (.succ (.succ .zero))) (.var .zero))
      (.atom s (.var .zero) (.var (.succ .zero)))))
    (.atom t (.var .zero) (.var (.succ (.succ .zero)))))

/-- First bind B, then C: R ; (S ; T). -/
def right (r : P a b) (s : P b c) (t : P c d) : Formula F [a, d] P :=
  .ex (.conj (.atom r (.var (.succ .zero)) (.var .zero))
    (.ex (.conj (.atom s (.var (.succ .zero)) (.var .zero))
      (.atom t (.var .zero) (.var (.succ (.succ (.succ .zero))))))))

theorem forward (r : P a b) (s : P b c) (t : P c d) :
    Derives (left (F := F) r s t) (right r s t) := by
  apply Rules.existsElim
  apply Rules.cut (Rules.andIntro Rules.andRight Rules.andLeft)
  apply Rules.existsElimWith
  apply Rules.existsWitness (.var .zero)
  apply Rules.andIntro
  · exact Rules.cut Rules.andRight Rules.andLeft
  · apply Rules.existsWitness (.var (.succ .zero))
    exact Rules.andIntro (Rules.cut Rules.andRight Rules.andRight) Rules.andLeft

theorem backward (r : P a b) (s : P b c) (t : P c d) :
    Derives (right (F := F) r s t) (left r s t) := by
  apply Rules.existsElim
  apply Rules.existsElimWith
  apply Rules.existsWitness (.var .zero)
  apply Rules.andIntro
  · apply Rules.existsWitness (.var (.succ .zero))
    exact Rules.andIntro Rules.andLeft (Rules.cut Rules.andRight Rules.andLeft)
  · exact Rules.cut Rules.andRight Rules.andRight

inductive RelSort where | input | first | second | output
abbrev Arrow (_ _ : RelSort) := Empty
inductive Relation : RelSort → RelSort → Type where
  | first : Relation .input .first
  | second : Relation .first .second
  | third : Relation .second .output

def model {A B C D : Type v} (R : A → B → Prop) (S : B → C → Prop)
    (T : C → D → Prop) : Interpretation Arrow Relation where
  Carrier | .input => A | .first => B | .second => C | .output => D
  arrow f := nomatch f
  relation | .first => R | .second => S | .third => T

def environment {A B C D : Type v} (R : A → B → Prop) (S : B → C → Prop)
    (T : C → D → Prop) (a : A) (d : D) : Env (model R S T) [.input, .output] :=
  Env.extend a (Env.extend d (fun {_} (i : Var [] _) => nomatch i))

/-- Validity is obtained from the derivations, without carrier assumptions. -/
theorem inSet {A B C D : Type v} (R : A → B → Prop) (S : B → C → Prop)
    (T : C → D → Prop) (a : A) (d : D) :
    (∃ c, (∃ b, R a b ∧ S b c) ∧ T c d) ↔
      (∃ b, R a b ∧ ∃ c, S b c ∧ T c d) :=
  ⟨sound (model R S T) (forward Relation.first Relation.second Relation.third)
      (environment R S T a d),
   sound (model R S T) (backward Relation.first Relation.second Relation.third)
      (environment R S T a d)⟩
end SquareKit.Internal.Associativity
