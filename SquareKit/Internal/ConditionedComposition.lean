import SquareKit.Internal.Frobenius
import SquareKit.Internal.Associativity

/-! Reassociate two witnesses, then move a context condition under the outer binder. -/
namespace SquareKit.Internal.ConditionedComposition
universe u v
variable {S : Type u} {F P : S → S → Type u} {a b c d : S}

/-- The inner C witness remains under the B witness. -/
def body (r : P a b) (s : P b c) (t : P c d) : Formula F [b, a, d] P :=
  .conj (.atom r (.var (.succ .zero)) (.var .zero))
    (.ex (.conj (.atom s (.var (.succ .zero)) (.var .zero))
      (.atom t (.var .zero) (.var (.succ (.succ (.succ .zero)))))))

theorem forward (h : Formula F [a, d] P) (r : P a b) (s : P b c) (t : P c d) :
    Derives (.conj h (Associativity.left r s t)) (.ex (.conj h.shift (body r s t))) :=
  Rules.cut (Rules.andIntro Rules.andLeft
    (Rules.cut Rules.andRight (Associativity.forward r s t)))
    (Frobenius.forward h (body r s t))

theorem backward (h : Formula F [a, d] P) (r : P a b) (s : P b c) (t : P c d) :
    Derives (.ex (.conj h.shift (body r s t))) (.conj h (Associativity.left r s t)) :=
  Rules.cut (Frobenius.backward h (body r s t))
    (Rules.andIntro Rules.andLeft (Rules.cut Rules.andRight (Associativity.backward r s t)))

open Associativity (RelSort Arrow)
inductive Relation : RelSort → RelSort → Type where
  | first : Relation .input .first
  | second : Relation .first .second
  | third : Relation .second .output
  | condition : Relation .output .output

def model {A B C D : Type v} (R : A → B → Prop) (S : B → C → Prop)
    (T : C → D → Prop) (H : D → Prop) : Interpretation Arrow Relation where
  Carrier | .input => A | .first => B | .second => C | .output => D
  arrow f := nomatch f
  relation | .first => R | .second => S | .third => T | .condition => fun d _ => H d

def condition : Formula Arrow [.input, .output] Relation :=
  .atom .condition (.var (.succ .zero)) (.var (.succ .zero))

/-- Ordinary predicates, no new caller-side model obligations. -/
theorem inSet {A B C D : Type v} (R : A → B → Prop) (S : B → C → Prop)
    (T : C → D → Prop) (H : D → Prop) (a : A) (d : D) :
    (H d ∧ ∃ c, (∃ b, R a b ∧ S b c) ∧ T c d) ↔
      ∃ b, H d ∧ R a b ∧ ∃ c, S b c ∧ T c d := by
  let M := model R S T H
  let ρ : Env M [.input, .output] :=
    Env.extend a (Env.extend d (fun {_} (i : Var [] _) => nomatch i))
  exact ⟨sound M (forward condition .first .second .third) ρ,
    sound M (backward condition .first .second .third) ρ⟩
end SquareKit.Internal.ConditionedComposition
