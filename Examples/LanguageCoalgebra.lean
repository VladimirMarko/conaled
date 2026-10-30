import Applications.Languages.Coalgebra
import Applications.Languages.WitnessTrie
import Applications.Languages.ParserBridge
import Mathlib.Data.Matrix.Mul

namespace LanguageCoalgebraExamples
open SquareKit.WordCoalgebra LanguageCoalgebra
open LanguageWitnesses

/-- Finality applies to arbitrary observations, including natural-number state output. -/
def counter : Coalgebra Unit Nat Nat := fun n => (n, fun _ => n+1)
example : run counter 3 [(),()] = 5 := rfl
example (f : Nat → Behavior Unit Nat) (h : Morphism counter final f) : f = run counter :=
  unique counter f h
example (n m : Nat) (h : n ≤ m) : (unfold counter 3 m).truncate n h = unfold counter 3 n :=
  truncate_unfold counter 3 n m h

namespace Weights
open Weighted
abbrev R := Matrix (Fin 2) (Fin 2) Nat
def left : R := fun i j => if i = 0 ∧ j = 1 then 1 else 0
def right : R := fun i j => if i = 1 ∧ j = 0 then 1 else 0

def pairMachine : Coalgebra Unit R Bool := fun b => (if b then right else left, fun _ => b)
def semantics (b : Bool) : Convolution.Series Unit R := ⟨run pairMachine b⟩
def expression : Term R Bool := .concat (.leaf false) (.leaf true)

theorem interpretation : Morphism pairMachine final (fun b => (semantics b).coeff) :=
  run_morphism pairMachine

example : run (coalgebra pairMachine) expression [] = left * right :=
  run_correct interpretation expression []
example : (run (coalgebra pairMachine) expression []) 0 0 = 1 := by decide
example : (right * left) 0 0 = 0 := by decide

/-- The recursive concat rule preserves the same order at a nonempty word. -/
example (word : List Unit) : run (coalgebra pairMachine) expression word =
    (semantics false * semantics true) word := run_correct interpretation expression word
example : (run (coalgebra pairMachine) expression [()]) 0 0 = 2 := by decide

example (word : List Unit) :
    run (extended pairMachine) (Extended.old expression) word = run (coalgebra pairMachine) expression word :=
  old_recovered expression word
example (word : List Unit) :
    run (extended pairMachine) (.pointwise (Extended.old expression) (Extended.old (.leaf true))) word =
      (semantics false * semantics true) word * semantics true word :=
  extended_correct interpretation _ word
example (word : List Unit) (n : Nat) (h : word.length ≤ n) :
    (SquareKit.WordCoalgebra.unfold (coalgebra pairMachine) expression n).lookup word =
      some ((semantics false * semantics true) word) := by
  rw [lookup_unfold _ _ _ _ h, run_correct interpretation]
  rfl

example (word : List Unit) :
    run (extended pairMachine)
      (.concat (.pointwise (Extended.old (.leaf false)) (Extended.old (.leaf true)))
        (Extended.old expression)) word =
      (Convolution.Series.mk (fun w => semantics false w * semantics true w) *
        (semantics false * semantics true)) word :=
  extended_correct interpretation _ word

example : expression.bind Term.leaf = expression := Term.bind_id expression
end Weights

example (p : LanguageDerivatives.Regex Unit) (word : List Unit) (n : Nat)
    (h : word.length ≤ n) :
    ((LanguageWitnesses.WitnessTrie.unfold (LanguageDerivatives.compileProofParser p) n).lookup word h).test =
      LanguageDerivatives.recognize p word := by
  rw [LanguageWitnesses.WitnessTrie.lookup_unfold]
  exact LanguageDerivatives.recognizers_agree p word

namespace Parses
open WitnessTrie

def emptyWitness : epsilon (α := Unit) [] := ⟨rfl⟩
def noneEmpty : Star (epsilon (α := Unit)) [] := (nullableStarIso _).backward []
def oneEmpty : Star (epsilon (α := Unit)) [] := (nullableStarIso _).backward [emptyWitness]

theorem distinct : noneEmpty ≠ oneEmpty := by
  intro h
  have lists := congrArg (nullableStarIso (epsilon (α := Unit))).forward h
  change (nullableStarIso _).forward ((nullableStarIso _).backward []) =
    (nullableStarIso _).forward ((nullableStarIso _).backward [emptyWitness]) at lists
  rw [(nullableStarIso _).forward_backward, (nullableStarIso _).forward_backward] at lists
  cases lists

def first : WitnessTrie (Star (epsilon (α := Unit))) 0 := .leaf (.yes noneEmpty)
def second : WitnessTrie (Star (epsilon (α := Unit))) 0 := .leaf (.yes oneEmpty)

example : first.lookup [] (by decide) = .yes noneEmpty := rfl
example : second.lookup [] (by decide) = .yes oneEmpty := rfl
example : first.lookup [] (by decide) ≠ second.lookup [] (by decide) := by
  intro h
  exact distinct (Decision.yes.inj h)
example : (first.lookup [] (by decide)).test = (second.lookup [] (by decide)).test := rfl

example : WitnessTrie.unfold (.star (.epsilon (α := Unit))) 0 = first := rfl

/-- Exact selected decisions, not just inhabitation, agree at every admitted word. -/
example {P : LanguageWitnesses.Language Unit} (p : Parser P) (n : Nat) (word : List Unit)
    (h : word.length ≤ n) :
    (WitnessTrie.unfold p n).lookup word h = p.parse word := lookup_unfold p n word h

example {P Q : LanguageWitnesses.Language Unit} (p : Parser P) (q : Parser Q) (n : Nat)
    (word : List Unit) (h : word.length ≤ n) :
    (concat n (WitnessTrie.unfold p n) (WitnessTrie.unfold q n)).lookup word h =
      (Parser.concat p q).parse word := by
  rw [← unfold_concat]
  exact lookup_unfold _ _ _ _

example {P : LanguageWitnesses.Language Unit} (p : Parser P) (n : Nat) (word : List Unit)
    (h : word.length ≤ n) :
    (star n (WitnessTrie.unfold p n)).lookup word h = (Parser.star p).parse word := by
  rw [← unfold_star]
  exact lookup_unfold _ _ _ _

example {P : LanguageWitnesses.Language Unit} (p : Parser P) (n m : Nat) (h : n ≤ m) :
    WitnessTrie.truncate n h (WitnessTrie.unfold p m) = WitnessTrie.unfold p n :=
  WitnessTrie.truncate_unfold p n m h
end Parses
end LanguageCoalgebraExamples
