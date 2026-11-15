import SquareKit.ObservationExtension
import Applications.Languages.ParserBridge
import Examples.LanguageExtension

/-! Recognition and FIFO clients exercise compatible and incompatible observers.
The parser counterexample keeps the selected decision, not just its success bit. -/
namespace Examples.ObservationExtension
open SquareKit.ObservationExtension

namespace Parsing
open LanguageWitnesses LanguageDerivatives

/-- Ambiguity is represented by two distinct epsilon witnesses. -/
abbrev P : LanguageWitnesses.Language Char := witnessLanguage (.plus .epsilon .epsilon)

def left : Parser P := compileProofParser (.plus .epsilon .epsilon)

def swap (w : List Char) : Iso (P w) (P w) where
  forward := Sum.swap
  backward := Sum.swap
  backward_forward := by intro x; cases x <;> rfl
  forward_backward := by intro x; cases x <;> rfl

def right : Parser P := .transport swap left

/-- Old observations are recognition at every word; no bound or enumeration. -/
def recognition : Setoid (Parser P) :=
  agreement (fun w p => (p.parse w).test) Set.univ

/-- This existing correctness proof is unchanged by adding a witness observer. -/
theorem old_agreement (p q : Parser P) : recognition.r p q := by
  intro w _
  have hp := Parser.parse_correct p w
  have hq := Parser.parse_correct q w
  cases h₁ : (p.parse w).test <;> cases h₂ : (q.parse w).test <;> simp_all

/-- The bridge to the independently defined regex recognizer remains available. -/
theorem old_bridge (w : List Char) :
    (left.parse w).test = recognize (.plus .epsilon .epsilon) w :=
  recognizers_agree _ _

def selected (p : Parser P) : Decision (P []) := p.parse []

/-- The actual parser results choose opposite alternatives at the same index. -/
theorem selected_different : selected left ≠ selected right := by
  intro h
  change Decision.yes (Sum.inl (Evidence.mk rfl)) =
    Decision.yes (Sum.inr (Evidence.mk rfl)) at h
  cases h

theorem selected_incompatible : ¬ Compatible recognition selected := by
  intro h
  exact selected_different (h (old_agreement left right))

theorem selected_no_factor :
    ¬ ∃ f : Quotient recognition → Decision (P []),
      ∀ p, f (Quotient.mk recognition p) = selected p :=
  no_factor recognition selected (old_agreement left right) selected_different

theorem refined_distinguishes : ¬ (extend recognition selected).r left right :=
  fun h => selected_different h.2

/-- Forgetting the new observation recovers every old word observation. -/
theorem refined_recognition {p q : Parser P}
    (h : (extend recognition selected).r p q) (w : List Char) :
    (p.parse w).test = (q.parse w).test :=
  extend_restrict recognition selected h w (Set.mem_univ w)

/-- Selected decisions for all words form an indexed family, without erasing P w. -/
def witnessAgreement (words : Set (List Char)) : Setoid (Parser P) :=
  agreement (fun w p => p.parse w) words

theorem restrict_words {small large : Set (List Char)} (h : small ⊆ large)
    {p q : Parser P} (hpq : (witnessAgreement large).r p q) :
    (witnessAgreement small).r p q := restrict _ h hpq

end Parsing

namespace FIFO
open Sequences.AbstractFIFO Sequences.Symmetric Examples.AbstractFIFO
open CategoricalCompiler SquareKit

/-- Restrict to valid representations; equality observes the decoded sequence. -/
abbrev State := {q : SymList Nat // Inv q}

def contents (q : State) : List Nat := fromSL q.val

def old : Setoid State := agreement (fun _ : Unit => contents) Set.univ

def rotated (cs : List (Command Nat)) (q : State) : Option Nat :=
  (symmetric Nat).head ((compile
    (STLCRelations.target _ (Extension.primitives (symmetric Nat) _ (symmetric_correct Nat)))
    (Extension.program cs)).impl ((),q.val))

/-- The author's new square is discharged by the existing public client theorem. -/
theorem rotated_square (cs : List (Command Nat)) (q : State) :
    rotated cs q = client (lists Nat) cs (Extension.rotate (lists Nat) (contents q)) :=
  Extension.observe _ _ (symmetric_correct Nat) cs ⟨q.property, rfl⟩

theorem rotated_compatible (cs : List (Command Nat)) : Compatible old (rotated cs) :=
  compatible_of_factor old contents (fun {_ _} h => h () (Set.mem_univ ())) (rotated cs)
    (fun xs => client (lists Nat) cs (Extension.rotate (lists Nat) xs)) (rotated_square cs)

/-- Adding rotation as an observer retains exactly the old identification. -/
theorem admitted (cs : List (Command Nat)) (x y : State) :
    (extend old (rotated cs)).r x y ↔ old.r x y :=
  extend_iff old (rotated cs) (rotated_compatible cs) x y

/-- The unchanged old proof consumes the restricted contract, for any old program. -/
theorem old_client (extra cs : List (Command Nat)) {x y : State}
    (h : (extend old (rotated extra)).r x y) :
    client (symmetric Nat) cs x.val = client (symmetric Nat) cs y.val := by
  have hc := extend_restrict old (rotated extra) h () (Set.mem_univ ())
  exact (symmetric_correct Nat).representation_independent cs
    (r := contents x) ⟨x.property, rfl⟩ ⟨y.property, hc.symm⟩

def leftState : State := ⟨leftLayout, left_related.1⟩
def rightState : State := ⟨rightLayout, right_related.1⟩

theorem same_contents : old.r leftState rightState := fun _ _ => rfl

theorem admitted_pair : (extend old (rotated [.delete])).r leftState rightState :=
  (admitted _ _ _).mpr same_contents

/-- [1,2,3] rotates to [2,3,1], then deletion leaves [3,1]. -/
theorem rotated_value : rotated [.delete] leftState = some 3 :=
  (rotated_square _ _).trans rfl

theorem old_client_pair (cs : List (Command Nat)) :
    client (symmetric Nat) cs leftLayout = client (symmetric Nat) cs rightLayout :=
  old_client [.delete] cs admitted_pair

def reveal (q : State) := Examples.LanguageExtension.revealFront q.val

theorem reveal_different : reveal leftState ≠ reveal rightState := by decide

theorem reveal_incompatible : ¬ Compatible old reveal :=
  fun h => reveal_different (h same_contents)

theorem reveal_no_factor :
    ¬ ∃ f : Quotient old → Sum Unit Unit,
      ∀ q, f (Quotient.mk old q) = reveal q :=
  no_factor old reveal same_contents reveal_different

/-- Admitted observers really have an interpretation on the old quotient. -/
example (cs : List (Command Nat)) (q : State) :
    descend old (rotated cs) (rotated_compatible cs) (Quotient.mk old q) = rotated cs q :=
  descend_mk _ _ _ _

end FIFO
end Examples.ObservationExtension
