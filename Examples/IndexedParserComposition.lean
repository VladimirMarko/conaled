import Applications.Languages.IndexedCompositional
import Examples.LanguageCoalgebra

/-! Exact selected witnesses survive compound indexed union/transport terms. -/
namespace IndexedParserCompositionExamples
universe u v
variable {α : Type u}
open LanguageWitnesses SquareKit.IndexedCompositional
open LanguageWitnesses.IndexedCompositional

def swap (P Q : LanguageWitnesses.Language α) (w : List α) : Iso (P w ⊕ Q w) (Q w ⊕ P w) where
  forward := Sum.elim Sum.inr Sum.inl
  backward := Sum.elim Sum.inr Sum.inl
  backward_forward x := by cases x <;> rfl
  forward_backward x := by cases x <;> rfl

def unionTerm {X : Index α → Type v} {P Q : LanguageWitnesses.Language α} {n}
    (p : Term signature X (P,n)) (q : Term signature X (Q,n)) :
    Term signature X (fun w => P w ⊕ Q w,n) :=
  .node (.union P Q n) (fun k => Fin.cases p (fun _ => q) k)

def swapped {X : Index α → Type v} {P Q : LanguageWitnesses.Language α} {n}
    (p : Term signature X (P,n)) (q : Term signature X (Q,n)) :
    Term signature X (fun w => Q w ⊕ P w,n) :=
  .node (.transport _ _ n (swap P Q)) (fun _ => unionTerm p q)

open LanguageCoalgebraExamples.Parses
abbrev E := epsilon (α := Unit)
abbrev S := Star E
abbrev Z : LanguageWitnesses.Language Unit := fun _ => PEmpty

def selected (t : WitnessTrie S 0) : Term signature Target (fun w => Z w ⊕ S w,0) :=
  swapped (.leaf t) (.leaf (.leaf (.no (fun x => nomatch x))))

theorem selected_read (t : WitnessTrie S 0) :
    read (rule.lift target) (selected t) [] (by decide) =
      (Term.fold targetAlgebra (fun _ x => x) (selected t)).lookup [] (by decide) :=
  recovered_trie _ _ _

example : read (rule.lift target) (selected first) [] (by decide) = .yes (.inr noneEmpty) := by
  rw [selected_read]; rfl
example : read (rule.lift target) (selected second) [] (by decide) = .yes (.inr oneEmpty) := by
  rw [selected_read]; rfl
example : read (rule.lift target) (selected first) [] (by decide) ≠
    read (rule.lift target) (selected second) [] (by decide) := by
  rw [selected_read, selected_read]
  intro h
  exact distinct (Sum.inr.inj (Decision.yes.inj h))
example : (read (rule.lift target) (selected first) [] (by decide)).test =
    (read (rule.lift target) (selected second) [] (by decide)).test := rfl

def mixed : Term signature Source (fun w => E w ⊕ atom () w,1) :=
  swapped (.leaf (.atom ())) (.leaf (.epsilon))
example : (Term.fold targetAlgebra unfold mixed).lookup [()] (by decide) =
    (Term.fold sourceAlgebra (fun _ x => x) mixed).parse [()] :=
  recovered _ _ _

def concatTerm {X : Index α → Type v} {P Q : LanguageWitnesses.Language α} {n}
    (p : Term signature X (P,n)) (q : Term signature X (Q,n)) :
    Term signature X (Concat P Q,n) :=
  .node (.concat P Q n) (fun k => Fin.cases p (fun _ => q) k)

def starTerm {X : Index α → Type v} {P : LanguageWitnesses.Language α} {n}
    (p : Term signature X (P,n)) : Term signature X (Star P,n) :=
  .node (.star P n) (fun _ => p)

abbrev Nullable := fun w => E w ⊕ atom () w

def nullableTerm (n : Nat) : Term signature Source (Nullable,n) :=
  unionTerm (.leaf .epsilon) (.leaf (.atom ()))

/-- A nullable star, retained right operand, scalar evidence, intersection, and transport. -/
def fullMixed (n : Nat) : Term signature Source
    (fun w => (Unit × Concat (Star Nullable) (atom ()) w) × (Nullable w ⊕ Z w),n) :=
  .node (.intersection _ _ n) (fun k => Fin.cases
    (.node (.scale _ n (.yes ())) (fun _ =>
      concatTerm (starTerm (nullableTerm n)) (.leaf (.atom ()))))
    (fun _ => swapped (.leaf (.zero)) (nullableTerm n)) k)

example (n : Nat) (w : List Unit) (h : w.length ≤ n) :
    (Term.fold targetAlgebra unfold (fullMixed n)).lookup w h =
      (Term.fold sourceAlgebra (fun _ x => x) (fullMixed n)).parse w :=
  recovered _ _ _

example : ((Term.fold targetAlgebra unfold (fullMixed 1)).lookup [()] (by decide)).test = true := by
  rw [recovered]; decide

example : ((Term.fold targetAlgebra unfold (fullMixed 0)).lookup [] (by decide)).test = false := by
  rw [recovered]; decide

/-- Repeated restriction observes the same word without consuming its prefix. -/
example : (Term.fold targetAlgebra unfold (cutTerm (cutTerm (fullMixed 3)))).lookup [()] (by decide) =
    (Term.fold sourceAlgebra (fun _ x => x) (fullMixed 3)).parse [()] := by
  rw [fold_cut_twice, WitnessTrie.lookup_truncate, recovered]

/-- Nullable star still chooses the empty list at the empty word. -/
example : (Term.fold targetAlgebra unfold (starTerm (nullableTerm 0))).lookup [] (by decide) =
    .yes ⟨[], rfl⟩ := by
  rw [recovered]; rfl

/-- The shared proof recovers the same equality as the previous direct induction. -/
example (n : Nat) :
    WitnessTrie.unfold (.concat (.star (.union .epsilon (.atom ()))) (.atom ())) n =
      WitnessTrie.concat n (WitnessTrie.star n (WitnessTrie.unfold (.union .epsilon (.atom ())) n))
        (WitnessTrie.unfold (.atom ()) n) := by
  rw [← recovered_concat, ← recovered_star]

/-- A valid nonstandard selected nullable-star witness, at positive depth. -/
def retainedChoice : WitnessTrie S 1 :=
  .node (.yes oneEmpty) (fun a => WitnessTrie.unfold ((Parser.star Parser.epsilon).derive a) 0)

def retainedTerm : Term signature Target (S,0) := cutTerm (.leaf retainedChoice)

example : read (rule.lift target) retainedTerm [] (by decide) = .yes oneEmpty := by
  rw [recovered_trie]; rfl

/-- Resetting a retained nullable-star witness violates the exact output law.
Both decisions recognize the empty word, so Boolean correctness misses the error. -/
theorem resetting_cut_fails :
    (target (S,0) (Term.fold targetAlgebra (fun _ x => x) retainedTerm)).1 ≠
      (Decision.yes noneEmpty : Decision (S [])) := by
  change Decision.yes oneEmpty ≠ Decision.yes noneEmpty
  intro h
  exact distinct (Decision.yes.inj h).symm

example : (target (S,0) (Term.fold targetAlgebra (fun _ x => x) retainedTerm)).1.test =
    (Decision.yes noneEmpty : Decision (S [])).test := rfl

end IndexedParserCompositionExamples
