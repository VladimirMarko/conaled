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
end IndexedParserCompositionExamples
