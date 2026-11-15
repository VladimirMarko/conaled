import Applications.Languages.ExactRewrites
import Examples.ObservationExtension

namespace ExactParserRewrites
open LanguageWitnesses SquareKit.IndexedCompositional
open LanguageWitnesses.IndexedCompositional

-- Toggling a Boolean witness and then exchanging product fields gives (unit,false).
def toggle : Iso (Bool × PUnit) (Bool × PUnit) where
  forward x := (!x.1, x.2)
  backward x := (!x.1, x.2)
  backward_forward x := by cases x with | mk b u => cases b <;> rfl
  forward_backward x := by cases x with | mk b u => cases b <;> rfl

def exchange : Iso (Bool × PUnit) (PUnit × Bool) where
  forward x := (x.2,x.1)
  backward x := (x.2,x.1)
  backward_forward _ := rfl
  forward_backward _ := rfl

abbrev Result : LanguageWitnesses.Language Unit := fun _ => PUnit × Bool

def site (n : Nat) : TransportPair (Result,n) :=
  ⟨(fun _ => Bool × PUnit), (fun _ => Bool × PUnit),
    (fun _ => toggle), (fun _ => exchange), .scale (.yes true) .universal⟩

example : (Term.fold sourceAlgebra (fun _ p => p)
    (TransportPair.expanded _ (site 1))).parse [()] = .yes (⟨⟩, false) := by
  calc
    _ = (Term.fold sourceAlgebra (fun _ p => p)
      (TransportPair.fused _ (site 1))).parse [()] :=
        contextual_transport_trans (.leaf (site 1)) [()] (by decide)
    _ = _ := rfl

-- The rewritten site sits below star, concatenation and a depth restriction.
def surrounding : Term signature TransportPair (Concat (Star Result) Result,1) :=
  cutTerm (.node (.concat (Star Result) Result 2) (fun k => Fin.cases
    (.node (.star Result 2) (fun _ => .leaf (site 2)))
    (fun _ => .leaf (site 2)) k))

example : (Term.fold sourceAlgebra (fun _ p => p)
    (surrounding.bind TransportPair.expanded)).parse [()] =
    (Term.fold sourceAlgebra (fun _ p => p)
      (surrounding.bind TransportPair.fused)).parse [()] :=
  contextual_transport_trans surrounding [()] (by decide)

example : Term.fold targetAlgebra unfold (surrounding.bind TransportPair.expanded) =
    Term.fold targetAlgebra unfold (surrounding.bind TransportPair.fused) :=
  contextual_tree TransportPair.expanded TransportPair.fused (fun j s w _ => by
    rcases j with ⟨R,m⟩
    exact Parser.parse_transport_trans s.first s.second s.parser w)
    surrounding

-- Eliminating identity conversions also preserves the non-leftmost choice.
def alternatives : Term signature Source (fun w => atom 'a' w ⊕ epsilon w,0) :=
  .node (.union (atom 'a') epsilon 0) (fun k => Fin.cases
    (.leaf (.atom 'a')) (fun _ => .leaf .epsilon) k)

example : (Term.fold sourceAlgebra (fun _ p => p)
    (alternatives.bind identityTransport)).parse [] = .yes (.inr ⟨rfl⟩) := by
  calc
    _ = (Term.fold sourceAlgebra (fun _ p => p) alternatives).parse [] :=
      contextual_transport_refl alternatives [] (by decide)
    _ = _ := rfl

-- Reuse #267's actual compiled ambiguous parser and observation contract.
open Examples.ObservationExtension.Parsing

example : left.parse [] = .yes (.inl ⟨rfl⟩) := rfl
example : right.parse [] = .yes (.inr ⟨rfl⟩) := rfl
example : left.parse [] ≠ right.parse [] := selected_different
example (w : List Char) : (left.parse w).test = (right.parse w).test :=
  old_agreement left right w (Set.mem_univ w)
example : ¬ SquareKit.ObservationExtension.Compatible recognition selected :=
  selected_incompatible
end ExactParserRewrites
