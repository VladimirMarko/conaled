import Examples.IndexedCompositional
import Examples.ObservationExtension
import Applications.Languages.WitnessTrie

namespace ConstructionObservationAuthorA
open SquareKit.IndexedCompositional
open IndexedCompositionalExamples.Vectors

-- This composes existing constructors; it adds no primitive signature operation.
def frame {X : Nat → Type} {n} (a b : Nat) (t : Term signature X n) :
    Term signature X (n+2) := cons a (double (cons b t))

theorem leaf_direct {n} (v : Vec n) (k : Fin n) :
    read (rule.lift native) (.leaf v) k = v k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    refine Fin.cases rfl (fun j => ?_) k
    exact ih (fun l => v l.succ) j

theorem double_direct {n} (t : Term signature Vec n) (k : Fin n) :
    read (rule.lift native) (double t) k = 2 * read (rule.lift native) t k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · change read (rule.lift native) (double ((rule.lift native (n+1) t).2 ())) j =
        2 * read (rule.lift native) ((rule.lift native (n+1) t).2 ()) j
      exact ih _ j

theorem frame_direct {n} (a b : Nat) (v : Vec n) (k : Fin (n+2)) :
    read (rule.lift native) (frame a b (.leaf v)) k =
      Fin.cases a (Fin.cases (2*b) (fun j => 2*v j)) k := by
  refine Fin.cases rfl (fun j => ?_) k
  change read (rule.lift native) (double (cons b (.leaf v))) j = _
  rw [double_direct]
  refine Fin.cases rfl (fun l => ?_) j
  change 2 * read (rule.lift native) (.leaf v) l = 2 * v l
  rw [leaf_direct]

theorem frame_direct_expanded {n} (a b : Nat) (v : Vec n) (k : Fin (n+2)) :
    read (rule.lift emptyCoalgebra) (Term.bind expand (frame a b (.leaf v))) k =
      Fin.cases a (Fin.cases (2*b) (fun j => 2*v j)) k := by
  rw [substituted]
  exact frame_direct a b v k

theorem frame_shared {n} (a b : Nat) (v : Vec n) (k : Fin (n+2)) :
    read (rule.lift native) (frame a b (.leaf v)) k =
      Fin.cases a (Fin.cases (2*b) (fun j => 2*v j)) k := by
  rw [correct]
  refine Fin.cases rfl (fun j => ?_) k
  refine Fin.cases rfl (fun l => ?_) j
  rfl

theorem frame_shared_expanded {n} (a b : Nat) (v : Vec n) (k : Fin (n+2)) :
    read (rule.lift emptyCoalgebra) (Term.bind expand (frame a b (.leaf v))) k =
      Fin.cases a (Fin.cases (2*b) (fun j => 2*v j)) k := by
  rw [substituted]
  exact frame_shared a b v k

def emptyVector : Vec 0 := Fin.elim0
def singletonVector : Vec 1 := fun _ => 13

theorem empty_direct (k : Fin 2) :
    read (rule.lift native) (frame 7 11 (.leaf emptyVector)) k =
      Fin.cases 7 (fun _ => 22) k := by
  rw [frame_direct]
  refine Fin.cases rfl (fun j => ?_) k
  refine Fin.cases rfl (fun l => Fin.elim0 l) j

theorem empty_shared (k : Fin 2) :
    read (rule.lift native) (frame 7 11 (.leaf emptyVector)) k =
      Fin.cases 7 (fun _ => 22) k := by
  rw [frame_shared]
  refine Fin.cases rfl (fun j => ?_) k
  refine Fin.cases rfl (fun l => Fin.elim0 l) j

theorem nonempty_direct :
    List.ofFn (read (rule.lift native) (frame 7 11 (.leaf singletonVector))) =
      [7,22,26] := by
  have h := funext (frame_direct 7 11 singletonVector)
  rw [h]
  rfl

theorem nonempty_shared :
    List.ofFn (read (rule.lift native) (frame 7 11 (.leaf singletonVector))) =
      [7,22,26] := by
  have h := funext (frame_shared 7 11 singletonVector)
  rw [h]
  rfl

theorem established_client :
    read (rule.lift native) (double (cons 7 (cons 11 nil))) 1 = 22 := by
  rw [correct]
  rfl

namespace Parsing
open LanguageWitnesses SquareKit.ObservationExtension

variable {P : Language Char}

def exactAgreement (P : Language Char) : Setoid (Parser P) where
  r p q := ∀ w, p.parse w = q.parse w
  iseqv := ⟨fun _ _ => rfl, fun h w => (h w).symm,
    fun h k w => (h w).trans (k w)⟩

def pairObservation (p : Parser P) : Decision (P []) × Decision (P ['a']) :=
  (p.parse [], p.parse ['a'])

theorem compatible_direct : Compatible (exactAgreement P) pairObservation := by
  intro p q h
  exact Prod.ext (h []) (h ['a'])

theorem extend_direct (p q : Parser P) :
    (extend (exactAgreement P) pairObservation).r p q ↔ (exactAgreement P).r p q := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, Prod.ext (h []) (h ['a'])⟩

def descend_direct : Quotient (exactAgreement P) → Decision (P []) × Decision (P ['a']) :=
  Quotient.lift pairObservation (fun _ _ h => Prod.ext (h []) (h ['a']))

theorem descend_direct_mk (p : Parser P) :
    descend_direct (Quotient.mk (exactAgreement P) p) = pairObservation p := rfl

theorem recovery_direct {p q : Parser P}
    (h : (extend (exactAgreement P) pairObservation).r p q) (w : List Char) :
    p.parse w = q.parse w := h.1 w

abbrev Operand : Language Char := fun w => epsilon w ⊕ atom 'a' w
abbrev StarLanguage : Language Char := Star Operand

def starParser : Parser StarLanguage := .star (.union .epsilon (.atom 'a'))

def emptyWitness : StarLanguage [] := ⟨[], rfl⟩
def aWitness : StarLanguage ['a'] := ⟨[⟨['a'], Sum.inr ⟨rfl⟩⟩], rfl⟩

theorem star_empty : (pairObservation starParser).1 = Decision.yes emptyWitness := rfl

theorem star_a : (pairObservation starParser).2 = Decision.yes aWitness := rfl

theorem star_empty_list : emptyWitness.val = [] := rfl

theorem star_a_lookup : (pairObservation starParser).2 =
    (WitnessTrie.unfold starParser 1).lookup ['a'] (by decide) :=
  (WitnessTrie.lookup_unfold starParser 1 ['a'] (by decide)).symm

theorem star_direct_quotient :
    descend_direct (Quotient.mk (exactAgreement StarLanguage) starParser) =
      (Decision.yes emptyWitness, Decision.yes aWitness) := by
  rw [descend_direct_mk]
  exact Prod.ext star_empty star_a

theorem ambiguous_pair_different :
    pairObservation Examples.ObservationExtension.Parsing.left ≠
      pairObservation Examples.ObservationExtension.Parsing.right := by
  intro h
  exact Examples.ObservationExtension.Parsing.selected_different (congrArg Prod.fst h)

theorem recognition_pair_incompatible :
    ¬ Compatible Examples.ObservationExtension.Parsing.recognition pairObservation := by
  intro h
  exact ambiguous_pair_different
    (h (Examples.ObservationExtension.Parsing.old_agreement _ _))

end Parsing
end ConstructionObservationAuthorA
