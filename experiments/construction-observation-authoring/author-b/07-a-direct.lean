import Examples.ObservationExtension
import Applications.Languages.WitnessTrie
import Examples.IndexedCompositional

namespace ConstructionObservationAuthorB
namespace Parsing
open LanguageWitnesses SquareKit.ObservationExtension

def old (P : LanguageWitnesses.Language Char) : Setoid (Parser P) :=
  agreement (fun w p => p.parse w) Set.univ

def pairObservation {P : LanguageWitnesses.Language Char} (p : Parser P) :
    Decision (P []) × Decision (P ['a']) := (p.parse [], p.parse ['a'])

namespace Shared
 theorem compatible (P : LanguageWitnesses.Language Char) : Compatible (old P) pairObservation :=
  compatible_of_factor (old P) (fun p w => p.parse w)
    (fun {_ _} h => funext (fun w => h w (Set.mem_univ w)))
    pairObservation (fun f => (f [], f ['a'])) (fun _ => rfl)
 theorem equivalence (P : LanguageWitnesses.Language Char) (p q : Parser P) :
    (extend (old P) pairObservation).r p q ↔ (old P).r p q :=
  extend_iff _ _ (compatible P) p q
 def onQuotient (P : LanguageWitnesses.Language Char) : Quotient (old P) →
     Decision (P []) × Decision (P ['a']) := descend _ _ (compatible P)
 theorem representative (P : LanguageWitnesses.Language Char) (p : Parser P) :
     onQuotient P (Quotient.mk (old P) p) = pairObservation p :=
  descend_mk _ _ (compatible P) p
end Shared

abbrev NullableOperand : LanguageWitnesses.Language Char :=
  fun w => epsilon w ⊕ atom 'a' w
abbrev NullableStar := Star NullableOperand
def nullableStar : Parser NullableStar := .star (.union .epsilon (.atom 'a'))

theorem empty_decision : (pairObservation nullableStar).1 = .yes ⟨[], rfl⟩ := rfl

def oneWitness : NullableStar ['a'] := ⟨[⟨['a'], Sum.inr (Evidence.mk rfl)⟩], rfl⟩
theorem nonempty_decision : (pairObservation nullableStar).2 = .yes oneWitness := rfl

theorem nonempty_lookup :
    (WitnessTrie.unfold nullableStar 1).lookup ['a'] (by decide) =
      (pairObservation nullableStar).2 := WitnessTrie.lookup_unfold _ _ _ _

theorem shared_instance : Shared.onQuotient NullableStar
    (Quotient.mk (old NullableStar) nullableStar) =
      (Decision.yes ⟨[], rfl⟩, Decision.yes oneWitness) :=
  (Shared.representative _ _).trans rfl

open Examples.ObservationExtension.Parsing in
 theorem first_components_differ :
    (pairObservation left).1 ≠ (pairObservation right).1 := selected_different

open Examples.ObservationExtension.Parsing in
 theorem recognition_incompatible : ¬ Compatible recognition pairObservation := by
  intro h
  exact first_components_differ (congrArg Prod.fst (h (old_agreement left right)))

namespace Direct
 theorem compatible (P : LanguageWitnesses.Language Char) : Compatible (old P) pairObservation := by
  intro p q h
  exact Prod.ext (h [] (Set.mem_univ [])) (h ['a'] (Set.mem_univ ['a']))
 theorem equivalence (P : LanguageWitnesses.Language Char) (p q : Parser P) :
    (extend (old P) pairObservation).r p q ↔ (old P).r p q :=
  ⟨fun h => h.1, fun h => ⟨h, compatible P h⟩⟩
 def onQuotient (P : LanguageWitnesses.Language Char) : Quotient (old P) →
     Decision (P []) × Decision (P ['a']) :=
   Quotient.lift pairObservation (fun _ _ h => compatible P h)
 theorem representative (P : LanguageWitnesses.Language Char) (p : Parser P) :
     onQuotient P (Quotient.mk (old P) p) = pairObservation p := rfl
 theorem instance_decisions : onQuotient NullableStar
    (Quotient.mk (old NullableStar) nullableStar) =
      (Decision.yes ⟨[], rfl⟩, Decision.yes oneWitness) :=
   (representative _ _).trans rfl
end Direct
end Parsing
namespace Vectors
open IndexedCompositionalExamples.Vectors SquareKit.IndexedCompositional

/-- A compound client of the existing signature, adding no primitive. -/
def frame {X : Nat → Type} {n} (a b : Nat) (t : Term signature X n) :
    Term signature X (n+2) := cons a (double (cons b t))

def expected {n} (a b : Nat) (v : Vec n) : Vec (n+2) :=
  Fin.cases a (Fin.cases (2*b) (fun k => 2*v k))

namespace Shared
 theorem coordinates {n} (a b : Nat) (v : Vec n) (k : Fin (n+2)) :
    read (rule.lift native) (frame a b (.leaf v)) k = expected a b v k := by
  rw [correct]
  refine Fin.cases ?_ (fun j => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun l => ?_) j <;> rfl
 theorem expanded {n} (a b : Nat) (v : Vec n) (k : Fin (n+2)) :
    read (rule.lift emptyCoalgebra) (Term.bind expand (frame a b (.leaf v))) k =
      expected a b v k :=
  (substituted _ _).trans (coordinates a b v k)
 theorem empty_tail (a b : Nat) (k : Fin 2) :
    read (rule.lift native) (frame a b (.leaf (fun i : Fin 0 => Fin.elim0 i))) k =
      Fin.cases a (fun _ => 2*b) k := by
  rw [coordinates]
  refine Fin.cases rfl (fun j => ?_) k
  refine Fin.cases rfl (fun i => Fin.elim0 i) j
 theorem sample (k : Fin 3) :
    read (rule.lift native) (frame 7 11 (.leaf (fun _ : Fin 1 => 13))) k =
      Fin.cases 7 (Fin.cases 22 (fun _ => 26)) k := by
  rw [coordinates]
  refine Fin.cases rfl (fun j => ?_) k
  refine Fin.cases rfl (fun _ => rfl) j
 theorem sample_expanded (k : Fin 3) :
    read (rule.lift emptyCoalgebra)
      (Term.bind expand (frame 7 11 (.leaf (fun _ : Fin 1 => 13)))) k =
      Fin.cases 7 (Fin.cases 22 (fun _ => 26)) k := by
  rw [substituted]
  exact sample k
end Shared

theorem established_client :
    read (rule.lift native) (double (cons 7 (cons 11 nil))) 1 = 22 := by
  rw [correct]
  rfl

namespace Direct
 theorem leaf_coordinate {n} (v : Vec n) (k : Fin n) :
    read (rule.lift native) (.leaf v) k = v k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    refine Fin.cases rfl (fun j => ?_) k
    exact ih (fun l => v l.succ) j

 theorem cons_coordinate {n} (a : Nat) (t : Term signature Vec n) (k : Fin (n+1)) :
    read (rule.lift native) (cons a t) k =
      Fin.cases a (read (rule.lift native) t) k := by
  refine Fin.cases rfl (fun _ => rfl) k

 theorem double_coordinate {n} (t : Term signature Vec n) (k : Fin n) :
    read (rule.lift native) (double t) k = 2 * read (rule.lift native) t k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    refine Fin.cases rfl (fun j => ?_) k
    change read (rule.lift native) (double ((rule.lift native _ t).2 ())) j =
      2 * read (rule.lift native) ((rule.lift native _ t).2 ()) j
    exact ih _ j

 theorem coordinates {n} (a b : Nat) (v : Vec n) (k : Fin (n+2)) :
    read (rule.lift native) (frame a b (.leaf v)) k = expected a b v k := by
  unfold frame
  rw [cons_coordinate]
  refine Fin.cases rfl (fun j => ?_) k
  change read (rule.lift native) (double (cons b (.leaf v))) j =
    Fin.cases (2*b) (fun l => 2*v l) j
  rw [double_coordinate, cons_coordinate]
  refine Fin.cases rfl (fun l => ?_) j
  change 2 * read (rule.lift native) (.leaf v) l = 2*v l
  rw [leaf_coordinate]

 theorem expanded {n} (a b : Nat) (v : Vec n) (k : Fin (n+2)) :
    read (rule.lift emptyCoalgebra) (Term.bind expand (frame a b (.leaf v))) k =
      expected a b v k :=
  (substituted _ _).trans (coordinates a b v k)
 theorem empty_tail (a b : Nat) (k : Fin 2) :
    read (rule.lift native) (frame a b (.leaf (fun i : Fin 0 => Fin.elim0 i))) k =
      Fin.cases a (fun _ => 2*b) k := by
  rw [coordinates]
  refine Fin.cases rfl (fun j => ?_) k
  refine Fin.cases rfl (fun i => Fin.elim0 i) j
 theorem sample (k : Fin 3) :
    read (rule.lift native) (frame 7 11 (.leaf (fun _ : Fin 1 => 13))) k =
      Fin.cases 7 (Fin.cases 22 (fun _ => 26)) k := by
  rw [coordinates]
  refine Fin.cases rfl (fun j => ?_) k
  refine Fin.cases rfl (fun _ => rfl) j
 theorem sample_expanded (k : Fin 3) :
    read (rule.lift emptyCoalgebra)
      (Term.bind expand (frame 7 11 (.leaf (fun _ : Fin 1 => 13)))) k =
      Fin.cases 7 (Fin.cases 22 (fun _ => 26)) k := by
  rw [substituted]
  exact sample k
end Direct
end Vectors
end ConstructionObservationAuthorB
