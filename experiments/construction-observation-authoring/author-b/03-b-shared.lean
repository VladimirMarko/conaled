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

end Parsing
end ConstructionObservationAuthorB
