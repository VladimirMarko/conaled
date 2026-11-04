import Examples.ObservationExtension
import Applications.Languages.WitnessTrie
import Examples.IndexedCompositional

namespace ConstructionObservationAuthorB
namespace Parsing
open LanguageWitnesses SquareKit.ObservationExtension

def old (P : Language Char) : Setoid (Parser P) :=
  agreement (fun w p => p.parse w) Set.univ

def pairObservation {P : Language Char} (p : Parser P) :
    Decision (P []) × Decision (P ['a']) := (p.parse [], p.parse ['a'])

namespace Shared
 theorem compatible (P : Language Char) : Compatible (old P) pairObservation :=
  compatible_of_factor (old P) (fun p w => p.parse w)
    (fun {_ _} h => funext (fun w => h w (Set.mem_univ w)))
    pairObservation (fun f => (f [], f ['a'])) (fun _ => rfl)
 theorem equivalence (P : Language Char) (p q : Parser P) :
    (extend (old P) pairObservation).r p q ↔ (old P).r p q :=
  extend_iff _ _ (compatible P) p q
 def onQuotient (P : Language Char) : Quotient (old P) →
     Decision (P []) × Decision (P ['a']) := descend _ _ (compatible P)
 theorem representative (P : Language Char) (p : Parser P) :
     onQuotient P (Quotient.mk (old P) p) = pairObservation p :=
  descend_mk _ _ (compatible P) p
end Shared
end Parsing
end ConstructionObservationAuthorB
