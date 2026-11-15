import Applications.Languages.DerivativeNormalization
import Examples.ExactParserRewrites

/-! Native derivative states, exact witness recovery and bounded logical costs. -/
namespace DerivativeNormalizationExamples
open LanguageWitnesses LanguageWitnesses.DerivativeNormalization

-- This is a derivative result, not a separate toy automaton.
def redundant : Parser (α := Bool) (fun _ => PUnit) :=
  (identityChain 8 (.universal : Parser (α := Bool) (fun _ => PUnit))).derive true

def adverse : Parser (α := Bool) (fun _ => PUnit) :=
  (Parser.universal : Parser (α := Bool) (fun _ => PUnit)).derive true

def workload : List Bool := List.replicate 20 true

-- Expected arithmetic: 20 * 9 versus (9 visits + 8 compositions + 1 wrapper) + 20 * 2.
example : runWork redundant workload = 180 := by decide
example : normalizationWork redundant + runWork (normalize redundant) workload = 58 := by decide
example : nodes redundant = 9 ∧ nodes (normalize redundant) = 2 := by decide
example : normalizationWork redundant + runWork (normalize redundant) workload <
    runWork redundant workload := by decide

-- The unchanged baseline has no redundant wrapper. The chosen uniform normal form adds one.
example : runWork adverse workload = 20 := by decide
example : normalizationWork adverse + runWork (normalize adverse) workload = 42 := by decide
example : nodes adverse = 1 ∧ nodes (normalize adverse) = 2 := by decide
example : runWork adverse workload <
    normalizationWork adverse + runWork (normalize adverse) workload := by decide

-- A short workload does not amortize normalization, even with eight wrappers.
example : runWork redundant [true] = 9 := by decide
example : normalizationWork redundant + runWork (normalize redundant) [true] = 20 := by decide

example (w : List Bool) : (normalize redundant).parse w = redundant.parse w :=
  normalize_exact _ _
example : outerDepth (normalize redundant) = 1 := normalized_depth _

-- Nonidentity maps and selected scalar evidence: composition must not drop or reorder them.
def selected : Parser (α := Unit) (fun _ => PUnit × Bool) :=
  (Parser.transport (fun _ => ExactParserRewrites.exchange)
    (.transport (fun _ => ExactParserRewrites.toggle)
      (.scale (.yes true) .universal))).derive ()

example : (normalize selected).parse [()] = .yes (⟨⟩, false) := by
  rw [normalize_exact]
  rfl

-- The public context theorem covers the prior star/concat/depth-restriction context.
example :
    (SquareKit.IndexedCompositional.Term.fold IndexedCompositional.sourceAlgebra (fun _ p => p)
      ((ExactParserRewrites.surrounding.bind IndexedCompositional.TransportPair.expanded).bind
        (fun _ p => .leaf (normalize p)))).parse [()] =
    (SquareKit.IndexedCompositional.Term.fold IndexedCompositional.sourceAlgebra (fun _ p => p)
      (ExactParserRewrites.surrounding.bind IndexedCompositional.TransportPair.expanded)).parse [()] :=
  contextual _ _ (by decide)

-- A Boolean-valid merge still fails even after this certified normalization.
open Examples.ObservationExtension.Parsing
example : (normalize left).parse [] ≠ (normalize right).parse [] := by
  rw [normalize_exact, normalize_exact]
  exact selected_different
example (w : List Char) : (left.parse w).test = (right.parse w).test :=
  old_agreement left right w (Set.mem_univ w)

end DerivativeNormalizationExamples
