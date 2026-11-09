import FirstRowReflectionSource
import CheckerClient

/-!
Experimental first-row comparison from the preserved preview. See
`docs/research/cqueens-preview-disposition.md`. The cases test the odd center,
empty sum and legal-column boundary of the newly selected generic law. The
source comparison reuses the existing endpoint-to-square adapter and consumer.
-/
set_option autoImplicit false

namespace CertifiedNatCheckerPreview.Reflection

open ADWH.Experiments.Chapter15.FirstRowReflection
open ADWH.Experiments.Chapter15.CertifiedNatChecker

/-- The optimized source realizes the same fixed-Word16 function. -/
def endpoint : Endpoint ADWH.Chapter15.Queens.BitRepresentation.cqueens where
  name := "ADWH.Chapter15.Queens.BitRepresentation.cqueens"
  run := SourceBridge.cqueens
  correct := SourceBridge.cqueens_eq

def thenSuccessor : Squares.Square natRep natRep :=
  Squares.compose successorSquare (endpointSquare endpoint)

theorem source_comparison (n : Nat) :
    thenSuccessor.impl n =
      ADWH.Chapter15.Queens.BitRepresentation.cqueens n + 1 :=
  thenSuccessor.commutes n

/-- Five positions of weight three have total fifteen. Pairing counts the
middle weight once; it must not double the center along with the two pairs. -/
theorem odd_constant_weight :
    pairedSum 5 (fun _ => 3) = 15 := by
  have h := paired_sum 5 (fun _ => 3) (fun _ _ => rfl)
  exact h.symm.trans (by decide)

theorem even_constant_weight :
    pairedSum 4 (fun _ => 3) = 12 := by
  have h := paired_sum 4 (fun _ => 3) (fun _ _ => rfl)
  exact h.symm.trans (by decide)

theorem empty_weight_sum : pairedSum 0 (fun _ => 3) = 0 := by
  have h := paired_sum 0 (fun _ => 3) (fun _ _ => rfl)
  exact h.symm.trans (by decide)

/-- The column hypothesis is necessary: truncated subtraction is not a
reflection involution on all naturals. No strengthened false law is assumed. -/
theorem outside_column_not_involutive : reflectColumn 5 (reflectColumn 5 7) ≠ 7 := by
  decide

end CertifiedNatCheckerPreview.Reflection
