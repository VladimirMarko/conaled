import SquareKit.DependentAdministrativeMaps
import SquareKit.DependentAdministrativeInclusions
import SquareKit.DependentPairTheoryMap

/-! The actual pair translations use the general composable certificate layer. -/
namespace SquareKit.DependentPairJudgments.Administrative
open DependentTheoryMaps DependentPairPresentations TypedSubstitution

def pairF := inclusion projectionInclusion

def pairG := lift G fullG

/-- Composition substitutes the entire G certificate into every F instruction.
It uses the generic operation available for two arbitrary administrative maps. -/
def pairFG := pairF.comp pairG

theorem pair_composition {H : Judgment projectionSignature → Type}
    {K : Judgment projectionSignature → Type} {L : Judgment eliminationSignature → Type}
    (h : ∀ j, H j → K j) (k : ∀ j, K j → L (Judgment.map G j))
    {j : Judgment projectionSignature} (d : Proof (projectionPresentation false) H j) :
    pairFG.transport (fun j p => k j (h j p)) d =
      pairG.transport k (pairF.transport h d) :=
  DependentBranchTheoryMaps.TheoryMap.comp_transport pairF pairG h k d

/-- The new composite erases to the retained compiler, with exactly the same
ordinary derivation tree rather than merely the same conclusion. -/
theorem pair_erases {j : Judgment projectionSignature}
    (d : Derivation (projectionPresentation false) (fun _ => Empty) j) :
    erase (fullEliminationLocal _) (fun _ h => Empty.elim h)
      (pairFG.transport (fun _ h => Empty.elim h) (embed d)) = compile d := by
  have empty_comp : (fun (_ : Judgment projectionSignature) (h : Empty) =>
      (Empty.elim (Empty.elim h) : Empty)) =
      (fun (_ : Judgment projectionSignature) (h : Empty) => (Empty.elim h : Empty)) := by
    funext j h
    exact Empty.elim h
  have hc := pair_composition (H := fun _ => Empty) (K := fun _ => Empty)
    (L := fun _ => Empty) (fun _ h => Empty.elim h) (fun _ h => Empty.elim h) (embed d)
  simp only [empty_comp] at hc
  rw [hc]
  unfold pairF pairG
  rw [inclusion_transport_embed, erase_lift]
  rfl

end SquareKit.DependentPairJudgments.Administrative
