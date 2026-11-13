import SquareKit.Internal.Cubical.NativeUnivalenceInverse
import SquareKit.Internal.Cubical.NativeUnivalenceTotals
import SquareKit.Internal.Cubical.NativeUnivalenceMapNaturality
import SquareKit.Internal.Cubical.EquivalenceIsoTransport
import SquareKit.Internal.Cubical.ChosenInverseHomotopies

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Γ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})

noncomputable def equivalenceTotal : HomotopyContractible (sigma (family Γ) (basedEquivalences a)) :=
  equivalenceTotalOfHomotopy a (rightInverseHomotopy (movingSource a) (movingTarget (Γ := Γ)))

noncomputable def movingUnivalence :
    HomotopyEquivalence (pathToEquiv (movingSource a) (movingTarget (Γ := Γ))) :=
  univalenceOfHomotopy a (rightInverseHomotopy (movingSource a) (movingTarget (Γ := Γ)))

/-- Native univalence for the actual universal-El path-to-equivalence map. -/
noncomputable def univalence : HomotopyEquivalence (pathToEquiv a b) := by
  let τ := pair (A := family Γ) (𝟙 Γ) (term b)
  let Jp := pathReindexIso
    (reindex (family (total (family Γ))) (projection (interval (total (family Γ)))))
    (term (movingSource a)) (term (movingTarget (Γ := Γ))) τ
  let Je := EquivalenceFamilies.equivReindexIso
    (liftedDecode (movingSource a)) (liftedDecode (movingTarget (Γ := Γ))) τ
  have E := ((movingUnivalence a).reindex τ).conjugateIso Jp.symm Je
  -- The naturality law identifies the transported map itself, not only its observations.
  exact (pathToEquiv_conjugate_reindex (movingSource a) (movingTarget (Γ := Γ)) τ) ▸ E

noncomputable def pathsFilling : Filling (paths a b) :=
  pathFilling (filling (total (interval Γ))) (filling_lawful _)
    (term a) (term b)

theorem pathsFilling_lawful : (pathsFilling a b).Lawful :=
  pathFilling_lawful (filling (total (interval Γ))) (filling_lawful _)
    (term a) (term b)

/-- The same constructed ua map is also a left inverse, through a native path. -/
noncomputable def leftInverseHomotopy :=
  (univalence a b).chosenLeftInverse (pathsFilling a b) (pathsFilling_lawful a b)
    (equivToPath a b) (rightInverseHomotopy a b)

/-- Pointwise form of the left inverse, for an arbitrary native universe path. -/
noncomputable def leftInverseAt (p : Term (paths a b)) :
    Term (homogeneousPath (paths a b)
      (Term.map (equivToPath a b) (Term.map (pathToEquiv a b) p)) p) :=
  homogeneousReindex (leftInverseHomotopy a b) (pair (A := paths a b) (𝟙 Γ) p)

end SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
