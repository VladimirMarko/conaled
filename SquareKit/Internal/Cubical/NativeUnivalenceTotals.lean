import SquareKit.Internal.Cubical.NativeUnivalenceUa
import SquareKit.Internal.Cubical.NativePathSingleton
import SquareKit.Internal.Cubical.FiberwiseHomotopyRetracts

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Γ : Context.{u+1}} (a : Γ ⟶ smallFamilyCodes.{u})

def movingSource : total (family Γ) ⟶ smallFamilyCodes.{u} := projection (family Γ) ≫ a

def movingTarget : total (family Γ) ⟶ smallFamilyCodes.{u} := code (generic (family Γ))

abbrev basedPaths := paths (movingSource a) (movingTarget (Γ := Γ))
abbrev basedEquivalences := equivalences (movingSource a) (movingTarget (Γ := Γ))

noncomputable def basedPathsFilling : Filling (basedPaths a) :=
  pathFilling (filling (total (interval (total (family Γ)))))
    (filling_lawful _) (term (movingSource a)) (term (movingTarget (Γ := Γ)))

theorem basedPathsFilling_lawful : (basedPathsFilling a).Lawful :=
  pathFilling_lawful (filling (total (interval (total (family Γ)))))
    (filling_lawful _) (term (movingSource a)) (term (movingTarget (Γ := Γ)))

noncomputable def basedEquivalencesFilling : Filling (basedEquivalences a) :=
  EquivalenceFamilies.equivFilling (NativeDecode.filling (movingSource a))
    (NativeDecode.filling_lawful _) (NativeDecode.filling (movingTarget (Γ := Γ)))
    (NativeDecode.filling_lawful _)

theorem basedEquivalencesFilling_lawful : (basedEquivalencesFilling a).Lawful :=
  EquivalenceFamilies.equivFilling_lawful (NativeDecode.filling (movingSource a))
    (NativeDecode.filling_lawful _) (NativeDecode.filling (movingTarget (Γ := Γ)))
    (NativeDecode.filling_lawful _)

noncomputable def basedPathTotalContractible : HomotopyContractible (sigma (family Γ) (basedPaths a)) :=
  NativePathSingleton.contractible (term a)

variable (h : Term (homogeneousPath (reindex (basedEquivalences a) (projection (basedEquivalences a)))
  (Term.map (Functor.whiskerLeft (projection (basedEquivalences a)).mapElements
    (pathToEquiv (movingSource a) (movingTarget (Γ := Γ))))
    (Term.map (Functor.whiskerLeft (projection (basedEquivalences a)).mapElements
      (equivToPath (movingSource a) (movingTarget (Γ := Γ)))) (generic (basedEquivalences a))))
  (generic (basedEquivalences a))))

/-- The total contraction uses the supplied native right-inverse homotopy, not an assumed contraction. -/
noncomputable def equivalenceTotalOfHomotopy :
    HomotopyContractible (sigma (family Γ) (basedEquivalences a)) :=
  (basedPathTotalContractible a).fiberwiseRetract (filling Γ) (filling_lawful Γ)
    (basedEquivalencesFilling a) (basedEquivalencesFilling_lawful a)
    (pathToEquiv (movingSource a) (movingTarget (Γ := Γ)))
    (equivToPath (movingSource a) (movingTarget (Γ := Γ))) h

noncomputable def univalenceOfHomotopy :
    HomotopyEquivalence (pathToEquiv (movingSource a) (movingTarget (Γ := Γ))) :=
  HomotopyEquivalence.ofContractibleTotals
    (pathToEquiv (movingSource a) (movingTarget (Γ := Γ)))
    (filling Γ) (filling_lawful Γ)
    (basedPathsFilling a) (basedPathsFilling_lawful a)
    (basedEquivalencesFilling a) (basedEquivalencesFilling_lawful a)
    (basedPathTotalContractible a) (equivalenceTotalOfHomotopy a h)

end SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
