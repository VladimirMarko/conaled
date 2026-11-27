import SquareKit.Internal.Cubical.CartesianHomotopyLevelTransport
import SquareKit.Internal.Cubical.CartesianNativeStructureUaComparison

/-! Sethood of whole structure paths retains carrier witnesses and preservation fields. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.StructureIdentity.Coherence
open CategoryTheory SquareKit.StructureIdentity
open Native StructuredIdentity StructuredIdentity.UaComparison SmallUniverse
universe u
variable {Γ : Context.{u+1}}

/-- Complete structured equivalences into a native set form a native set. -/
noncomputable def equivalencesIsSet (D : Description.{u}) {A B : Family Γ}
    (s : Term (family D A)) (t : Term (family D B))
    (sB : Term (HomotopyLevels.isSet B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    Term (HomotopyLevels.isSet (Native.equivalences D s t)) :=
  let P := equivalenceFieldsFilling D s t FA hFA FB hFB
  HomotopyLevels.sigmaIsSet (HomotopyLevels.equivIsSet sB FA hFA FB hFB)
    (equivalenceFieldsIsProp D s t sB FA hFA FB hFB)
    (EquivalenceFamilies.equivFilling FA hFA FB hFB)
    (EquivalenceFamilies.equivFilling_lawful FA hFA FB hFB) P.1 P.2

variable (D : Description.{u}) (a b : Γ ⟶ smallFamilyCodes.{u})
  (s : Term (family D (liftedDecode a))) (t : Term (family D (liftedDecode b)))
  (sB : Term (HomotopyLevels.isSet (liftedDecode b)))

/-- The selected total correspondence transports sethood to the whole path family. -/
noncomputable def wholePathsIsSet :
    Term (HomotopyLevels.isSet
      (homogeneousPath (objects D Γ) (objectOf D a s) (objectOf D b t))) := by
  let FA := NativeDecode.filling a
  let FB := NativeDecode.filling b
  have hFA := NativeDecode.filling_lawful a
  have hFB := NativeDecode.filling_lawful b
  let E := equivalencesFilling D s t FA hFA FB hFB
  let O := objectsFilling D Γ
  let P := pathFilling (O.1.reindex (projection (interval Γ))) (O.2.reindex _)
    (objectOf D a s) (objectOf D b t)
  have hP := pathFilling_lawful (O.1.reindex (projection (interval Γ))) (O.2.reindex _)
    (objectOf D a s) (objectOf D b t)
  exact HomotopyLevels.targetIsSet (explicitMap D a s b t) (explicitEquivalence D a s b t)
    (equivalencesIsSet D s t sB FA hFA FB hFB) E.1 E.2 P hP

/-- Compare two already supplied parallel 2-paths, keeping their exact endpoints. -/
noncomputable def wholeThreePath
    (p q : Term (homogeneousPath (objects D Γ) (objectOf D a s) (objectOf D b t)))
    (H K : Term (homogeneousPath
      (homogeneousPath (objects D Γ) (objectOf D a s) (objectOf D b t)) p q)) :
    Term (homogeneousPath
      (homogeneousPath (homogeneousPath (objects D Γ) (objectOf D a s) (objectOf D b t)) p q) H K) :=
  HomotopyLevels.path (HomotopyLevels.pathIsPropAt (wholePathsIsSet D a b s t sB) p q) H K

end SquareKit.Cubical.Cartesian.StructureIdentity.Coherence
