import SquareKit.Internal.Cubical.NativeUnivalenceElimination
import SquareKit.Internal.Cubical.NativeUnivalenceMapLaws
import SquareKit.Internal.Cubical.EquivalencePaths

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Γ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})
  (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)

/-- Pointwise native comparison at the generic source element. -/
noncomputable def uaMapHomotopy : Term (homogeneousPath
    (reindex (liftedDecode b) (projection (liftedDecode a)))
    (Term.map (Functor.whiskerLeft (projection (liftedDecode a)).mapElements f)
      (generic (liftedDecode a)))
    (Term.map (Functor.whiskerLeft (projection (liftedDecode a)).mapElements
      (pathToMap (ua a b f E))) (generic (liftedDecode a)))) := by
  let σ := projection (liftedDecode a)
  let q := uaComparison (σ ≫ a) (σ ≫ b)
    (Functor.whiskerLeft σ.mapElements f) (E.reindex σ) (generic (liftedDecode a))
  have hm := (pathToMap_reindex (ua a b f E) σ).trans
    (congrArg pathToMap (ua_reindex a b f E σ))
  exact pathLam (pathApp q) (pathApp_zero q)
    ((pathApp_one q).trans (congrArg (fun k => Term.map k (generic (liftedDecode a))) hm.symm))

/-- The native comparison retains both complete chosen endpoint equivalences. -/
noncomputable def uaEquivalenceComparison : Term (homogeneousPath (equivalences a b)
    ((EquivalenceFamilies.equivSections (liftedDecode a) (liftedDecode b)) ⟨f,E⟩)
    ((EquivalenceFamilies.equivSections (liftedDecode a) (liftedDecode b))
      ⟨pathToMap (ua a b f E),pathToEquivalence (ua a b f E)⟩)) :=
  EquivalencePaths.ofHomotopy f (pathToMap (ua a b f E)) (uaMapHomotopy a b f E)
    (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling b) (NativeDecode.filling_lawful b)
    E (pathToEquivalence (ua a b f E))

end SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
