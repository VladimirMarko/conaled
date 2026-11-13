import SquareKit.Internal.Cubical.UniversePathEquivalence
import SquareKit.Internal.Cubical.EquivalenceFamilies

/-! The native map from universe paths to internal equivalences. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Γ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})

abbrev paths := homogeneousPath (family Γ) (term a) (term b)
abbrev equivalences := EquivalenceFamilies.equiv (liftedDecode a) (liftedDecode b)

def genericPath : Term (homogeneousPath (family (total (paths a b)))
    (term (projection (paths a b) ≫ a)) (term (projection (paths a b) ≫ b))) :=
  Term.map (pathReindex (reindex (family Γ) (projection (interval Γ)))
    (term a) (term b) (projection (paths a b))) (generic (paths a b))

noncomputable def pathEquivalenceSection :
    Term (reindex (equivalences a b) (projection (paths a b))) :=
  EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b)
    (projection (paths a b))
    ⟨pathToMap (genericPath a b),pathToEquivalence (genericPath a b)⟩

/-- The target is the internal equivalence family, retaining the chosen native
fiber contractions as well as the transported function. -/
noncomputable def pathToEquiv : paths a b ⟶ equivalences a b :=
  EquivalenceFamilies.decodeMap (lam (pathEquivalenceSection a b))

end SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
