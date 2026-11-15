import SquareKit.Internal.Cubical.NormalizedIdentityFilling
import SquareKit.Internal.Cubical.ComprehensionTransport
import SquareKit.Internal.Cubical.ContextIsoSections
import SquareKit.Internal.Cubical.IdentityElimination

/-! The strict marked-identity eliminator survives the normalized presentation.
Its motive and selected composition operation are pulled along the context
isomorphism, and the resulting section is transported back. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace NormalizedIdentitySingleton
variable {Γ : Context.{u}} (A : Family Γ) (a : Term A)

abbrev fiber : Family (total A) :=
  normalizedIdentity (reindex A (projection A)) (a.reindex (projection A)) (generic A)
abbrev context : Context := total (fiber A a)
abbrev presentation : IdentitySingleton.context A a ≅ context A a :=
  totalIso (normalizedIdentityIso (reindex A (projection A)) (a.reindex (projection A)) (generic A))
abbrev reflexivity : Γ ⟶ context A a := IdentitySingleton.reflexivity A a ≫ (presentation A a).hom

end NormalizedIdentitySingleton

namespace NormalizedIdentityElimination
variable {Γ : Context.{u}} (A : Family Γ) (a : Term A)
  (C : Family (NormalizedIdentitySingleton.context A a))
  (d : Term (reindex C (NormalizedIdentitySingleton.reflexivity A a)))

noncomputable def eliminate (G : Composition C) : Term C :=
  (IdentityElimination.eliminate A a
    (reindex C (NormalizedIdentitySingleton.presentation A a).hom) d
    (G.reindex (NormalizedIdentitySingleton.presentation A a).hom)).descendIso
      (NormalizedIdentitySingleton.presentation A a)

theorem eliminate_beta (G : Composition C) (hG : G.Lawful) :
    (eliminate A a C d G).reindex (NormalizedIdentitySingleton.reflexivity A a) = d := by
  have h := Term.descendIso_reindex (NormalizedIdentitySingleton.presentation A a)
    (IdentityElimination.eliminate A a
      (reindex C (NormalizedIdentitySingleton.presentation A a).hom) d
      (G.reindex (NormalizedIdentitySingleton.presentation A a).hom))
  exact (congrArg (fun t => t.reindex (IdentitySingleton.reflexivity A a)) h).trans
    (IdentityElimination.eliminate_beta A a _ d _
      (hG.reindex (NormalizedIdentitySingleton.presentation A a).hom))

end NormalizedIdentityElimination
end SquareKit.Cubical.Presheaf
