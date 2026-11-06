import SquareKit.Internal.Cubical.IdentityComposition

/-! Marked identity inherits uniform filling from the underlying family.
Its selected constancy face is retained on the whole original tube. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

noncomputable def identityComposition {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) (a b : Term A) : Composition (identity A a b) :=
  IdentityComposition.composition
    (pathFilling (F.reindex (projection (interval Γ))) (hF.reindex (projection (interval Γ))) a b).toComposition
    (Filling.toComposition_lawful (pathFilling_lawful (F.reindex (projection (interval Γ))) (hF.reindex (projection (interval Γ))) a b))

theorem identityComposition_lawful {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) (a b : Term A) : (identityComposition F hF a b).Lawful :=
  IdentityComposition.composition_lawful _ _

noncomputable def identityFilling {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) (a b : Term A) : Filling (identity A a b) :=
  (identityComposition F hF a b).toFilling

theorem identityFilling_lawful {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) (a b : Term A) : (identityFilling F hF a b).Lawful :=
  Composition.toFilling_lawful (identityComposition_lawful F hF a b)

end SquareKit.Cubical.Presheaf
