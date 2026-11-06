import SquareKit.Internal.Cubical.IdentityFillingSubstitution
import SquareKit.Internal.Cubical.NormalizedFillingSubstitution
import SquareKit.Internal.Cubical.NormalizedIdentity

/-! The selected normalized Id filler obeys literal family substitution. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem normalizedIdentityIso_reindex {Γ Δ : Context.{u}} (B : Family Γ)
    (a₀ : Term B) (a₁ : Term B) (σ : Δ ⟶ Γ) :
    (Functor.isoWhiskerLeft σ.mapElements (normalizedIdentityIso B a₀ a₁)).trans
      (eqToIso (normalizedIdentity_reindex B a₀ a₁ σ)) =
      (identityReindexIso B a₀ a₁ σ).trans
        (normalizedIdentityIso (reindex B σ) (a₀.reindex σ) (a₁.reindex σ)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro p
  have cast_heq : ∀ {C D : Family Δ} (e : C = D) (v : C.obj x), HEq ((eqToHom e).app x v) v := by
    intro C D e v
    cases e
    rfl
  exact eq_of_heq ((cast_heq (normalizedIdentity_reindex B a₀ a₁ σ) p.toLocal).trans
    (identityToLocal_substitution B a₀ a₁ σ x p))

noncomputable def normalizedIdentityFilling {Γ : Context.{u}} {B : Family Γ}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term B) (a₁ : Term B) :
    Filling (normalizedIdentity B a₀ a₁) :=
  (identityFilling F hF a₀ a₁).transport (normalizedIdentityIso B a₀ a₁)

theorem normalizedIdentityFilling_lawful {Γ : Context.{u}} {B : Family Γ}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term B) (a₁ : Term B) :
    (normalizedIdentityFilling F hF a₀ a₁).Lawful :=
  Filling.transport_lawful _ _ (identityFilling_lawful F hF a₀ a₁)

theorem normalizedIdentityFilling_reindex {Γ Δ : Context.{u}} {B : Family Γ}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term B) (a₁ : Term B) (σ : Δ ⟶ Γ) :
    ((normalizedIdentityFilling F hF a₀ a₁).reindex σ).convert (normalizedIdentity_reindex B a₀ a₁ σ) =
      normalizedIdentityFilling (F.reindex σ) (hF.reindex _) (a₀.reindex σ) (a₁.reindex σ) := by
  let e := normalizedIdentity_reindex B a₀ a₁ σ
  let n := normalizedIdentityIso (reindex B σ) (a₀.reindex σ) (a₁.reindex σ)
  calc
    _ = ((identityFilling F hF a₀ a₁).reindex σ).transport
        ((Functor.isoWhiskerLeft σ.mapElements (normalizedIdentityIso B a₀ a₁)).trans (eqToIso e)) :=
      (Filling.transport_eqToIso e ((normalizedIdentityFilling F hF a₀ a₁).reindex σ)).symm
    _ = ((identityFilling F hF a₀ a₁).reindex σ).transport ((identityReindexIso B a₀ a₁ σ).trans n) :=
      congrArg (fun k => ((identityFilling F hF a₀ a₁).reindex σ).transport k) (normalizedIdentityIso_reindex B a₀ a₁ σ)
    _ = _ := congrArg (fun H => H.transport n) (identityFilling_reindex_iso F hF a₀ a₁ σ)

end SquareKit.Cubical.Presheaf
