import SquareKit.Internal.Cubical.PathFillingSubstitution
import SquareKit.Internal.Cubical.NormalizedFillingSubstitution
import SquareKit.Internal.Cubical.NormalizedPaths

/-! The selected normalized Path filler obeys literal family substitution. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem normalizedPathIso_reindex {Γ Δ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false))) (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) :
    (Functor.isoWhiskerLeft σ.mapElements (normalizedPathIso B a₀ a₁)).trans
      (eqToIso (normalizedPath_reindex B a₀ a₁ σ)) =
      (pathReindexIso B a₀ a₁ σ).trans
        (normalizedPathIso (reindex B (liftSub (interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro p
  have cast_heq : ∀ {C D : Family Δ} (e : C = D) (v : C.obj x), HEq ((eqToHom e).app x v) v := by
    intro C D e v
    cases e
    rfl
  exact eq_of_heq ((cast_heq (normalizedPath_reindex B a₀ a₁ σ) p.toLocal).trans
    (pathToLocal_substitution B a₀ a₁ σ x p))

noncomputable def normalizedPathFilling {Γ : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term (reindex B (endpointSub Γ false))) (a₁ : Term (reindex B (endpointSub Γ true))) :
    Filling (normalizedPath B a₀ a₁) :=
  (pathFilling F hF a₀ a₁).transport (normalizedPathIso B a₀ a₁)

theorem normalizedPathFilling_lawful {Γ : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term (reindex B (endpointSub Γ false))) (a₁ : Term (reindex B (endpointSub Γ true))) :
    (normalizedPathFilling F hF a₀ a₁).Lawful :=
  Filling.transport_lawful _ _ (pathFilling_lawful F hF a₀ a₁)

theorem normalizedPathFilling_reindex {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term (reindex B (endpointSub Γ false))) (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) :
    ((normalizedPathFilling F hF a₀ a₁).reindex σ).convert (normalizedPath_reindex B a₀ a₁ σ) =
      normalizedPathFilling (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _) (a₀.reindex σ) (a₁.reindex σ) := by
  let e := normalizedPath_reindex B a₀ a₁ σ
  let n := normalizedPathIso (reindex B (liftSub (interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ)
  calc
    _ = ((pathFilling F hF a₀ a₁).reindex σ).transport
        ((Functor.isoWhiskerLeft σ.mapElements (normalizedPathIso B a₀ a₁)).trans (eqToIso e)) :=
      (Filling.transport_eqToIso e ((normalizedPathFilling F hF a₀ a₁).reindex σ)).symm
    _ = ((pathFilling F hF a₀ a₁).reindex σ).transport ((pathReindexIso B a₀ a₁ σ).trans n) :=
      congrArg (fun k => ((pathFilling F hF a₀ a₁).reindex σ).transport k) (normalizedPathIso_reindex B a₀ a₁ σ)
    _ = _ := congrArg (fun H => H.transport n) (pathFilling_reindex_iso F hF a₀ a₁ σ)

end SquareKit.Cubical.Presheaf
