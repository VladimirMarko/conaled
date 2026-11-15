import SquareKit.Internal.Cubical.ScaledBoxMap

/-! Compatibility of chosen compositions with a family map extends to the
whole fillers constructed from those compositions. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem Term.map_convert_sub {Γ Δ : Context.{u}} {A B : Family Γ} (η : A ⟶ B)
    {p q : Δ ⟶ Γ} (e : p = q) (t : Term (Presheaf.reindex A p)) :
    Term.map (Functor.whiskerLeft q.mapElements η) (t.convert (congrArg (Presheaf.reindex A) e)) =
      (Term.map (Functor.whiskerLeft p.mapElements η) t).convert (congrArg (Presheaf.reindex B) e) := by
  cases e
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem Composition.fill_map {Γ : Context.{u}} {A B : Family Γ}
    (C : Composition A) (D : Composition B) (η : A ⟶ B)
    (hc : ∀ {Δ : Context.{u}} (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
      (b : OpenBox (Presheaf.reindex A p) φ),
      D.comp p φ (b.map (Functor.whiskerLeft p.mapElements η)) =
        Term.map (Functor.whiskerLeft (endpointSub Δ true ≫ p).mapElements η) (C.comp p φ b))
    {Δ : Context.{u}} (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (Presheaf.reindex A p) φ) :
    D.fill p φ (b.map (Functor.whiskerLeft p.mapElements η)) =
      Term.map (Functor.whiskerLeft p.mapElements η) (C.fill p φ b) := by
  have hs := scaledBox_map (Functor.whiskerLeft p.mapElements η) b
  have hd := congrArg (D.comp (scaleInterval Δ ≫ p) (scaledFace φ)) hs
  have hh := hd.trans (hc (scaleInterval Δ ≫ p) (scaledFace φ) (scaledBox b))
  have e : endpointSub (total (interval Δ)) true ≫ scaleInterval Δ ≫ p = p :=
    congrArg (fun q => q ≫ p) (scaleInterval_one Δ)
  exact (congrArg (fun t : Term (Presheaf.reindex B
      (endpointSub (total (interval Δ)) true ≫ scaleInterval Δ ≫ p)) =>
        t.convert (congrArg (Presheaf.reindex B) e)) hh).trans
    (Term.map_convert_sub η e _).symm

end SquareKit.Cubical.Presheaf
