import SquareKit.Internal.Cubical.Conversion

/-! Sections are transported along actual context isomorphisms. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

noncomputable def Term.descendIso {Γ Δ : Context.{u}} (e : Γ ≅ Δ) {A : Family Δ}
    (t : Term (Presheaf.reindex A e.hom)) : Term A :=
  (t.reindex e.inv).convert (congrArg (Presheaf.reindex A) e.inv_hom_id)

theorem Term.descendIso_reindex {Γ Δ : Context.{u}} (e : Γ ≅ Δ) {A : Family Δ}
    (t : Term (Presheaf.reindex A e.hom)) : (t.descendIso e).reindex e.hom = t := by
  apply Term.ext
  intro x
  apply eq_of_heq
  apply (Term.convert_val_heq _ _ (e.hom.mapElements.obj x)).trans
  have he : e.hom.mapElements ⋙ e.inv.mapElements = 𝟭 Γ.Elements :=
    congrArg NatTrans.mapElements e.hom_inv_id
  exact Term.val_heq_of_heq rfl (heq_of_eq (rfl : t = t))
    (congrArg (fun q : Γ.Elements ⥤ Γ.Elements => q.obj x) he)

theorem Term.descendIso_reindex_section {Γ Δ : Context.{u}} (e : Γ ≅ Δ) {A : Family Δ}
    (t : Term A) : (t.reindex e.hom).descendIso e = t := by
  apply Term.ext
  intro x
  apply eq_of_heq
  apply (Term.convert_val_heq _ _ x).trans
  have he : e.inv.mapElements ⋙ e.hom.mapElements = 𝟭 Δ.Elements :=
    congrArg NatTrans.mapElements e.inv_hom_id
  exact Term.val_heq_of_heq rfl (heq_of_eq (rfl : t = t))
    (congrArg (fun q : Δ.Elements ⥤ Δ.Elements => q.obj x) he)

end SquareKit.Cubical.Presheaf
