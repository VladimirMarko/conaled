import SquareKit.Internal.PathTransport.TwoIdentityTransport
namespace SquareKit.Internal.PathTransport.TwoIdentityTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w u' v' w'
variable {A : Type u} [Bicategory.{w,v} A] [Strict A]
variable {B : Type u'} [Bicategory.{w',v'} B] [Strict B] [IsLocallyGroupoid B]
omit [IsLocallyGroupoid B] in
/-- Inverse whiskering recovers a cell up to the strict unit boundary casts. -/
theorem inverse_whisker_heq {a b c : B} (f : a ⟶ b) [IsIso f]
    {g h : b ⟶ c} (α : g ⟶ h) : HEq (inv f ◁ (f ◁ α)) α := by
  have hh := heq_of_eq (comp_whiskerLeft (inv f) f α)
  simp only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff] at hh
  apply HEq.trans hh.symm
  rw [IsIso.inv_hom_id]
  simp only [id_whiskerLeft, Strict.leftUnitor_eqToIso, eqToIso.hom, eqToIso.inv]
  apply HEq.trans (eqToHom_comp_heq _ _)
  exact comp_eqToHom_heq _ _
omit [IsLocallyGroupoid B] in
/-- Whiskering by an invertible 1-arrow is injective on genuine 2-cells. -/
theorem iso_whiskerLeft_injective {a b c : B} (f : a ⟶ b) [IsIso f]
    {g h : b ⟶ c} (α β : g ⟶ h) (e : f ◁ α = f ◁ β) : α = β := by
  apply eq_of_heq
  exact (inverse_whisker_heq f α).symm.trans
    ((heq_of_eq (congrArg (fun z => inv f ◁ z) e)).trans (inverse_whisker_heq f β))
variable {F G : StrictPseudofunctor A B} (η : StrictTwoTransformation.Trans F G)
variable {a a' : A} {b b' : B} {u : F.obj a ⟶ b} {u' : G.obj a ⟶ b}
variable [IsIso u] [IsIso u'] {v : F.obj a' ⟶ b'} {v' : G.obj a' ⟶ b'}
omit [Strict A] in
/-- At an invertible transported path, a comparison determines its second endpoint cell. -/
theorem homComparison_second_injective (ρ : u ⟶ η.app a ≫ u') (σ τ : v ⟶ η.app a' ≫ v')
    (p : a ⟶ a') [IsIso (F.map p)]
    (h : (homComparison η ρ σ).app p = (homComparison η ρ τ).app p) : σ = τ := by
  simp only [homComparison, homNaturality, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  simp only [precomp_map, postcomposing_map_app, associatorNatIsoLeft_inv_app,
    associatorNatIsoMiddle_hom_app, associatorNatIsoRight_inv_app, precomposing_map_app] at h
  simp only [cancel_mono] at h
  have h' := iso_whiskerLeft_injective (inv u) _ _ h
  simp only [cancel_mono] at h'
  exact iso_whiskerLeft_injective (F.map p) σ τ h'
end SquareKit.Internal.PathTransport.TwoIdentityTransport
