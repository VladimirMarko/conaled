import SquareKit.Internal.PathTransport.TwoFamilySectionMap

/-! Coherent base homotopies act on every admitted higher section. -/
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w' u'' v'' w''
variable {A : Type u} [Bicategory.{w,v} A] [Bicategory.Strict A]
variable {B : Type u'} [Bicategory.{w',v'} B] [Bicategory.Strict B]
variable {C : Type u''} [Bicategory.{w'',v''} C] [Bicategory.Strict C]
variable {F G : StrictPseudofunctor A B}
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
variable (H : StrictPseudofunctor B C)
/-- Map the full coherent transformation through a strict higher functor. -/
def strongPostcomp : Pseudofunctor.StrongTrans (F.comp H).toPseudofunctor (G.comp H).toPseudofunctor where
  app x := H.map (η.app x)
  naturality f := (H.mapComp (F.map f) (η.app _)).symm ≪≫
    H.map₂Iso (η.naturality f) ≪≫ H.mapComp (η.app _) (G.map f)
  naturality_naturality {a b} {f g} α := by
    have h := congrArg H.map₂ (η.naturality_naturality α)
    have k := congrArg (fun z => eqToHom (H.map_comp (F.map f) (η.app b)).symm ≫
      z ≫ eqToHom (H.map_comp (η.app a) (G.map g))) h
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    change H.map₂ (F.map₂ α) ▷ H.map (η.app b) ≫
      (H.mapComp (F.map g) (η.app b)).inv ≫ H.map₂ (η.naturality g).hom ≫
        (H.mapComp (η.app a) (G.map g)).hom =
      (H.mapComp (F.map f) (η.app b)).inv ≫ H.map₂ (η.naturality f).hom ≫
        (H.mapComp (η.app a) (G.map f)).hom ≫ H.map (η.app a) ◁ H.map₂ (G.map₂ α)
    simpa only [PrelaxFunctor.map₂_comp, Pseudofunctor.map₂_whisker_left,
      Pseudofunctor.map₂_whisker_right, H.mapComp_eq_eqToIso,
      eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans_assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id] using k
  naturality_id x := by
    have h := congrArg H.map₂ (η.naturality_id x)
    have e : H.map (η.app x ≫ 𝟙 (G.obj x)) = H.map (η.app x) ≫ 𝟙 (H.obj (G.obj x)) := by simp
    have k := congrArg (fun z => eqToHom (H.map_comp (F.map (𝟙 x)) (η.app x)).symm ≫
      z ≫ eqToHom e) h
    simp only [PrelaxFunctor.map₂_comp, F.mapId_eq_eqToIso, G.mapId_eq_eqToIso,
      H.mapComp_eq_eqToIso, (F.comp H).mapId_eq_eqToIso, (G.comp H).mapId_eq_eqToIso,
      Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
      Bicategory.Strict.leftUnitor_eqToIso, Bicategory.Strict.rightUnitor_eqToIso,
      Bicategory.whiskerLeft_eqToHom, Bicategory.eqToHom_whiskerRight,
      PrelaxFunctor.map₂_eqToHom, Category.assoc, eqToHom_trans_assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id] at k ⊢
    change eqToHom _ ≫ H.map₂ (η.naturality (𝟙 x)).hom ≫ eqToHom _ = eqToHom _
    exact k
  naturality_comp {a b c} f g := by
    have h := congrArg H.map₂ (η.naturality_comp f g)
    have e : H.map (η.app a ≫ (G.map f ≫ G.map g)) =
        H.map (η.app a) ≫ (H.map (G.map f) ≫ H.map (G.map g)) := by
      rw [H.map_comp, H.map_comp]
    have k := congrArg (fun z => eqToHom (H.map_comp (F.map (f ≫ g)) (η.app c)).symm ≫
      z ≫ eqToHom e) h
    simp only [PrelaxFunctor.map₂_comp, F.mapComp_eq_eqToIso, G.mapComp_eq_eqToIso,
      H.mapComp_eq_eqToIso, (F.comp H).mapComp_eq_eqToIso, (G.comp H).mapComp_eq_eqToIso,
      Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
      Bicategory.Strict.associator_eqToIso,
      Bicategory.whiskerLeft_eqToHom, Bicategory.eqToHom_whiskerRight,
      Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_whisker_right,
      Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
      PrelaxFunctor.map₂_eqToHom, Category.assoc, eqToHom_trans_assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id] at k ⊢
    exact k
namespace TwoFamily
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]
variable {Δ : Type*} [Bicategory Δ] [Bicategory.Strict Δ]
variable (E : Family.{u,v,w,u',v',w'} Γ)
variable {σ τ : StrictPseudofunctor Δ Γ}
/-- Transport any section along a coherent base homotopy, retaining its full cell action. -/
def Section.transport (η : Pseudofunctor.StrongTrans σ.toPseudofunctor τ.toPseudofunctor)
    (s : Section (reindex σ E)) : Section (reindex τ E) :=
  s.map (strongPostcomp η E)
end TwoFamily
end SquareKit.Internal.PathTransport
