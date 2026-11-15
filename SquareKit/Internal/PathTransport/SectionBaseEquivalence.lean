import SquareKit.Internal.PathTransport.SectionDescent

/-! Extend a complete section along an equivalence of base contexts. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.SectionDescent
open CategoryTheory CategoryTheory.Functor ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v' w z
variable {Γ : Type u} [Category.{v} Γ] {Δ : Type u'} [Category.{v'} Δ]
variable (e : Γ ≌ Δ) (B : Δ ⥤ Grpd.{z,w}) (s : Section (e.functor ⋙ B))

/-- View the supplied section in the target total family, still over its
original context. -/
def overBase : Γ ⥤ Extend B :=
  s.lift ⋙ Grothendieck.pre (B ⋙ Grpd.forgetToCat) e.functor

/-- Extend using the inverse base equivalence, then normalize the projection.
The input contains the section's complete action on context arrows. -/
def extendBase : Section B :=
  Section.ofOver
    (ContextualElimination.extend e.inverse e.functor e.counitIso (overBase e B s) rfl)
    (extend_over _ _ _ _ _)

/-- After restricting back, the constructed section recovers the supplied
functor into the total family. -/
def extendBaseRecovery : e.functor ⋙ (extendBase e B s).lift ≅ overBase e B s :=
  isoWhiskerLeft e.functor
    ((eqToIso (Section.ofOver_lift _ _)) ≪≫ normalizeComparison _ _) ≪≫
    isoWhiskerRight e.unitIso.symm (overBase e B s)

/-- Recovery lies over the identity of the image context. -/
theorem extendBaseRecovery_base (γ : Γ) :
    ((extendBaseRecovery e B s).hom.app γ).base = 𝟙 (e.functor.obj γ) := by
  simp [extendBaseRecovery, normalizeComparison, normalizeIso,
    Grothendieck.transportIso, Grothendieck.isoMk, overBase, Grothendieck.pre]
  change e.counitIso.inv.app (e.functor.obj γ) ≫
    𝟙 (e.functor.obj (e.inverse.obj (e.functor.obj γ))) ≫
    e.functor.map (e.unitIso.inv.app γ) = _
  exact (congrArg (e.counitIso.inv.app (e.functor.obj γ) ≫ ·)
    (Category.id_comp (e.functor.map (e.unitIso.inv.app γ)))).trans
      (e.counitInv_functor_comp γ)

/-- Restriction recovers the section in its original total family, retaining
all its context-arrow action. -/
def restrictRecovery : ((extendBase e B s).reindex e.functor).lift ≅ s.lift := by
  letI : (Grothendieck.pre (B ⋙ Grpd.forgetToCat) e.functor).IsEquivalence :=
    (Grothendieck.preEquivalence (B ⋙ Grpd.forgetToCat) e).isEquivalence_functor
  exact fullyFaithfulCancelRight (Grothendieck.pre (B ⋙ Grpd.forgetToCat) e.functor)
    (extendBaseRecovery e B s)

/-- The recovery in the original context is vertical as well. -/
theorem restrictRecovery_base (γ : Γ) :
    ((restrictRecovery e B s).hom.app γ).base = 𝟙 γ := by
  let : (Grothendieck.pre (B ⋙ Grpd.forgetToCat) e.functor).IsEquivalence :=
    (Grothendieck.preEquivalence (B ⋙ Grpd.forgetToCat) e).isEquivalence_functor
  have h := (Grothendieck.pre (B ⋙ Grpd.forgetToCat) e.functor).map_preimage
    (X := ((extendBase e B s).reindex e.functor).lift.obj γ) (Y := s.lift.obj γ)
    ((extendBaseRecovery e B s).hom.app γ)
  have hb := congrArg Grothendieck.Hom.base h
  change e.functor.map ((restrictRecovery e B s).hom.app γ).base = _ at hb
  rw [extendBaseRecovery_base] at hb
  apply e.functor.map_injective
  exact hb.trans (e.functor.map_id γ).symm

end SquareKit.Internal.PathTransport.GroupoidModel.SectionDescent
