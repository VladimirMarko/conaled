import SquareKit.Internal.PathTransport.FamilyMapPath

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D C' D' C'' D'' : Type u}
  [Category.{u} C] [Category.{u} D] [Category.{u} C'] [Category.{u} D']
  [Category.{u} C''] [Category.{u} D'']

/-- Composition retains the contraction coherence, not just its outer edges. -/
theorem Square.comp {e : D ≌ C} {e' : D' ≌ C'} {e'' : D'' ≌ C''}
    {K : C' ⥤ C} {L : D' ⥤ D} {K' : C'' ⥤ C'} {L' : D'' ⥤ D'}
    (s : Square e e' K L) (t : Square e' e'' K' L') :
    Square e e'' (K' ⋙ K) (L' ⋙ L) where
  forward := by rw [← CategoryTheory.Functor.assoc, t.forward,
    CategoryTheory.Functor.assoc, s.forward]; rfl
  inverse := by rw [CategoryTheory.Functor.assoc, s.inverse,
    ← CategoryTheory.Functor.assoc, t.inverse]; rfl
  counitInv := by
    apply NatTrans.ext
    funext a
    have hs := congrArg (fun q => q.app (K'.obj a)) s.counitInv
    have ht := congrArg (fun q => K.map (q.app a)) t.counitInv
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, eqToHom_app,
      CategoryTheory.Functor.map_comp, eqToHom_map] at hs ht ⊢
    have ht' := congrArg (fun f => f ≫ eqToHom
      (CategoryTheory.Functor.congr_obj s.forward (L'.obj (e''.inverse.obj a)))) ht
    have hs' := congrArg (fun f => f ≫ eqToHom (congrArg
      (fun d => e.functor.obj (L.obj d)) (CategoryTheory.Functor.congr_obj t.inverse a))) hs
    simp only [Category.assoc, eqToHom_trans] at ht' hs'
    exact ht'.trans hs'
end SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare

namespace SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- A changing dependent family induces a coherent square between the lifted
contractions. No equivalence assumption is made on the family transformation. -/
theorem familyLiftSquare (e : D ≌ C) {A B : C ⥤ Cat.{u,u}} (α : A ⟶ B) :
    Square (Grothendieck.preEquivalence B e) (Grothendieck.preEquivalence A e)
      (Grothendieck.map α) (Grothendieck.map (whiskerLeft e.functor α)) where
  forward := rfl
  inverse := by
    change Grothendieck.map α ⋙ Grothendieck.map (whiskerRight e.counitInv B) ⋙
      Grothendieck.pre (e.functor ⋙ B) e.inverse =
      Grothendieck.map (whiskerRight e.counitInv A) ⋙
        Grothendieck.pre (e.functor ⋙ A) e.inverse ⋙
          Grothendieck.map (whiskerLeft e.functor α)
    rw [Grothendieck.pre_comp_map]
    rw [← CategoryTheory.Functor.assoc, ← CategoryTheory.Functor.assoc,
      ← Grothendieck.map_comp_eq, ← Grothendieck.map_comp_eq]
    congr 1
    congr 1
    apply NatTrans.ext
    funext c
    exact (α.naturality (e.counitInv.app c)).symm
  counitInv := by
    apply NatTrans.ext
    funext a
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, eqToHom_app]
    fapply Grothendieck.ext
    · simp [Grothendieck.preEquivalence, Grothendieck.preNatIso, Grothendieck.map,
        Grothendieck.transportIso, Grothendieck.isoMk, Grothendieck.base_eqToHom]
    · simp [Grothendieck.preEquivalence, Grothendieck.preNatIso, Grothendieck.map,
        Grothendieck.transportIso, Grothendieck.isoMk, eqToHom_map]

end SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare

namespace SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D C' D' : Type u}
  [Category.{u} C] [Category.{u} D] [Category.{u} C'] [Category.{u} D']

/-- Extend a coherent contraction square by independently specified dependent
families and their natural comparison. -/
theorem liftChangingSquare (e : D ≌ C) (e' : D' ≌ C') (K : C' ⥤ C) (L : D' ⥤ D)
    (sq : Square e e' K L) (A : C ⥤ Cat.{u,u}) (B : C' ⥤ Cat.{u,u}) (α : B ⟶ K ⋙ A) :
    Square (Grothendieck.preEquivalence A e) (Grothendieck.preEquivalence B e')
      (Grothendieck.map α ⋙ Grothendieck.pre A K)
      (Grothendieck.map (whiskerLeft e'.functor α) ⋙ branchMap e e' K L sq A) :=
  (liftSquare e e' K L sq A).comp (familyLiftSquare e' α)

end SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare

namespace SquareKit.Internal.PathTransport.GroupoidModel.PathComparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ Δ : Type u} [Category.{u} Γ] [Category.{u} Δ]
variable {A B : Γ ⥤ Grpd.{u,u}}

/-- Relabel the image point by an explicit equality of sections. -/
def familyMapTo (α : A ⟶ B) (x : Section A) (y : Section B)
    (h : x.familyImage α = y) : PathCtx A x ⥤ PathCtx B y := h ▸ familyMap α x

variable [IsGroupoid Γ]
theorem familyMapToSquare (α : A ⟶ B) (x : Section A) (y : Section B)
    (h : x.familyImage α = y) :
    EquivalenceSquare.Square (pathEquivalence B y) (pathEquivalence A x)
      (familyMapTo α x y h) (𝟭 Γ) := by
  cases h
  exact familyMapSquare α x

variable [IsGroupoid Δ]

/-- A general base/family map induces the actual path-contraction comparison.
The endpoint equation is equality of sections, including their arrow action. -/
theorem baseFamilySquare (A : Γ ⥤ Grpd.{u,u}) (B : Δ ⥤ Grpd.{u,u})
    (K : Δ ⥤ Γ) (α : B ⟶ K ⋙ A) (x : Section A) (y : Section B)
    (h : y.familyImage α = x.reindex K) :
    EquivalenceSquare.Square (pathEquivalence A x) (pathEquivalence B y)
      (familyMapTo α y (x.reindex K) h ⋙ substitution A x K) K :=
  (EquivalenceSquare.rootSquare A x K).comp (familyMapToSquare α y (x.reindex K) h)

end SquareKit.Internal.PathTransport.GroupoidModel.PathComparison
