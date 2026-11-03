import SquareKit.Internal.PathTransport.GroupoidElimination
import SquareKit.Internal.PathTransport.ContextualElimination
import Mathlib.CategoryTheory.Grothendieck

/-! Squares of equivalences and strict naturality of normalized elimination.
The square retains its contraction coherence after each dependent extension. -/

open CategoryTheory CategoryTheory.Functor
namespace SquareKit.Internal.PathTransport.GroupoidModel.GrothSquare
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v' w z
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {C' : Type*} [Category* C'] {D' : Type*} [Category* D']

lemma map_pre_congr (H : D ⥤ Cat.{w,z}) {R₁ R₂ : C ⥤ D}
    {F : C ⥤ Cat.{w,z}} (α : F ⟶ R₁ ⋙ H) (h : R₁ = R₂) :
    Grothendieck.map (α ≫ eqToHom (congrArg (· ⋙ H) h)) ⋙ Grothendieck.pre H R₂ =
      Grothendieck.map α ⋙ Grothendieck.pre H R₁ := by
  subst R₂
  simp

lemma retraction_square (H : D ⥤ Cat.{w,z}) (F : C ⥤ Cat.{w,z})
    (R : C ⥤ D) (R' : C' ⥤ D') (K : C' ⥤ C) (L : D' ⥤ D)
    (α : F ⟶ R ⋙ H) (β : K ⋙ F ⟶ R' ⋙ L ⋙ H)
    (hr : K ⋙ R = R' ⋙ L)
    (hc : β = whiskerLeft K α ≫ eqToHom (congrArg (· ⋙ H) hr)) :
    Grothendieck.pre F K ⋙ Grothendieck.map α ⋙ Grothendieck.pre H R =
      Grothendieck.map β ⋙ Grothendieck.pre (L ⋙ H) R' ⋙ Grothendieck.pre H L := by
  rw [Grothendieck.pre_comp_map_assoc K α (Grothendieck.pre H R)]
  rw [hc]
  change Grothendieck.map (whiskerLeft K α) ⋙
      Grothendieck.pre H (K ⋙ R) =
    Grothendieck.map (whiskerLeft K α ≫ eqToHom (congrArg (· ⋙ H) hr)) ⋙
      Grothendieck.pre H (R' ⋙ L)
  exact (map_pre_congr H (whiskerLeft K α) hr).symm
end SquareKit.Internal.PathTransport.GroupoidModel.GrothSquare

namespace SquareKit.Internal.PathTransport.GroupoidModel.GrothSquare
open CategoryTheory
variable {C : Type*} [Category* C] {D : Type*} [Category* D]
variable (F : C ⥤ Cat) (K : D ⥤ C)
lemma pre_transportIso (a : Grothendieck (K ⋙ F)) {d : D} (e : a.base ≅ d) :
    (Grothendieck.pre F K).mapIso (Grothendieck.transportIso a e) =
      Grothendieck.transportIso ((Grothendieck.pre F K).obj a) (K.mapIso e) := rfl
end SquareKit.Internal.PathTransport.GroupoidModel.GrothSquare

namespace SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
variable (e : D ≌ C) (e' : D' ≌ C') (K : C' ⥤ C) (L : D' ⥤ D)
structure Square where
  forward : e'.functor ⋙ K = L ⋙ e.functor
  inverse : K ⋙ e.inverse = e'.inverse ⋙ L
  counitInv :
    whiskerRight e'.counitInv K ≫ eqToHom (congrArg (e'.inverse ⋙ ·) forward) =
      whiskerLeft K e.counitInv ≫ eqToHom (congrArg (· ⋙ e.functor) inverse)
variable (s : Square e e' K L) (T : C ⥤ Cat)

def branchMap : Grothendieck (e'.functor ⋙ K ⋙ T) ⥤ Grothendieck (e.functor ⋙ T) :=
  Grothendieck.map (eqToHom (congrArg (· ⋙ T) s.forward)) ⋙
    Grothendieck.pre (e.functor ⋙ T) L

theorem forward_lift :
    (Grothendieck.preEquivalence (K ⋙ T) e').functor ⋙ Grothendieck.pre T K =
      branchMap e e' K L s T ⋙ (Grothendieck.preEquivalence T e).functor := by
  have h := GrothSquare.map_pre_congr T (𝟙 (e'.functor ⋙ K ⋙ T)) s.forward
  simpa [branchMap, Grothendieck.map_id_eq, Grothendieck.preEquivalence, Functor.id_comp, Functor.assoc] using h.symm

theorem inverse_lift :
    Grothendieck.pre T K ⋙ (Grothendieck.preEquivalence T e).inverse =
      (Grothendieck.preEquivalence (K ⋙ T) e').inverse ⋙ branchMap e e' K L s T := by
  have hc : whiskerRight e'.counitInv (K ⋙ T) ≫
      whiskerLeft e'.inverse (eqToHom (congrArg (· ⋙ T) s.forward)) =
      whiskerLeft K (whiskerRight e.counitInv T) ≫
        eqToHom (congrArg (· ⋙ e.functor ⋙ T) s.inverse) := by
    apply NatTrans.ext
    funext a
    have h := congrArg (fun q => T.map (q.app a)) s.counitInv
    simpa [Functor.map_comp, eqToHom_map] using h
  have h := GrothSquare.retraction_square (e.functor ⋙ T) T e.inverse e'.inverse K L
    (whiskerRight e.counitInv T)
    (whiskerRight e'.counitInv (K ⋙ T) ≫
      whiskerLeft e'.inverse (eqToHom (congrArg (· ⋙ T) s.forward))) s.inverse hc
  dsimp [Grothendieck.preEquivalence, Grothendieck.preInv, branchMap]
  simpa [Grothendieck.map_comp_eq, Functor.assoc, Grothendieck.pre_comp_map_assoc] using h

set_option maxHeartbeats 1000000 in
theorem liftSquare : Square (Grothendieck.preEquivalence T e)
    (Grothendieck.preEquivalence (K ⋙ T) e') (Grothendieck.pre T K)
    (branchMap e e' K L s T) where
  forward := forward_lift e e' K L s T
  inverse := inverse_lift e e' K L s T
  counitInv := by
    apply NatTrans.ext
    funext a
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, eqToHom_app]
    fapply Grothendieck.ext
    · simp [Grothendieck.preEquivalence, Grothendieck.preNatIso,
        Grothendieck.transportIso, Grothendieck.isoMk, branchMap]
      have h := congrArg (fun α => α.app a.base) s.counitInv
      simpa using h
    · simp [Grothendieck.preEquivalence, Grothendieck.preNatIso,
        Grothendieck.transportIso, Grothendieck.isoMk, branchMap]
end SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare
open CategoryTheory CategoryTheory.Functor
namespace SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {E : Type*} [Category* E] (F : C ⥤ Cat.{w,z}) (K : D ⥤ C)
variable (t : E ⥤ Grothendieck (K ⋙ F)) {L : E ⥤ D}
variable (α : t ⋙ Grothendieck.forget (K ⋙ F) ≅ L)

theorem normalize_congr {t₁ t₂ : E ⥤ Grothendieck F} {L₁ L₂ : E ⥤ C}
    (α₁ : t₁ ⋙ Grothendieck.forget F ≅ L₁)
    (α₂ : t₂ ⋙ Grothendieck.forget F ≅ L₂)
    (h : t₁ = t₂) (hb : L₁ = L₂)
    (hc : α₁ = eqToIso (congrArg (· ⋙ Grothendieck.forget F) h) ≪≫
      α₂ ≪≫ (eqToIso hb).symm) : normalize t₁ α₁ = normalize t₂ α₂ := by
  subst t₂
  subst L₂
  simp at hc
  subst α₁
  rfl

variable {B : Type*} [Category* B]
variable (q : B ⥤ Grothendieck F) {N : B ⥤ C}
variable (β : q ⋙ Grothendieck.forget F ≅ N)
variable (S : E ⥤ B)
variable (h : t ⋙ Grothendieck.pre F K = S ⋙ q)
variable (hb : L ⋙ K = S ⋙ N)
variable (hc : isoWhiskerRight α K =
    eqToIso (congrArg (· ⋙ Grothendieck.forget F) h) ≪≫
      isoWhiskerLeft S β ≪≫ (eqToIso hb).symm)

include h hb hc in
theorem normalize_square :
    normalize t α ⋙ Grothendieck.pre F K = S ⋙ normalize q β := by
  rw [normalize_pre]
  exact (normalize_congr F (isoWhiskerRight α K) (isoWhiskerLeft S β) h hb hc).trans
    (normalize_precomp q β S)
end SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination
namespace SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare
open CategoryTheory CategoryTheory.Functor
open SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
variable (e : D ≌ C) (e' : D' ≌ C') (K : C' ⥤ C) (L : D' ⥤ D)
variable (sq : Square e e' K L) (F : C ⥤ Cat)
variable (s : D ⥤ Grothendieck F) (s' : D' ⥤ Grothendieck (K ⋙ F))
variable (hs : s ⋙ Grothendieck.forget F = e.functor)
variable (hs' : s' ⋙ Grothendieck.forget (K ⋙ F) = e'.functor)
variable (hb : s' ⋙ Grothendieck.pre F K = L ⋙ s)

include sq hb in
theorem extend_square :
    extend e'.inverse e'.functor e'.counitIso s' hs' ⋙ Grothendieck.pre F K =
      K ⋙ extend e.inverse e.functor e.counitIso s hs := by
  have ht : (e'.inverse ⋙ s') ⋙ Grothendieck.pre F K = K ⋙ e.inverse ⋙ s := by
    change e'.inverse ⋙ (s' ⋙ Grothendieck.pre F K) = (K ⋙ e.inverse) ⋙ s
    rw [hb, sq.inverse]
    exact (Functor.assoc _ _ _).symm
  apply normalize_square F K (e'.inverse ⋙ s') _ (e.inverse ⋙ s) _ K ht rfl
  apply Iso.ext
  apply NatTrans.ext
  funext a
  have h₀ := congrArg (fun q => q.app a) sq.counitInv
  have h := IsIso.inv_eq_inv.mpr h₀
  simp [IsIso.inv_comp, inv_eqToHom, ← Functor.map_inv] at h
  dsimp
  simp only [Functor.map_comp, eqToHom_map, eqToHom_app,
    Category.comp_id]
  have hp : K.obj (s'.obj (e'.inverse.obj a)).base = e.functor.obj (L.obj (e'.inverse.obj a)) :=
    (congrArg K.obj (Functor.congr_obj hs' (e'.inverse.obj a))).trans
      (Functor.congr_obj sq.forward (e'.inverse.obj a))
  simpa only [Category.assoc, eqToHom_trans_assoc] using
    congrArg (fun f => eqToHom hp ≫ f) h
end SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare

namespace SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare
open CategoryTheory CategoryTheory.Functor
open SquareKit.Internal.PathTransport.GroupoidModel
open PathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Γ : Type*} [Category* Γ] [IsGroupoid Γ]
variable {Δ : Type*} [Category* Δ] [IsGroupoid Δ]
variable (A : Γ ⥤ Grpd) (x : Section A) (σ : Δ ⥤ Γ)

theorem rootSquare : Square (pathEquivalence A x)
    (pathEquivalence (σ ⋙ A) (x.reindex σ)) (substitution A x σ) σ where
  forward := rfl
  inverse := rfl
  counitInv := by
    simpa [pathEquivalence] using congrArg Iso.inv (substitution_contraction A x σ)
end SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare

namespace SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare
open CategoryTheory
open SquareKit.Internal.PathTransport.GroupoidModel
open ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D C D' C' : Cat.{u,u}}
variable (e : NormalizedEquivalence D C) (e' : NormalizedEquivalence D' C')
variable (K : C' ⥤ C) (L : D' ⥤ D)
variable (sq : Square e.equiv e'.equiv K L)

include sq in
theorem changeFunctorSquare (F : D ⥤ C) (F' : D' ⥤ C')
    (h : e.equiv.functor = F) (h' : e'.equiv.functor = F') :
    Square (e.changeFunctor F h).equiv (e'.changeFunctor F' h').equiv K L := by
  subst F
  subst F'
  simpa [NormalizedEquivalence.changeFunctor, Equivalence.changeFunctor_refl] using sq

variable (A : C ⥤ Grpd.{u,u})
variable (d : Section (e.equiv.functor ⋙ A))
variable (d' : Section (e'.equiv.functor ⋙ K ⋙ A))

include sq in
theorem eliminateSection_square
    (hd : pair (K ⋙ A) e'.equiv.functor d' ⋙ Grothendieck.pre (A ⋙ Grpd.forgetToCat) K =
      L ⋙ pair A e.equiv.functor d) :
    eliminateSection e' (K ⋙ A) d' = (eliminateSection e A d).reindex K := by
  apply pair_injective K
  change (eliminateSection e' (K ⋙ A) d').lift ⋙
      Grothendieck.pre (A ⋙ Grpd.forgetToCat) K = K ⋙ (eliminateSection e A d).lift
  simp only [eliminateSection, Section.ofOver_lift]
  exact extend_square e.equiv e'.equiv K L sq (A ⋙ Grpd.forgetToCat)
    (pair A e.equiv.functor d) (pair (K ⋙ A) e'.equiv.functor d') rfl rfl hd
end SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare

namespace SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare
open CategoryTheory SquareKit.Internal.PathTransport.GroupoidModel
open ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D D' C' : Cat.{u,u}}

theorem pair_cast (A : C ⥤ Grpd.{u,u}) {F G : D ⥤ C} (h : F = G)
    (d : Section (G ⋙ A)) :
    pair A F (cast (congrArg (fun F => Section (F ⋙ A)) h.symm) d) = pair A G d := by
  subst G
  rfl

noncomputable def reindexBranch (e : NormalizedEquivalence D C)
    (e' : NormalizedEquivalence D' C') (K : C' ⥤ C) (L : D' ⥤ D)
    (sq : Square e.equiv e'.equiv K L) (A : C ⥤ Grpd.{u,u})
    (d : Section (e.equiv.functor ⋙ A)) : Section (e'.equiv.functor ⋙ K ⋙ A) :=
  cast (congrArg (fun F => Section (F ⋙ A)) sq.forward.symm) (d.reindex L)

theorem eliminateSection_substitution (e : NormalizedEquivalence D C)
    (e' : NormalizedEquivalence D' C') (K : C' ⥤ C) (L : D' ⥤ D)
    (sq : Square e.equiv e'.equiv K L) (A : C ⥤ Grpd.{u,u})
    (d : Section (e.equiv.functor ⋙ A)) :
    eliminateSection e' (K ⋙ A) (reindexBranch e e' K L sq A d) =
      (eliminateSection e A d).reindex K := by
  apply eliminateSection_square e e' K L sq A d
  exact pair_cast A sq.forward (d.reindex L)
end SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare

namespace SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare
open CategoryTheory SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D D' : Type u} [Category.{u} D] [Category.{u} D']

theorem map_cast_pair (A : D ⥤ Grpd.{u,u}) (L : D' ⥤ D)
    (B : D' ⥤ Grpd.{u,u}) (h : B = L ⋙ A) :
    pair A (weaken B ⋙ L)
      (cast (congrArg Section (congrArg (weaken B ⋙ ·) h)) («variable» B)) =
    Grothendieck.map (eqToHom (congrArg (· ⋙ Grpd.forgetToCat) h)) ⋙
      Grothendieck.pre (A ⋙ Grpd.forgetToCat) L := by
  subst B
  simp only [eqToHom_refl, Grothendieck.map_id_eq, Functor.id_comp]
  rfl
end SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare
