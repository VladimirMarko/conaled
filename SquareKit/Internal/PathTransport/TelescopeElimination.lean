import SquareKit.Internal.PathTransport.ContextualElimination

/-!
# Elimination under repeated dependent extensions

A normalized groupoid equivalence retains its strict unit after a
Grothendieck extension. This invariant can be iterated over finite dependent
telescopes; it gives strict reflexive computation for section extension.
-/
open CategoryTheory CategoryTheory.Functor
universe u v u' v' w z
namespace SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination.RepeatedTail
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (e : D ≌ C) (hobj : ∀ d, d = e.inverse.obj (e.functor.obj d))
variable (hhom : ∀ d, e.unitIso.hom.app d = eqToHom (hobj d))

include hhom in
lemma counitInv (d : D) : e.counitIso.inv.app (e.functor.obj d) =
    e.functor.map (eqToHom (hobj d)) := by
  apply (cancel_mono (e.counitIso.hom.app (e.functor.obj d))).mp
  rw [← hhom]
  exact ((e.counitIso.app (e.functor.obj d)).inv_hom_id).trans
    (e.functor_unitIso_comp d).symm

variable (T : C ⥤ Cat.{w,z})

lemma transport_eqToHom (a : Grothendieck (e.functor ⋙ T))
    {d : D} (h : a.base = d) : a.transport (eqToHom h) = a := by
  cases h
  simp [Grothendieck.transport]

include hobj hhom in
lemma lifted_unit_obj (a : Grothendieck (e.functor ⋙ T)) :
    a = (Grothendieck.preEquivalence T e).inverse.obj
      ((Grothendieck.preEquivalence T e).functor.obj a) := by
  dsimp [Grothendieck.preEquivalence, Grothendieck.preInv,
    Grothendieck.map, Grothendieck.pre]
  rw [counitInv e hobj hhom]
  change a = a.transport (eqToHom (hobj a.base))
  exact (transport_eqToHom e T a (hobj a.base)).symm
include hobj hhom in
lemma counitHom (d : D) : e.counitIso.hom.app (e.functor.obj d) =
    eqToHom (congrArg e.functor.obj (hobj d).symm) := by
  apply (cancel_epi (e.counitIso.inv.app (e.functor.obj d))).mp
  calc
    _ = 𝟙 _ := (e.counitIso.app (e.functor.obj d)).inv_hom_id
    _ = _ := by rw [counitInv e hobj hhom]; simp [eqToHom_map]

include hobj hhom in
lemma lifted_counit_hom (a : Grothendieck (e.functor ⋙ T)) :
    (Grothendieck.preEquivalence T e).counitIso.hom.app
        ((Grothendieck.preEquivalence T e).functor.obj a) =
      eqToHom (congrArg (Grothendieck.preEquivalence T e).functor.obj
        (lifted_unit_obj e hobj hhom T a).symm) := by
  fapply Grothendieck.ext
  · simp [Grothendieck.preEquivalence, Grothendieck.preNatIso,
      Grothendieck.transportIso, Grothendieck.isoMk, counitHom e hobj hhom]
  · simp [Grothendieck.preEquivalence, Grothendieck.preNatIso,
      Grothendieck.transportIso, Grothendieck.isoMk]

include hobj hhom in
lemma lifted_unit_hom (a : Grothendieck (e.functor ⋙ T)) :
    (Grothendieck.preEquivalence T e).unitIso.hom.app a =
      eqToHom (lifted_unit_obj e hobj hhom T a) := by
  apply (Grothendieck.preEquivalence T e).functor.map_injective
  apply (cancel_mono ((Grothendieck.preEquivalence T e).counitIso.hom.app
    ((Grothendieck.preEquivalence T e).functor.obj a))).mp
  calc
    _ = 𝟙 _ := (Grothendieck.preEquivalence T e).functor_unitIso_comp a
    _ = _ := by rw [lifted_counit_hom e hobj hhom]; simp [eqToHom_map]
end SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination.RepeatedTail

namespace SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (e : D ≌ C) (hobj : ∀ d, d = e.inverse.obj (e.functor.obj d))
variable (hhom : ∀ d, e.unitIso.hom.app d = eqToHom (hobj d))

include hobj hhom in
theorem normalized_retraction : e.functor ⋙ e.inverse = 𝟭 _ :=
  (Functor.ext_of_iso e.unitIso hobj hhom).symm

include hobj hhom in
theorem extend_beta {F : C ⥤ Cat}
    (s : D ⥤ Grothendieck F) (hs : s ⋙ Grothendieck.forget F = e.functor) :
    e.functor ⋙ extend e.inverse e.functor e.counitIso s hs = s := by
  have hr : e.functor ⋙ e.inverse ⋙ s = s := by
    change (e.functor ⋙ e.inverse) ⋙ s = s
    rw [normalized_retraction e hobj hhom]; rfl
  let α := (eqToIso (congrArg (e.inverse ⋙ ·) hs)) ≪≫ e.counitIso
  have h : (e.functor ⋙ (e.inverse ⋙ s)) ⋙ Grothendieck.forget F =
      e.functor ⋙ 𝟭 _ := by rw [hr]; exact hs
  have hα : isoWhiskerLeft e.functor α = eqToIso h := by
    ext a
    dsimp [α]
    rw [RepeatedTail.counitHom e hobj hhom]
    simp
  exact (normalize_restriction (e.inverse ⋙ s) α e.functor h hα).trans hr
end SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination

namespace SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {E : Type*} [Category* E] (F : C ⥤ Cat.{w,z}) (K : D ⥤ C)
variable (t : E ⥤ Grothendieck (K ⋙ F)) {L : E ⥤ D}
variable (α : t ⋙ Grothendieck.forget (K ⋙ F) ≅ L)


theorem normalize_pre :
    normalize t α ⋙ Grothendieck.pre F K =
      normalize (t ⋙ Grothendieck.pre F K) (isoWhiskerRight α K) := by
  fapply Functor.ext
  · intro a; rfl
  · intro a b f
    simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
    change (Grothendieck.pre F K).map
        ((normalizeIso t α a).hom ≫ t.map f ≫ (normalizeIso t α b).inv) = _
    rw [Functor.map_comp, Functor.map_comp]
    rfl
end SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination

namespace SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination
open CategoryTheory
universe q

/-- The unit is equality transport, not a potentially nontrivial automorphism. -/
structure NormalizedEquivalence (D C : Cat.{q,q}) where
  equiv : D ≌ C
  unit_obj : ∀ d, d = equiv.inverse.obj (equiv.functor.obj d)
  unit_hom : ∀ d, equiv.unitIso.hom.app d = eqToHom (unit_obj d)

/-- Extend the normalized equivalence by one arbitrary dependent family. -/
def NormalizedEquivalence.extend {D C : Cat.{q,q}}
    (e : NormalizedEquivalence D C) (A : C ⥤ Cat.{q,q}) :
    NormalizedEquivalence (Cat.of (Grothendieck (e.equiv.functor ⋙ A)))
      (Cat.of (Grothendieck A)) where
  equiv := Grothendieck.preEquivalence A e.equiv
  unit_obj := RepeatedTail.lifted_unit_obj e.equiv e.unit_obj e.unit_hom A
  unit_hom := RepeatedTail.lifted_unit_hom e.equiv e.unit_obj e.unit_hom A

/-- Each next declaration can depend on the complete preceding extension. -/
inductive Telescope : Cat.{q,q} → Cat.{q,q} → Type (q+1) where
  | empty (C) : Telescope C C
  | ext {C D} (tail : Telescope C D) (A : D ⥤ Cat.{q,q}) :
      Telescope C (Cat.of (Grothendieck A))

/-- Pull back a finite telescope and retain normalized elimination at its tip. -/
def Telescope.reindex {C D E : Cat.{q,q}} (tail : Telescope C D)
    (e : NormalizedEquivalence E C) :
    Σ E' : Cat.{q,q}, Telescope E E' × NormalizedEquivalence E' D :=
  match tail with
  | .empty _ => ⟨E, .empty E, e⟩
  | .ext previous A =>
    let ⟨_E', branch, comparison⟩ := previous.reindex e
    ⟨Cat.of (Grothendieck (comparison.equiv.functor ⋙ A)),
      .ext branch (comparison.equiv.functor ⋙ A), comparison.extend A⟩

/-- Extend a branch after any finite sequence of dependent declarations. -/
def NormalizedEquivalence.eliminate {D C : Cat.{q,q}}
    (e : NormalizedEquivalence D C) {A : C ⥤ Cat.{q,q}}
    (s : D ⥤ Grothendieck A) (hs : s ⋙ Grothendieck.forget A = e.equiv.functor) :
    C ⥤ Grothendieck A :=
  ContextualElimination.extend e.equiv.inverse e.equiv.functor e.equiv.counitIso s hs

/-- Reflexive computation remains an equality after every dependent extension. -/
theorem NormalizedEquivalence.eliminate_beta {D C : Cat.{q,q}}
    (e : NormalizedEquivalence D C) {A : C ⥤ Cat.{q,q}}
    (s : D ⥤ Grothendieck A) (hs : s ⋙ Grothendieck.forget A = e.equiv.functor) :
    e.equiv.functor ⋙ e.eliminate s hs = s :=
  extend_beta e.equiv e.unit_obj e.unit_hom s hs

end SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination

namespace SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe q

def NormalizedEquivalence.changeFunctor {D C : Cat.{q,q}}
    (e : NormalizedEquivalence D C) (F : D ⥤ C) (h : e.equiv.functor = F) :
    NormalizedEquivalence D C where
  equiv := e.equiv.changeFunctor (eqToIso h)
  unit_obj d := (e.unit_obj d).trans
    (congrArg e.equiv.inverse.obj (CategoryTheory.Functor.congr_obj h d))
  unit_hom d := by
    cases h
    simpa [Equivalence.changeFunctor] using e.unit_hom d
end SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination
