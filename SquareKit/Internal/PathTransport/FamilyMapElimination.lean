import SquareKit.Internal.PathTransport.GroupoidSoundness

/-! Family-map comparison for normalized elimination, independent of source
comparison packaging. -/
noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {A B : C ⥤ Cat.{u,u}} (α : A ⟶ B)
variable (t : D ⥤ Grothendieck A) {K : D ⥤ C}
variable (ε : t ⋙ Grothendieck.forget A ≅ K)

/-- A family map carries normalized transport to normalized transport. -/
theorem normalize_map : normalize t ε ⋙ Grothendieck.map α =
    normalize (t ⋙ Grothendieck.map α) ε := by
  let i := isoWhiskerRight (normalizeComparison t ε) (Grothendieck.map α) ≪≫
    (normalizeComparison (t ⋙ Grothendieck.map α) ε).symm
  refine CategoryTheory.Functor.ext_of_iso i ?_ ?_
  · intro d
    apply congrArg (fun x => (⟨K.obj d,x⟩ : Grothendieck B))
    exact congrArg (fun F => F.toFunctor.obj (t.obj d).fiber)
      (α.naturality (ε.hom.app d))
  · intro d
    fapply Grothendieck.ext
    · simp [i, normalizeComparison, normalizeIso, Grothendieck.map,
        Grothendieck.transportIso, Grothendieck.isoMk, Grothendieck.base_eqToHom]
    · simp [i, normalizeComparison, normalizeIso, Grothendieck.map,
        Grothendieck.transportIso, Grothendieck.isoMk, eqToHom_map]

variable {E F : Cat.{u,u}}

/-- Normalized elimination commutes strictly with a changing motive family.
The transformation is not assumed invertible or faithful. -/
theorem NormalizedEquivalence.eliminate_map (e : NormalizedEquivalence E F)
    {A B : F ⥤ Cat.{u,u}} (α : A ⟶ B)
    (s : E ⥤ Grothendieck A) (hs : s ⋙ Grothendieck.forget A = e.equiv.functor) :
    e.eliminate s hs ⋙ Grothendieck.map α =
      e.eliminate (s ⋙ Grothendieck.map α) hs :=
  normalize_map α (e.equiv.inverse ⋙ s) _

/-- The same strict comparison applies after any finite dependent telescope.
Every declaration may depend on the complete preceding extension. -/
theorem Telescope.eliminate_map {E F G : Cat.{u,u}} (T : Telescope F G)
    (e : NormalizedEquivalence E F) {A B : G ⥤ Cat.{u,u}} (α : A ⟶ B)
    (s : (T.reindex e).1 ⥤ Grothendieck A)
    (hs : s ⋙ Grothendieck.forget A = (T.reindex e).2.2.equiv.functor) :
    (T.reindex e).2.2.eliminate s hs ⋙ Grothendieck.map α =
      (T.reindex e).2.2.eliminate (s ⋙ Grothendieck.map α) hs :=
  NormalizedEquivalence.eliminate_map _ α s hs

end SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination

namespace SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare
open ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D C D' C' : Cat.{u,u}}

/-- Compare elimination across a coherent contraction square and a genuinely
changing family. The branch equation retains the entire functor, including
arrows; no target theorem or eliminator compatibility is assumed. -/
theorem eliminate_familyMap (e : NormalizedEquivalence D C)
    (e' : NormalizedEquivalence D' C') (K : C' ⥤ C) (L : D' ⥤ D)
    (sq : Square e.equiv e'.equiv K L)
    (A : C ⥤ Cat.{u,u}) (B : C' ⥤ Cat.{u,u}) (α : B ⟶ K ⋙ A)
    (s : D ⥤ Grothendieck A) (hs : s ⋙ Grothendieck.forget A = e.equiv.functor)
    (s' : D' ⥤ Grothendieck B) (hs' : s' ⋙ Grothendieck.forget B = e'.equiv.functor)
    (hb : s' ⋙ Grothendieck.map α ⋙ Grothendieck.pre A K = L ⋙ s) :
    e'.eliminate s' hs' ⋙ Grothendieck.map α ⋙ Grothendieck.pre A K =
      K ⋙ e.eliminate s hs := by
  rw [← CategoryTheory.Functor.assoc, NormalizedEquivalence.eliminate_map]
  exact extend_square e.equiv e'.equiv K L sq A s
    (s' ⋙ Grothendieck.map α) hs hs' hb

end SquareKit.Internal.PathTransport.GroupoidModel.EquivalenceSquare

namespace SquareKit.Internal.PathTransport.GroupoidModel
open ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C : Type u} [Category.{u} C]

/-- Apply a functor-valued family transformation to a section, retaining its
arrow action. This operation is independent of any source-comparison model. -/
def Section.mapFamily {A B : C ⥤ Grpd.{u,u}} (α : A ⟶ B) (s : Section A) : Section B :=
  Section.ofOver (s.lift ⋙ Grothendieck.map (whiskerRight α Grpd.forgetToCat)) rfl

theorem Section.mapFamily_lift {A B : C ⥤ Grpd.{u,u}} (α : A ⟶ B) (s : Section A) :
    (s.mapFamily α).lift = s.lift ⋙ Grothendieck.map (whiskerRight α Grpd.forgetToCat) :=
  Section.ofOver_lift _ _

theorem pair_mapFamily {E : Type u} [Category.{u} E] {A B : C ⥤ Grpd.{u,u}}
    (α : A ⟶ B) (K : E ⥤ C) (s : Section (K ⋙ A)) :
    pair B K (s.mapFamily (whiskerLeft K α)) =
      pair A K s ⋙ Grothendieck.map (whiskerRight α Grpd.forgetToCat) := by
  change (s.mapFamily (whiskerLeft K α)).lift ⋙ Grothendieck.pre (B ⋙ Grpd.forgetToCat) K = _
  rw [Section.mapFamily_lift]
  exact congrArg (s.lift ⋙ ·) (Grothendieck.pre_comp_map K
    (whiskerRight α Grpd.forgetToCat)).symm

/-- Section-valued contextual elimination commutes with a noninvertible
transformation of its motive. Equality includes the section's arrow action. -/
theorem eliminateSection_mapFamily {E F : Cat.{u,u}} (e : NormalizedEquivalence E F)
    {A B : F ⥤ Grpd.{u,u}} (α : A ⟶ B)
    (d : Section (e.equiv.functor ⋙ A)) :
    (eliminateSection e A d).mapFamily α =
      eliminateSection e B (d.mapFamily (whiskerLeft e.equiv.functor α)) := by
  apply Section.lift_injective
  rw [Section.mapFamily_lift]
  simp only [eliminateSection, Section.ofOver_lift]
  rw [NormalizedEquivalence.eliminate_map]
  congr 1
  exact (pair_mapFamily α e.equiv.functor d).symm

end SquareKit.Internal.PathTransport.GroupoidModel

namespace SquareKit.Internal.PathTransport.GroupoidModel.Instance
open CategoryTheory SquareKit.Internal.PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => structuralModel C B

/-- The existing contextual J, with its actual arbitrary dependent tail,
commutes with a changing motive family. The tail is held fixed in this result. -/
theorem contextualJ_mapFamily {Γ : (M).Context} {n} (A : (M).Family Γ)
    (x : (M).Section Γ A)
    (T : StructuralModel.Telescope M (StructuralModel.pathContext M A x) n)
    {P Q : (show Grpd.{u,u} from StructuralModel.Telescope.total M T) ⥤ Grpd.{u,u}} (α : P ⟶ Q)
    (d : (M).Section
      (StructuralModel.Telescope.total M
        (StructuralModel.Telescope.pullback M T (StructuralModel.rootSub M A x)))
      ((M).subTy P (StructuralModel.rootTail M A x T))) :
    (contextualJ C B A x T P d).down.mapFamily α =
      (contextualJ C B A x T Q
        ⟨d.down.mapFamily (whiskerLeft (StructuralModel.rootTail M A x T).down α)⟩).down :=
  eliminateSection_mapFamily (rootTailEquivalence C B A x.down T) α d.down

end SquareKit.Internal.PathTransport.GroupoidModel.Instance
