import SquareKit.Internal.PathTransport.VerticalFiber

/-! Fiber components extracted from a selected vertical comparison of total
maps. The base functor may be nonfaithful. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory CategoryTheory.Functor
open Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Grpd.{u,u}} (F : C ⥤ D)
variable {A : C ⥤ Grpd.{u,u}} {B : D ⥤ Grpd.{u,u}}

theorem inclusion_totalMap (α : A ⟶ F ⋙ B) (c : C) :
    Grothendieck.ι (A ⋙ Grpd.forgetToCat) c ⋙ totalMap F α =
      (α.app c : A.obj c ⥤ B.obj (F.obj c)) ⋙
        Grothendieck.ι (B ⋙ Grpd.forgetToCat) (F.obj c) := by
  fapply CategoryTheory.Functor.ext
  · intro x; rfl
  · intro x y f
    fapply Grothendieck.ext
    · simp [totalMap, Grothendieck.ι]
    · simp [totalMap, Grothendieck.ι, Grothendieck.map, eqToHom_map,
        Grpd.forgetToCat, Category.assoc]
      have hi := NatIso.naturality_2 (eqToIso (B.map_id (F.obj c))) ((α.app c).map f)
      simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, Grpd.id_eq_id,
        Functor.id_map] at hi
      rw [← hi]
      simp

structure TotalFamilyModification (α β : A ⟶ F ⋙ B) where
  total : totalMap F α ≅ totalMap F β
  base : ∀ x, (total.hom.app x).base = 𝟙 (F.obj x.base)

namespace TotalFamilyModification
variable {F} {α β : A ⟶ F ⋙ B}

def atFiber (m : TotalFamilyModification F α β) (c : C) :
    (α.app c : A.obj c ⥤ B.obj (F.obj c)) ⋙ Grothendieck.ι (B ⋙ Grpd.forgetToCat) (F.obj c) ≅
      (β.app c : A.obj c ⥤ B.obj (F.obj c)) ⋙ Grothendieck.ι (B ⋙ Grpd.forgetToCat) (F.obj c) :=
  (eqToIso (inclusion_totalMap F α c)).symm ≪≫
    isoWhiskerLeft (Grothendieck.ι (A ⋙ Grpd.forgetToCat) c) m.total ≪≫
      eqToIso (inclusion_totalMap F β c)

theorem atFiber_base (m : TotalFamilyModification F α β) (c : C) (x : A.obj c) :
    ((m.atFiber c).hom.app x).base = 𝟙 (F.obj c) := by
  simpa [atFiber] using m.base ⟨c, x⟩

def component (m : TotalFamilyModification F α β) (c : C) :
    (show A.obj c ⥤ B.obj (F.obj c) from α.app c) ≅ β.app c :=
  verticalFiberIso B (m.atFiber c) (m.atFiber_base c)

theorem component_inclusion (m : TotalFamilyModification F α β) (c : C) :
    isoWhiskerRight (m.component c) (Grothendieck.ι (B ⋙ Grpd.forgetToCat) (F.obj c)) =
      m.atFiber c := verticalFiberIso_inclusion B _ _

theorem component_total (m : TotalFamilyModification F α β) (c : C) (x : A.obj c) :
    (Grothendieck.ι (B ⋙ Grpd.forgetToCat) (F.obj c)).map ((m.component c).hom.app x) =
      m.total.hom.app ⟨c, x⟩ := by
  have hh := congrArg (fun e => e.hom.app x) (m.component_inclusion c)
  simpa [atFiber] using hh

private theorem fiber_congr {X Y : Extend B} {f g : X ⟶ Y} (h : f = g) :
    eqToHom (congrArg (fun k => (B.map k).obj X.fiber)
      (congrArg Grothendieck.Hom.base h).symm) ≫ f.fiber = g.fiber := by
  cases h
  simp

theorem component_naturality (m : TotalFamilyModification F α β) {c d : C} (f : c ⟶ d) :
    isoWhiskerLeft (A.map f) (m.component d) ≪≫ eqToIso (familyMap_naturality β f) =
      eqToIso (familyMap_naturality α f) ≪≫
        isoWhiskerRight (m.component c) (B.map (F.map f)) := by
  ext x
  have hn := m.total.hom.naturality (Grothendieck.toTransport
    (F := A ⋙ Grpd.forgetToCat) ⟨c, x⟩ f)
  change _ ≫ m.total.hom.app ⟨d, (A.map f).obj x⟩ = _ at hn
  rw [← m.component_total d ((A.map f).obj x), ← m.component_total c x] at hn
  have hf := fiber_congr hn
  simp [totalMap, Grothendieck.toTransport, Grothendieck.map, Grothendieck.ι,
    Grpd.forgetToCat, eqToHom_map, Category.assoc] at hf
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, eqToIso.hom, eqToHom_app]
  have hh := congrArg (fun k =>
    eqToHom (show (α.app d).obj ((A.map f).obj x) =
      (B.map (𝟙 (F.obj c) ≫ F.map f)).obj ((α.app c).obj x) from by
        simpa using congrArg (fun K => K.obj x) (familyMap_naturality α f)) ≫ k ≫
      eqToHom (congrArg (fun K => K.obj x) (familyMap_naturality β f))) hf
  simpa [Category.assoc] using hh

/-- Actual-arrow naturality of the extracted components is forced by the
natural isomorphism of total maps, even when the base functor is nonfaithful. -/
def modification (m : TotalFamilyModification F α β) : FamilyModification α β where
  app := m.component
  naturality := m.component_naturality

/-- Rebuilding the total comparison recovers the selected original arrows. -/
theorem modification_total (m : TotalFamilyModification F α β) :
    isoWhiskerRight (FamilyModification.totalIso m.modification)
      (Grothendieck.pre (B ⋙ Grpd.forgetToCat) F) = m.total := by
  ext x
  trans (Grothendieck.ι (B ⋙ Grpd.forgetToCat) (F.obj x.base)).map
    ((m.component x.base).hom.app x.fiber)
  · fapply Grothendieck.ext
    · simp [FamilyModification.totalIso, FamilyModification.totalComponent]
    · simp [FamilyModification.totalIso, FamilyModification.totalComponent,
        Grothendieck.ι, modification]
  · exact m.component_total x.base x.fiber

end TotalFamilyModification
end SquareKit.Internal.PathTransport.GroupoidModel
