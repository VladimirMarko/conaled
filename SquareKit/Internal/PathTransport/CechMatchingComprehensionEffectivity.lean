import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberArrow
import SquareKit.Internal.PathTransport.GrothendieckVertical
import SquareKit.Internal.PathTransport.GroupoidFiberFull
import SquareKit.Internal.PathTransport.GroupoidFiberEssential

/-! Fiberwise equivalences detect equivalence of the actual total functor. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension.Effectivity
open CategoryTheory
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D : StrictDiagram.{u,u}} (A : FamilyData D) (h : A.Coherence)
variable {C : Grpd.{u,u}} (F : C ⥤ Grpd.{u,u})
local instance : Groupoid (Extend F) := Groupoid.ofIsGroupoid
variable (E : Extend F ⥤ Datum (A.total h).toDiagram) (R : C ⥤ Datum D.toDiagram)
variable (square : E ⋙ (A.projection h).functor =
  Grothendieck.forget (F ⋙ Grpd.forgetToCat) ⋙ R)

include square in
theorem fiberProjection (c : C) :
    (Grothendieck.ι (F ⋙ Grpd.forgetToCat) c ⋙ E) ⋙ (A.projection h).functor =
      (Functor.const (F.obj c)).obj (R.obj c) := by
  rw [Functor.assoc, square]
  exact inclusion_forget_comp F R c

def fiber (c : C) : F.obj c ⥤ Fiber A h (R.obj c) :=
  fixedBaseFunctor A h (Grothendieck.ι (F ⋙ Grpd.forgetToCat) c ⋙ E) (R.obj c)
    (fiberProjection A h F E R square c)

def comparison (c : C) : fiber A h F E R square c ⋙ Fiber.forget ≅
    Grothendieck.ι (F ⋙ Grpd.forgetToCat) c ⋙ E :=
  fixedBaseComparison A h _ _ _

theorem faithful [R.Faithful]
    (fibers : ∀ c, (fiber A h F E R square c).Faithful) : E.Faithful := by
  apply GroupoidFiberFaithful.faithful_of_vertical_kernel E
    (Grothendieck.forget (F ⋙ Grpd.forgetToCat)) (A.projection h).functor R square
  intro x f hb hf
  rcases x with ⟨c,x⟩
  have := fibers c
  let : (Grothendieck.ι (F ⋙ Grpd.forgetToCat) c ⋙ E).Faithful :=
    Functor.Faithful.of_iso (comparison A h F E R square c)
  let g := GrothendieckVertical.arrow (F ⋙ Grpd.forgetToCat) f hb
  have hg : (Grothendieck.ι (F ⋙ Grpd.forgetToCat) c).map g = f :=
    GrothendieckVertical.inclusion_arrow _ f hb
  have hi : g = 𝟙 x := (Grothendieck.ι (F ⋙ Grpd.forgetToCat) c ⋙ E).map_injective (by
    change E.map ((Grothendieck.ι (F ⋙ Grpd.forgetToCat) c).map g) = _
    rw [hg, hf]
    simp only [Functor.comp_map, CategoryTheory.Functor.map_id]
    rfl)
  rw [← hg, hi, CategoryTheory.Functor.map_id]
  rfl

theorem full [R.Full]
    (fibers : ∀ c, (fiber A h F E R square c).Full) : E.Full := by
  apply GroupoidFiberFull.full_of_vertical E
    (Grothendieck.forget (F ⋙ Grpd.forgetToCat)) (A.projection h).functor R square
    (GrothendieckProjectionLifts.lift_base (F ⋙ Grpd.forgetToCat))
  intro x y hb p hp
  rcases x with ⟨c,x⟩
  rcases y with ⟨d,y⟩
  change c = d at hb
  subst d
  have := fibers c
  have hp' : (A.projection h).functor.map p ≫
      eqToHom (Functor.congr_obj (fiberProjection A h F E R square c) y) =
      eqToHom (Functor.congr_obj (fiberProjection A h F E R square c) x) := by
    simp only [eqToIso.hom, eqToHom_app, eqToHom_refl] at hp
    change (A.projection h).functor.map p ≫ eqToHom _ = eqToHom _ ≫ R.map (𝟙 c) at hp
    rw [R.map_id] at hp
    exact hp.trans (Category.comp_id _)
  let q : (fiber A h F E R square c).obj x ⟶ (fiber A h F E R square c).obj y :=
    ofDatumArrow _ _ p hp'
  obtain ⟨g,hg⟩ := (fiber A h F E R square c).map_surjective q
  refine ⟨(Grothendieck.ι (F ⋙ Grpd.forgetToCat) c).map g, ?_⟩
  have hm := congrArg (fun f => f.matchingArrow) hg
  change eqToHom _ ≫ E.map ((Grothendieck.ι (F ⋙ Grpd.forgetToCat) c).map g) ≫
    eqToHom _ = eqToHom _ ≫ p ≫ eqToHom _ at hm
  simpa only [Category.assoc, cancel_epi, cancel_mono] using hm

theorem essSurj [R.EssSurj]
    (fibers : ∀ c, (fiber A h F E R square c).EssSurj) : E.EssSurj := by
  apply GroupoidFiberEssential.essSurj_of_fibers E (A.projection h).functor R
  · intro y c hi
    obtain ⟨i⟩ := hi
    let z := Fiber.ofDatum y rfl
    let t := Fiber.transport i.hom z
    refine ⟨t.datum, Fiber.projection_datum t, ?_⟩
    exact ⟨(eqToIso (Fiber.datum_ofDatum y rfl)).symm ≪≫ asIso (Fiber.lift i.hom z)⟩
  · intro c z hz
    have := fibers c
    obtain ⟨x, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (fiber A h F E R square c)
      (Fiber.ofDatum z hz)
    refine ⟨⟨c,x⟩, ?_⟩
    exact ⟨((comparison A h F E R square c).app x).symm ≪≫ Fiber.forget.mapIso i ≪≫
      eqToIso (Fiber.datum_ofDatum z hz)⟩

theorem isEquivalence [R.IsEquivalence]
    (fibers : ∀ c, (fiber A h F E R square c).IsEquivalence) : E.IsEquivalence := by
  have := faithful A h F E R square (fun c => (fibers c).faithful)
  have := full A h F E R square (fun c => (fibers c).full)
  have := essSurj A h F E R square (fun c => (fibers c).essSurj)
  constructor <;> infer_instance

end SquareKit.Internal.PathTransport.CechMatching.Comprehension.Effectivity
