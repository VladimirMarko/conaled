import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! Local chart lifting for arbitrary pushouts of type-valued sheaves. -/
noncomputable section
namespace SquareKit.SheafPushoutLocal
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {U L R : Sheaf J (Type (max u v))} (f : U ⟶ L) (g : U ⟶ R)

abbrev rawDiagram := span f g ⋙ sheafToPresheaf J (Type (max u v))
abbrev rawPushout := colimit (rawDiagram f g)

def sheafifiedIso : (presheafToSheaf J (Type (max u v))).obj (rawPushout f g) ≅ pushout f g :=
  (Sheaf.isColimitSheafifyCocone (colimit.cocone (rawDiagram f g))
    (colimit.isColimit (rawDiagram f g))).coconePointUniqueUpToIso
      (colimit.isColimit (span f g))

def rawMap : rawPushout f g ⟶ (pushout f g).obj :=
  toSheafify J (rawPushout f g) ≫ (sheafifiedIso f g).hom.hom

instance : Presheaf.IsLocallySurjective J (rawMap f g) := by
  dsimp only [rawMap]
  infer_instance

theorem rawMap_ι (j : WalkingSpan) :
    colimit.ι (rawDiagram f g) j ≫ rawMap f g = (colimit.ι (span f g) j).hom := by
  have h := (Sheaf.isColimitSheafifyCocone (colimit.cocone (rawDiagram f g))
    (colimit.isColimit (rawDiagram f g))).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (span f g)) j
  have hh := congrArg (fun f => (sheafToPresheaf J (Type (max u v))).map f) h
  change ((Sheaf.sheafifyCocone (colimit.cocone (rawDiagram f g))).ι.app j).hom ≫
    (sheafifiedIso f g).hom.hom = _ at hh
  rw [Sheaf.sheafifyCocone_ι_app_val] at hh
  exact (Category.assoc (colimit.ι (rawDiagram f g) j)
    (toSheafify J (rawPushout f g)) (sheafifiedIso f g).hom.hom).symm.trans hh

/-- A raw presheaf-colimit section comes from one of the two chart vertices. -/
theorem rawMap_chart {V : C} (a : (rawPushout f g).obj (op V)) :
    (∃ l : L.obj.obj (op V), (rawMap f g).app (op V) a = (pushout.inl f g).hom.app (op V) l) ∨
    (∃ r : R.obj.obj (op V), (rawMap f g).app (op V) a = (pushout.inr f g).hom.app (op V) r) := by
  obtain ⟨j, b, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj (op V)) (colimit.isColimit (rawDiagram f g))) a
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (rawMap_ι f g j) (op V)) b
  cases j with
  | some j =>
    cases j with
    | left => exact Or.inl ⟨b, h⟩
    | right => exact Or.inr ⟨b, h⟩
  | none =>
    refine Or.inl ⟨f.hom.app (op V) b, h.trans ?_⟩
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun f => (sheafToPresheaf J (Type (max u v))).map f)
        (colimit.w (span f g) WalkingSpan.Hom.fst)) (op V)) b).symm

/-- The sieve of arrows along which a section lifts to either chart. -/
def chartSieve {V : C} (x : (pushout f g).obj.obj (op V)) : Sieve V where
  arrows {W} k :=
    (∃ l : L.obj.obj (op W), (pushout.inl f g).hom.app (op W) l = (pushout f g).obj.map k.op x) ∨
    (∃ r : R.obj.obj (op W), (pushout.inr f g).hom.app (op W) r = (pushout f g).obj.map k.op x)
  downward_closed := by
    intro W Z k hk m
    rcases hk with ⟨l, hl⟩ | ⟨r, hr⟩
    · left
      refine ⟨L.obj.map m.op l, ?_⟩
      rw [NatTrans.naturality_apply, hl]
      exact (ConcreteCategory.congr_hom ((pushout f g).obj.map_comp k.op m.op) x).symm
    · right
      refine ⟨R.obj.map m.op r, ?_⟩
      rw [NatTrans.naturality_apply, hr]
      exact (ConcreteCategory.congr_hom ((pushout f g).obj.map_comp k.op m.op) x).symm

/-- Every section of the sheaf pushout locally lifts to one chart. -/
theorem chartSieve_cover {V : C} (x : (pushout f g).obj.obj (op V)) :
    chartSieve f g x ∈ J V := by
  apply J.superset_covering _ (Presheaf.imageSieve_mem J (rawMap f g) x)
  intro W k hk
  obtain ⟨a, ha⟩ := hk
  rcases rawMap_chart f g a with ⟨l, hl⟩ | ⟨r, hr⟩
  · exact Or.inl ⟨l, hl.symm.trans ha⟩
  · exact Or.inr ⟨r, hr.symm.trans ha⟩

end SquareKit.SheafPushoutLocal
