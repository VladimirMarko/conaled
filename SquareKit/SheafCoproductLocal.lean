import SquareKit.SheafPushoutLocal
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Sites.LocallyInjective

/-! A sheaf coproduct is locally, rather than globally, a choice of summand. -/
noncomputable section
namespace SquareKit.SheafCoproductLocal
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type (max u v)} (F : I → Sheaf J (Type (max u v)))

abbrev diagram := Discrete.functor F
abbrev rawDiagram := diagram F ⋙ sheafToPresheaf J (Type (max u v))
abbrev raw := colimit (rawDiagram F)
abbrev total := colimit (diagram F)
abbrev inclusion (i : I) : F i ⟶ total F := colimit.ι (diagram F) ⟨i⟩

def sheafifiedIso : (presheafToSheaf J (Type (max u v))).obj (raw F) ≅ total F :=
  (Sheaf.isColimitSheafifyCocone (colimit.cocone (rawDiagram F))
    (colimit.isColimit (rawDiagram F))).coconePointUniqueUpToIso
      (colimit.isColimit (diagram F))

def rawMap : raw F ⟶ (total F).obj :=
  toSheafify J (raw F) ≫ (sheafifiedIso F).hom.hom

instance : Presheaf.IsLocallySurjective J (rawMap F) := by
  dsimp only [rawMap]
  infer_instance

theorem rawMap_inclusion (i : I) :
    colimit.ι (rawDiagram F) ⟨i⟩ ≫ rawMap F = (inclusion F i).hom := by
  have h := (Sheaf.isColimitSheafifyCocone (colimit.cocone (rawDiagram F))
    (colimit.isColimit (rawDiagram F))).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (diagram F)) ⟨i⟩
  have hh := congrArg (fun f => (sheafToPresheaf J (Type (max u v))).map f) h
  change ((Sheaf.sheafifyCocone (colimit.cocone (rawDiagram F))).ι.app ⟨i⟩).hom ≫
    (sheafifiedIso F).hom.hom = _ at hh
  rw [Sheaf.sheafifyCocone_ι_app_val] at hh
  exact (Category.assoc (colimit.ι (rawDiagram F) ⟨i⟩)
    (toSheafify J (raw F)) (sheafifiedIso F).hom.hom).symm.trans hh

theorem rawMap_section {V : C} (a : (raw F).obj (op V)) :
    ∃ i, ∃ b : (F i).obj.obj (op V),
      (rawMap F).app (op V) a = (inclusion F i).hom.app (op V) b := by
  obtain ⟨⟨i⟩, b, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj (op V)) (colimit.isColimit (rawDiagram F))) a
  exact ⟨i, b, ConcreteCategory.congr_hom (NatTrans.congr_app (rawMap_inclusion F i) (op V)) b⟩

/-- Local factorization through a family of actual sheaf maps. -/
def liftSieve {X : Sheaf J (Type (max u v))} (j : ∀ i, F i ⟶ X)
    {V : C} (x : X.obj.obj (op V)) : Sieve V where
  arrows {W} k := ∃ i, ∃ b : (F i).obj.obj (op W), (j i).hom.app (op W) b = X.obj.map k.op x
  downward_closed := by
    intro W Z k hk m
    obtain ⟨i,b,hb⟩ := hk
    refine ⟨i, (F i).obj.map m.op b, ?_⟩
    rw [NatTrans.naturality_apply, hb]
    exact (ConcreteCategory.congr_hom (X.obj.map_comp k.op m.op) x).symm

/-- Every coproduct section is locally in an actual summand. -/
theorem liftSieve_cover {V : C} (x : (total F).obj.obj (op V)) :
    liftSieve F (inclusion F) x ∈ J V := by
  apply J.superset_covering _ (Presheaf.imageSieve_mem J (rawMap F) x)
  intro W k hk
  obtain ⟨a,ha⟩ := hk
  obtain ⟨i,b,hb⟩ := rawMap_section F a
  exact ⟨i,b,hb.symm.trans ha⟩

def desc {X : Sheaf J (Type (max u v))} (j : ∀ i, F i ⟶ X) : total F ⟶ X :=
  colimit.desc (diagram F) (Cofan.mk X j)

@[simp, reassoc] theorem inclusion_desc {X : Sheaf J (Type (max u v))}
    (j : ∀ i, F i ⟶ X) (i : I) : inclusion F i ≫ desc F j = j i :=
  colimit.ι_desc _ _

/-- The admitted chart sieve proves that the coproduct map is a cover. -/
theorem isLocallySurjective_desc {X : Sheaf J (Type (max u v))} (j : ∀ i, F i ⟶ X)
    (cover : ∀ (V : C) (x : X.obj.obj (op V)), liftSieve F j x ∈ J V) :
    Presheaf.IsLocallySurjective J (desc F j).hom where
  imageSieve_mem {V} x := by
    apply J.superset_covering _ (cover V x)
    intro W k hk
    obtain ⟨i,b,hb⟩ := hk
    refine ⟨(inclusion F i).hom.app (op W) b, ?_⟩
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app
      (congrArg (fun f => f.hom) (inclusion_desc F j i)) (op W)) b).trans hb

/-- Equality out of a sheaf coproduct may be checked after decomposing both
sections locally. This is used to descend overlap labels without discarding data. -/
theorem desc_fiber_constant {X N : Sheaf J (Type (max u v))}
    (j : ∀ i, F i ⟶ X) (m : ∀ i, F i ⟶ N)
    (compatible : ∀ (V : C) (i k : I) (x : (F i).obj.obj (op V))
      (y : (F k).obj.obj (op V)),
      (j i).hom.app (op V) x = (j k).hom.app (op V) y →
      (m i).hom.app (op V) x = (m k).hom.app (op V) y)
    (V : C) (x y : (total F).obj.obj (op V))
    (h : (desc F j).hom.app (op V) x = (desc F j).hom.app (op V) y) :
    (desc F m).hom.app (op V) x = (desc F m).hom.app (op V) y := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp N.property)
    (liftSieve F (inclusion F) x ⊓ liftSieve F (inclusion F) y)
    (J.intersection_covering (liftSieve_cover F x) (liftSieve_cover F y))).isSeparatedFor.ext
  intro W f hf
  obtain ⟨⟨i,a,ha⟩,⟨k,b,hb⟩⟩ := hf
  have fac (Z : Sheaf J (Type (max u v))) (n : ∀ i, F i ⟶ Z) (l : I)
      (z : (F l).obj.obj (op W)) :
      (desc F n).hom.app (op W) ((inclusion F l).hom.app (op W) z) = (n l).hom.app (op W) z :=
    congrArg (fun t : F l ⟶ Z => t.hom.app (op W) z) (inclusion_desc F n l)
  have hj : (j i).hom.app (op W) a = (j k).hom.app (op W) b := by
    rw [← fac X j i a, ← fac X j k b, ha, hb,
      NatTrans.naturality_apply, NatTrans.naturality_apply, h]
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, ← ha, ← hb,
    fac N m i a, fac N m k b]
  exact compatible W i k a b hj

/-- Raw summand coordinates retain the index before sheafification. -/
def coordinates : Cᵒᵖ ⥤ Type (max u v) where
  obj V := Σ i, (F i).obj.obj V
  map f := TypeCat.ofHom (fun x => ⟨x.1, (F x.1).obj.map f x.2⟩)
  map_id V := by
    apply ConcreteCategory.hom_ext
    rintro ⟨i,x⟩
    exact congrArg (Sigma.mk i) (ConcreteCategory.congr_hom ((F i).obj.map_id V) x)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨i,x⟩
    exact congrArg (Sigma.mk i) (ConcreteCategory.congr_hom ((F i).obj.map_comp f g) x)

def coordinateInjection (i : I) : (F i).obj ⟶ coordinates F where
  app V := TypeCat.ofHom (fun x => (⟨i,x⟩ : Σ j, (F j).obj.obj V))
  naturality _ _ _ := by apply ConcreteCategory.hom_ext; intro x; rfl

def rawCoordinates : raw F ⟶ coordinates F :=
  colimit.desc (rawDiagram F) {
    pt := coordinates F
    ι := { app i := coordinateInjection F i.as
           naturality := by
             intro ⟨i⟩ ⟨j⟩ f
             have h : i = j := Discrete.eq_of_hom f
             subst j
             have hf : f = 𝟙 _ := Subsingleton.elim _ _
             subst f
             simp } }

theorem rawCoordinates_inclusion (i : I) :
    colimit.ι (rawDiagram F) ⟨i⟩ ≫ rawCoordinates F = coordinateInjection F i :=
  colimit.ι_desc _ _

instance rawMap_isLocallyInjective : Presheaf.IsLocallyInjective J (rawMap F) := by
  dsimp only [rawMap]
  infer_instance

/-- Equality of sheaf coproduct representatives locally identifies their actual
indices and component sections. This also handles an empty covering sieve. -/
theorem inclusion_locally_equal {V : C} (i j : I)
    (x : (F i).obj.obj (op V)) (y : (F j).obj.obj (op V))
    (h : (inclusion F i).hom.app (op V) x = (inclusion F j).hom.app (op V) y) :
    Presheaf.equalizerSieve (F := coordinates F) ⟨i,x⟩ ⟨j,y⟩ ∈ J V := by
  let a := (colimit.ι (rawDiagram F) ⟨i⟩).app (op V) x
  let b := (colimit.ι (rawDiagram F) ⟨j⟩).app (op V) y
  have ha : (rawMap F).app (op V) a = (inclusion F i).hom.app (op V) x :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (rawMap_inclusion F i) (op V)) x
  have hb : (rawMap F).app (op V) b = (inclusion F j).hom.app (op V) y :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (rawMap_inclusion F j) (op V)) y
  apply J.superset_covering _ (Presheaf.equalizerSieve_mem J (rawMap F) a b (ha.trans (h.trans hb.symm)))
  intro W k hk
  have eq := congrArg ((rawCoordinates F).app (op W)) hk
  have ca : (rawCoordinates F).app (op V) a = ⟨i,x⟩ :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (rawCoordinates_inclusion F i) (op V)) x
  have cb : (rawCoordinates F).app (op V) b = ⟨j,y⟩ :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (rawCoordinates_inclusion F j) (op V)) y
  change (rawCoordinates F).app (op W) ((raw F).map k.op a) =
    (rawCoordinates F).app (op W) ((raw F).map k.op b) at eq
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ca, cb] at eq
  exact eq

end SquareKit.SheafCoproductLocal
