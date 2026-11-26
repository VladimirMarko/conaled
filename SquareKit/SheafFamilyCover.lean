import SquareKit.SheafCover
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-! Joint local lifting and categorical coproduct covers of sheaves. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SheafFamilyCover
open CategoryTheory Limits Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type (max u v)} {X : Sheaf J (Type (max u v))}
variable {Y : I → Sheaf J (Type (max u v))} (f : ∀ i, Y i ⟶ X)

/-- Restrictions of a section which lift through some member of the family. -/
def imageSieve {U : C} (x : X.obj.obj (op U)) : Sieve U where
  arrows V k := ∃ i, ∃ y : (Y i).obj.obj (op V), (f i).hom.app _ y = X.obj.map k.op x
  downward_closed := by
    rintro V W k ⟨i, y, hy⟩ l
    refine ⟨i, (Y i).obj.map l.op y, ?_⟩
    rw [NatTrans.naturality_apply, hy, op_comp, X.obj.map_comp]
    rfl

/-- Every target section locally lifts through some family member. -/
def JointlyLocallySurjective : Prop :=
  ∀ ⦃U : C⦄ (x : X.obj.obj (op U)), imageSieve f x ∈ J U

/-- The intermediate coproduct is in presheaves, not asserted to be a sheaf. -/
def presheafCocone (Y : I → Sheaf J (Type (max u v))) :
    Cocone (Discrete.functor Y ⋙ sheafToPresheaf J (Type (max u v))) :=
  (Cocone.precompose (Discrete.compNatIsoDiscrete Y (sheafToPresheaf J _)).hom).obj
    (colimit.cocone (Discrete.functor (fun i => (Y i).obj)))

def presheafIsColimit (Y : I → Sheaf J (Type (max u v))) :
    IsColimit (presheafCocone Y) :=
  (IsColimit.precomposeHomEquiv (Discrete.compNatIsoDiscrete Y (sheafToPresheaf J _)) _).symm
    (colimit.isColimit _)

/-- Sheafification constructs an actual categorical coproduct cocone. -/
def coproductCocone (Y : I → Sheaf J (Type (max u v))) : Cocone (Discrete.functor Y) :=
  Sheaf.sheafifyCocone (presheafCocone Y)

def coproductIsColimit (Y : I → Sheaf J (Type (max u v))) :
    IsColimit (coproductCocone Y) :=
  Sheaf.isColimitSheafifyCocone _ (presheafIsColimit Y)

/-- Comparison with Mathlib's chosen categorical coproduct of sheaves. -/
def coproductIso (Y : I → Sheaf J (Type (max u v))) : (coproductCocone Y).pt ≅ ∐ Y :=
  (coproductIsColimit Y).coconePointUniqueUpToIso (coproductIsCoproduct Y)

/-- The induced map on the constructed sheaf coproduct. -/
def aggregate : (coproductCocone Y).pt ⟶ X :=
  (coproductIsColimit Y).desc (Cofan.mk X f)

lemma unit_aggregate :
    toSheafify J (presheafCocone Y).pt ≫ (aggregate f).hom =
      Sigma.desc (fun i => (f i).hom) := by
  apply Sigma.hom_ext
  intro i
  have h := congrArg (fun k => k.hom) ((coproductIsColimit Y).fac (Cofan.mk X f) ⟨i⟩)
  unfold coproductCocone at h
  rw [ObjectProperty.FullSubcategory.comp_hom, Sheaf.sheafifyCocone_ι_app_val] at h
  change (Sigma.ι (fun i => (Y i).obj) i ≫ toSheafify J (presheafCocone Y).pt) ≫
    (aggregate f).hom = (f i).hom at h
  simpa only [Category.assoc, Sigma.ι_comp_desc] using h

lemma imageSieve_presheaf_desc {U : C} (x : X.obj.obj (op U)) :
    Presheaf.imageSieve (Sigma.desc (fun i => (f i).hom)) x = imageSieve f x := by
  ext V k
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨⟨i⟩, z, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation _ _).obj (op V))
        (coproductIsCoproduct (fun i => (Y i).obj))) y
    refine ⟨i, z, ?_⟩
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (Sigma.ι_comp_desc (fun i => (f i).hom) i) (op V)) z
    exact h.symm.trans hy
  · rintro ⟨i, y, hy⟩
    refine ⟨(Sigma.ι (fun i => (Y i).obj) i).app _ y, ?_⟩
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (Sigma.ι_comp_desc (fun i => (f i).hom) i) (op V)) y
    exact h.trans hy

theorem jointlyLocallySurjective_iff_aggregate :
    JointlyLocallySurjective f ↔ Presheaf.IsLocallySurjective J (aggregate f).hom := by
  rw [← Presheaf.isLocallySurjective_iff_of_fac J (unit_aggregate f)]
  constructor
  · intro h
    exact ⟨fun x => (imageSieve_presheaf_desc f x).symm ▸ h x⟩
  · intro h U x
    rw [← imageSieve_presheaf_desc]
    exact Presheaf.imageSieve_mem J (Sigma.desc (fun i => (f i).hom)) x

theorem aggregate_comparison :
    (coproductIso Y).hom ≫ Sigma.desc f = aggregate f :=
  (coproductIsColimit Y).coconePointUniqueUpToIso_hom_desc (coproductIsCoproduct Y)

/-- The comparison also holds for Mathlib's chosen sheaf coproduct map. -/
theorem jointlyLocallySurjective_iff_isLocallySurjective_desc :
    JointlyLocallySurjective f ↔ Presheaf.IsLocallySurjective J (Sigma.desc f).hom := by
  rw [jointlyLocallySurjective_iff_aggregate]
  exact Presheaf.isLocallySurjective_iff_of_fac J
    (congrArg (fun k => k.hom) (aggregate_comparison f))

/-- The actual map of categorical coproducts induced by a family refinement. -/
def refinementMap {K : Type (max u v)} {Z : K → Sheaf J (Type (max u v))}
    (r : K → I) (a : ∀ k, Z k ⟶ Y (r k)) : (∐ Z) ⟶ ∐ Y :=
  Sigma.desc (fun k => a k ≫ Sigma.ι Y (r k))

theorem refinementMap_aggregate {K : Type (max u v)} {Z : K → Sheaf J (Type (max u v))}
    (g : ∀ k, Z k ⟶ X) (r : K → I) (a : ∀ k, Z k ⟶ Y (r k))
    (fac : ∀ k, a k ≫ f (r k) = g k) :
    refinementMap r a ≫ Sigma.desc f = Sigma.desc g := by
  apply Sigma.hom_ext
  intro k
  simp [refinementMap, Category.assoc, fac]

/-- A covering refinement makes the original family cover. -/
theorem of_refinement {K : Type (max u v)} {Z : K → Sheaf J (Type (max u v))}
    (g : ∀ k, Z k ⟶ X) (r : K → I) (a : ∀ k, Z k ⟶ Y (r k))
    (fac : ∀ k, a k ≫ f (r k) = g k) (hg : JointlyLocallySurjective g) :
    JointlyLocallySurjective f := by
  intro U x
  apply J.superset_covering _ (hg x)
  rintro V k ⟨i, z, hz⟩
  refine ⟨r i, (a i).hom.app _ z, ?_⟩
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun t => t.hom) (fac i)) (op V)) z
  exact h.trans hz

/-- A singleton joint cover is exactly an ordinary locally surjective map. -/
theorem singleton_iff {Y : Sheaf J (Type (max u v))} (g : Y ⟶ X) :
    JointlyLocallySurjective (fun _ : PUnit => g) ↔ Presheaf.IsLocallySurjective J g.hom := by
  have he (U : C) (x : X.obj.obj (op U)) :
      imageSieve (fun _ : PUnit => g) x = Presheaf.imageSieve g.hom x := by
    ext V k
    exact ⟨fun ⟨_, y, h⟩ => ⟨y, h⟩, fun ⟨y, h⟩ => ⟨PUnit.unit, y, h⟩⟩
  constructor
  · intro h
    exact ⟨fun {U} x => he U x ▸ h x⟩
  · intro h U x
    rw [he]
    exact Presheaf.imageSieve_mem J g.hom x

/-- An empty family covers precisely where every existing target section admits
an empty covering sieve. This includes sites with empty covers. -/
theorem empty_iff [IsEmpty I] :
    JointlyLocallySurjective f ↔ ∀ ⦃U : C⦄ (_ : X.obj.obj (op U)), (⊥ : Sieve U) ∈ J U := by
  have he (U : C) (x : X.obj.obj (op U)) : imageSieve f x = ⊥ := by
    ext V k
    exact ⟨fun ⟨i, _, _⟩ => isEmptyElim i, False.elim⟩
  simp only [JointlyLocallySurjective, he]

/-- The split-family realization of the actual pullback of every member. -/
def pullbackFamily {Z : Sheaf J (Type (max u v))} (g : Z ⟶ X) (i : I) : SplitSheaf.Ty Z :=
  SplitSheaf.tySub (SplitSheaf.ofDisplay (f i)) g

abbrev pullbackMaps {Z : Sheaf J (Type (max u v))} (g : Z ⟶ X) :
    ∀ i, SplitSheaf.extension (pullbackFamily f g i) ⟶ Z :=
  fun i => SplitSheaf.p (pullbackFamily f g i)

/-- Each selected member is an actual pullback of the original map. -/
theorem pullback_square {Z : Sheaf J (Type (max u v))} (g : Z ⟶ X) (i : I) :
    IsPullback (SplitSheaf.lift (SplitSheaf.ofDisplay (f i)) g ≫
      (SplitSheaf.displayIso (f i)).hom) (pullbackMaps f g i) (f i) g := by
  apply (SplitSheaf.extension_pullback (SplitSheaf.ofDisplay (f i)) g).of_iso
    (Iso.refl _) (SplitSheaf.displayIso (f i)) (Iso.refl _) (Iso.refl _)
  · simp
  · simp [pullbackMaps, pullbackFamily]
  · simp [SplitSheaf.displayIso_projection]
  · simp

/-- Joint local lifting is stable under arbitrary change of context. -/
theorem jointlyLocallySurjective_pullbackMaps (hf : JointlyLocallySurjective f)
    {Z : Sheaf J (Type (max u v))} (g : Z ⟶ X) :
    JointlyLocallySurjective (pullbackMaps f g) := by
  intro U z
  apply J.superset_covering _ (hf (g.hom.app _ z))
  rintro V k ⟨i, y, hy⟩
  refine ⟨i, ⟨Z.obj.map k.op z, ⟨y, ?_⟩⟩, rfl⟩
  exact hy.trans (NatTrans.naturality_apply g.hom k.op z).symm

end SquareKit.SheafFamilyCover
