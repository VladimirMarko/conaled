import SquareKit.Internal.CoherentFamilyClassification
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import SquareKit.Internal.CoherentRepresentableCoding
import SquareKit.SheafSlice
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Equivalence

/-! Coherent local diagrams with sheaf conditions on their rooted views. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.CoherentSheafOver
open CategoryTheory Opposite
universe u v w
variable {B : Type u} [Category.{v} B]

/-- A section over an arrow is a local view rooted at its codomain. -/
def rootView (X : B) : (Over X)ᵒᵖ ⥤ Arrow Bᵒᵖ where
  obj Y := Arrow.mk Y.unop.hom.op
  map f := Arrow.homMk (𝟙 _) f.unop.left.op (by
    rw [Category.id_comp]
    exact congrArg Quiver.Hom.op (Over.w f.unop).symm)
  map_id Y := by apply Arrow.hom_ext <;> simp
  map_comp f g := by apply Arrow.hom_ext <;> simp

/-- Membership is checked on each local presheaf before assembly. -/
def Local (J : GrothendieckTopology B) :
    ObjectProperty (CoherentFamilyClassification.Code Bᵒᵖ (Type w)) :=
  fun A => ∀ X : B, Presheaf.IsSheaf (J.over X) (rootView X ⋙ A.obj)

abbrev Code (J : GrothendieckTopology B) := (Local.{u,v,w} J).FullSubcategory

/-- Sheafness can be tested on all slice sites. -/
theorem isSheaf_of_over (J : GrothendieckTopology B) (P : Bᵒᵖ ⥤ Type w)
    (h : ∀ X, Presieve.IsSheaf (J.over X) ((Over.forget X).op ⋙ P)) :
    Presieve.IsSheaf J P := by
  intro X R hR x hx
  let T : Over X := Over.mk (𝟙 X)
  let S : Sieve T := (Sieve.overEquiv T).symm R
  let y : Presieve.FamilyOfElements ((Over.forget X).op ⋙ P) S.arrows :=
    fun Y f hf => x f.left hf
  have hy : y.Compatible := by
    intro Y Z W f g a b ha hb hab
    exact hx f.left g.left ha hb (congrArg (fun k => k.left) hab)
  obtain ⟨t, ht, hut⟩ := h X S (by
    rw [GrothendieckTopology.mem_over_iff]
    simpa only [S, OrderIso.apply_symm_apply, T, Over.mk_left] using hR) y hy
  refine ⟨t, ?_, ?_⟩
  · intro Y f hf
    exact ht (Over.homMk f (V := T) (U := Over.mk f) (by simp [T])) hf
  · intro t' ht'
    apply hut t'
    intro Y f hf
    exact ht' f.left hf

/-- Coherent restriction comparisons identify each local sheaf with the
restriction of the evaluated presheaf. -/
noncomputable def rootRecovery
    (A : CoherentFamilyClassification.Code Bᵒᵖ (Type w)) (X : B) :
    rootView X ⋙ A.obj ≅ (Over.forget X).op ⋙
      (CoherentFamilyClassification.decode Bᵒᵖ (Type w)).obj A :=
  Functor.isoWhiskerLeft (rootView X)
    (CoherentFamilyClassification.recovery Bᵒᵖ (Type w) A)

/-- The decoder's sheaf condition follows from the local sheaf conditions. -/
theorem decoded_isSheaf (J : GrothendieckTopology B) (A : Code.{u,v,w} J) :
    Presheaf.IsSheaf J
      ((CoherentFamilyClassification.decode Bᵒᵖ (Type w)).obj A.obj) := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply isSheaf_of_over
  intro X
  rw [← isSheaf_iff_isSheaf_of_type]
  exact (Presheaf.isSheaf_of_iso_iff (rootRecovery A.obj X)).1 (A.property X)

/-- Evaluation builds the sheaf and retains every natural transformation. -/
def decode (J : GrothendieckTopology B) : Code.{u,v,w} J ⥤ Sheaf J (Type w) where
  obj A := ⟨(CoherentFamilyClassification.decode Bᵒᵖ (Type w)).obj A.obj,
    decoded_isSheaf J A⟩
  map f := ⟨(CoherentFamilyClassification.decode Bᵒᵖ (Type w)).map f.hom⟩

/-- Restrict an actual sheaf to its local diagrams. -/
def encode (J : GrothendieckTopology B) : Sheaf J (Type w) ⥤ Code.{u,v,w} J where
  obj A := ⟨(CoherentFamilyClassification.code Bᵒᵖ (Type w)).obj A.obj,
    fun X => ((J.overPullback (Type w) X).obj A).property⟩
  map f := ObjectProperty.homMk
    ((CoherentFamilyClassification.code Bᵒᵖ (Type w)).map f.hom)

/-- Recovery is natural in arbitrary code maps. -/
noncomputable def recoveryIso (J : GrothendieckTopology B) :
    𝟭 (Code.{u,v,w} J) ≅ decode J ⋙ encode J :=
  NatIso.ofComponents (fun A => (Local J).isoMk
    ((CoherentFamilyClassification.recoveryIso Bᵒᵖ (Type w)).app A.obj)) (by
      intro A B f
      apply ObjectProperty.hom_ext
      exact (CoherentFamilyClassification.recoveryIso _ _).hom.naturality f.hom)

/-- Local sheaf diagrams classify sheaves, with no assumed assembled sheafness. -/
noncomputable def classification (J : GrothendieckTopology B) :
    Code.{u,v,w} J ≌ Sheaf J (Type w) :=
  CategoryTheory.Equivalence.mk (decode J) (encode J) (recoveryIso J) (Iso.refl _)

section Dense
universe a b
variable {D : Type a} [Category.{b} D] (G : B ⥤ D)
variable (J : GrothendieckTopology D) (Γ : D)

/-- Represented domains over the specified context, with their actual triangles. -/
abbrev LocalSite := CostructuredArrow G Γ

/-- The topology is induced from the existing sheaf-over fiber. -/
def localTopology : GrothendieckTopology (LocalSite G Γ) :=
  (CostructuredArrow.toOver G Γ).inducedTopology (J.over Γ)

abbrev LocalCode := Code.{_,_,w} (localTopology G J Γ)

variable [G.Full] [G.Faithful]
variable [(CostructuredArrow.toOver G Γ).IsCoverDense (J.over Γ)]
variable [∀ X : (Over Γ)ᵒᵖ,
  Limits.HasLimitsOfShape (StructuredArrow X (CostructuredArrow.toOver G Γ).op) (Type w)]

/-- Cover density, rather than subcanonicity alone, justifies descent from
represented domains to the whole sheaf-over fiber. -/
noncomputable def sheafOverClassification :
    LocalCode.{u,v,w} G J Γ ≌ Sheaf (J.over Γ) (Type w) :=
  (classification (localTopology G J Γ)).trans
    ((CostructuredArrow.toOver G Γ).sheafInducedTopologyEquivOfIsCoverDense
      (J.over Γ) (Type w))

/-- Recovery identifies the actual restrictions on represented domains,
including their section maps, with the independently decoded local family. -/
noncomputable def decodedLocalRecovery (A : LocalCode.{u,v,w} G J Γ) :
    (CostructuredArrow.toOver G Γ).op ⋙
        ((sheafOverClassification G J Γ).functor.obj A).obj ≅
      ((decode (localTopology G J Γ)).obj A).obj :=
  (sheafToPresheaf (localTopology G J Γ) (Type w)).mapIso
    (((CostructuredArrow.toOver G Γ).sheafInducedTopologyEquivOfIsCoverDense
      (J.over Γ) (Type w)).unitIso.app ((decode (localTopology G J Γ)).obj A)).symm

noncomputable def rootedLocalRecovery (A : LocalCode.{u,v,w} G J Γ)
    (X : LocalSite G Γ) :
    rootView X ⋙ A.obj.obj ≅
      (Over.forget X).op ⋙ (CostructuredArrow.toOver G Γ).op ⋙
        ((sheafOverClassification G J Γ).functor.obj A).obj :=
  rootRecovery A.obj X ≪≫
    Functor.isoWhiskerLeft (Over.forget X).op (decodedLocalRecovery G J Γ A).symm

end Dense

section Contexts
open RepresentableClassification
variable {C : Type u} [Category.{v} C]

/-- The old represented contexts are the universe-lifted Yoneda embedding. -/
theorem representables_eq_uliftYoneda :
    representables.{w} (C := C) = uliftYoneda.{w} := rfl

instance : (representables.{w} (C := C)).Full := by
  rw [representables_eq_uliftYoneda]
  infer_instance

instance : (representables.{w} (C := C)).Faithful := by
  rw [representables_eq_uliftYoneda]
  infer_instance

/-- A covering sieve contains every represented generalized element. This is
the pointwise-surjective topology on the presheaf context category. -/
def representedTopology : GrothendieckTopology (Context.{w} C) where
  sieves Γ := {S | ∀ x : Γ.Elements, S (represented x)}
  top_mem' _ _ := trivial
  pullback_stable' Γ Δ S σ hS x := by
    change S (represented x ≫ σ)
    rw [← represented_naturality]
    exact hS _
  transitive' Γ S hS R hR x := by
    have h := hR (hS x) (representableGeneric x.obj.unop)
    change R (represented (representableGeneric x.obj.unop) ≫ represented x) at h
    rw [represented_generic_identity] at h
    change R (𝟙 _ ≫ represented x) at h
    simpa only [Category.id_comp] using h

instance (Γ : Context.{w} C) :
    (CostructuredArrow.toOver representables Γ).IsCoverDense
      ((representedTopology (C := C)).over Γ) where
  is_cover U := by
    intro x
    rw [Sieve.overEquiv_iff]
    exact ⟨⟨CostructuredArrow.mk (represented x ≫ U.hom),
      Over.homMk (𝟙 _), Over.homMk (represented x), by
        apply Over.OverMorphism.ext
        exact Category.id_comp _⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def contextGlue {Γ A : Context.{w} C} {S : Sieve Γ}
    (hS : S ∈ representedTopology (C := C) Γ)
    (p : Presieve.FamilyOfElements (yoneda.obj A) S.arrows) (hp : p.Compatible) : Γ ⟶ A where
  app I := ↾fun z => (p (represented (Γ.elementsMk I z)) (hS _)).app I ⟨𝟙 _⟩
  naturality I K f := by
    ext z
    let x := Γ.elementsMk I z
    let y := Γ.elementsMk K (Γ.map f z)
    have h := hp (representableMap f.unop) (𝟙 _) (hS x) (hS y)
      (by simpa using represented_restrict (Functor.Elements.homMk f rfl : x ⟶ y))
    change representableMap f.unop ≫ p (represented x) (hS x) =
      (𝟙 _) ≫ p (represented y) (hS y) at h
    have hh := congrArg (fun k : representable.{w} K.unop ⟶ A => k.app K ⟨𝟙 K.unop⟩) h
    have hn := congrArg
      (fun k : (representable.{w} I.unop).obj I ⟶ A.obj K => k ⟨𝟙 I.unop⟩)
      ((p (represented x) (hS x)).naturality f)
    dsimp [representableMap, representable] at hh hn
    simp only [Category.id_comp, Category.comp_id] at hh hn
    exact hh.symm.trans hn

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem contextGlue_valid {Γ A : Context.{w} C} {S : Sieve Γ}
    (hS : S ∈ representedTopology (C := C) Γ)
    (p : Presieve.FamilyOfElements (yoneda.obj A) S.arrows) (hp : p.Compatible) :
    p.IsAmalgamation (contextGlue hS p hp) := by
  intro Δ f hf
  change f ≫ contextGlue hS p hp = p f hf
  ext I z
  let x := Δ.elementsMk I z
  have h := hp (𝟙 _) (represented x) (hS (f.mapElements.obj x)) hf
    (by simpa using represented_naturality f x)
  change (𝟙 _) ≫ p (represented (f.mapElements.obj x)) (hS _) =
    represented x ≫ p f hf at h
  have hh := congrArg (fun k : representable.{w} I.unop ⟶ A => k.app I ⟨𝟙 I.unop⟩) h
  change (p (represented (f.mapElements.obj x)) (hS _)).app I ⟨𝟙 I.unop⟩ =
    (p f hf).app I ((represented x).app I ⟨𝟙 I.unop⟩) at hh
  rw [show (represented x).app I ⟨𝟙 I.unop⟩ = z from represented_id x] at hh
  exact hh

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance : (representedTopology.{u,v,w} (C := C)).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ (fun A Γ S hS p hp => by
    refine ⟨contextGlue hS p hp, contextGlue_valid hS p hp, ?_⟩
    intro t ht
    change (t : Γ ⟶ A) = contextGlue hS p hp
    apply NatTrans.ext
    funext I
    apply ConcreteCategory.hom_ext
    intro z
    have h := ht (represented (Γ.elementsMk I z)) (hS _)
    change represented (Γ.elementsMk I z) ≫ t = p _ _ at h
    have hh := congrArg (fun k : representable.{w} I.unop ⟶ A => k.app I ⟨𝟙 I.unop⟩) h
    change t.app I ((represented (Γ.elementsMk I z)).app I ⟨𝟙 I.unop⟩) = _ at hh
    rw [show (represented (Γ.elementsMk I z)).app I ⟨𝟙 I.unop⟩ = z from represented_id _] at hh
    exact hh)

end Contexts

section Display
variable (Γ : B)

/-- Elements of the representable presheaf are arrows into the original context. -/
def elementOver : ElementSite.Site (yoneda.obj Γ) ⥤ Over Γ where
  obj X := Over.mk X.unop.val
  map f := Over.homMk f.unop.hom.unop f.unop.map_val
  map_id _ := rfl
  map_comp _ _ := rfl

def overElement : Over Γ ⥤ ElementSite.Site (yoneda.obj Γ) where
  obj X := op ((yoneda.obj Γ).elementsMk (op X.left) X.hom)
  map f := (Functor.Elements.homMk f.left.op (Over.w f)).op
  map_id _ := rfl
  map_comp _ _ := rfl

def elementOverEquivalence : ElementSite.Site (yoneda.obj Γ) ≌ Over Γ :=
  CategoryTheory.Equivalence.mk (elementOver Γ) (overElement Γ)
    (NatIso.ofComponents (fun X => eqToIso (by cases X; rfl)) (by
      intro X Y f
      apply Quiver.Hom.unop_inj
      apply Functor.Elements.hom_ext
      simp [elementOver, overElement]))
    (NatIso.ofComponents (fun X => eqToIso (by cases X; rfl)) (by
      intro X Y f
      apply Over.OverMorphism.ext
      change f.left ≫ eqToHom (by rfl) = eqToHom (by rfl) ≫ f.left
      simp))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem elementOver_pullback {X : ElementSite.Site (yoneda.obj Γ)}
    (S : Sieve ((elementOver Γ).obj X)) :
    ElementSite.down (yoneda.obj Γ) (S.functorPullback (elementOver Γ)) =
      Sieve.overEquiv _ S := by
  ext Y f
  rw [Sieve.overEquiv_iff]
  constructor
  · rintro ⟨y, h, hs⟩
    cases h
    exact hs
  · intro hs
    exact ⟨_, rfl, hs⟩

theorem overElement_pullback {X : Over Γ}
    (S : Sieve ((overElement Γ).obj X)) :
    Sieve.overEquiv _ (S.functorPullback (overElement Γ)) =
      ElementSite.down (yoneda.obj Γ) S := by
  ext Y f
  rw [Sieve.overEquiv_iff]
  constructor
  · intro hs
    exact ⟨_, rfl, hs⟩
  · rintro ⟨y, h, hs⟩
    cases h
    exact hs

variable (J : GrothendieckTopology B)

instance : (elementOver Γ).IsCocontinuous
    (ElementSite.topology (yoneda.obj Γ) J) (J.over Γ) where
  cover_lift hS := by
    rw [ElementSite.covering_iff, elementOver_pullback]
    exact hS

instance : (overElement Γ).IsCocontinuous
    (J.over Γ) (ElementSite.topology (yoneda.obj Γ) J) where
  cover_lift hS := by
    rw [GrothendieckTopology.mem_over_iff, overElement_pullback]
    exact hS

instance : (elementOverEquivalence Γ).inverse.IsDenseSubsite
    (J.over Γ) (ElementSite.topology (yoneda.obj Γ) J) := by
  let : (elementOverEquivalence Γ).functor.IsCocontinuous
      (ElementSite.topology (yoneda.obj Γ) J) (J.over Γ) :=
    inferInstanceAs ((elementOver Γ).IsCocontinuous _ _)
  let : (elementOverEquivalence Γ).inverse.IsCocontinuous
      (J.over Γ) (ElementSite.topology (yoneda.obj Γ) J) :=
    inferInstanceAs ((overElement Γ).IsCocontinuous _ _)
  exact (elementOverEquivalence Γ).isDenseSubsite_inverse_of_isCocontinuous _ _

/-- The slice-site equivalence transports actual sheaves, without sheafification. -/
def elementSheafEquivalence :
    Sheaf (ElementSite.topology (yoneda.obj Γ) J) (Type v) ≌
      Sheaf (J.over Γ) (Type v) :=
  (elementOverEquivalence Γ).sheafCongr _ _ (Type v)

variable [J.Subcanonical]

/-- The represented context is a sheaf by subcanonicity, not an assumed generic element law. -/
def contextSheaf : Sheaf J (Type v) :=
  ⟨yoneda.obj Γ, (isSheaf_iff_isSheaf_of_type _ _).2
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)⟩

/-- A sheaf-over object decodes to a total sheaf and its projection over the
original represented context. Sheafness of the total is derived by `SheafSlice`. -/
def displayEquivalence : Sheaf (J.over Γ) (Type v) ≌ Over (contextSheaf Γ J) :=
  (elementSheafEquivalence Γ J).symm.trans (SheafSlice.equivalence (contextSheaf Γ J)).symm

theorem display_sections (Q : Sheaf (J.over Γ) (Type v)) (X : B) :
    ((displayEquivalence Γ J).functor.obj Q).left.obj.obj (op X) =
      (Σ f : X ⟶ Γ, Q.obj.obj (op (Over.mk f))) := rfl

theorem display_projection (Q : Sheaf (J.over Γ) (Type v)) (X : B)
    (a : ((displayEquivalence Γ J).functor.obj Q).left.obj.obj (op X)) :
    ((displayEquivalence Γ J).functor.obj Q).hom.hom.app (op X) a = a.1 := rfl

theorem display_restriction (Q : Sheaf (J.over Γ) (Type v)) {X Y : B} (f : Y ⟶ X)
    (a : ((displayEquivalence Γ J).functor.obj Q).left.obj.obj (op X)) :
    ((displayEquivalence Γ J).functor.obj Q).left.obj.map f.op a =
      ⟨f ≫ a.1, Q.obj.map (Over.homMk f).op a.2⟩ := rfl

theorem display_map {Q R : Sheaf (J.over Γ) (Type v)} (k : Q ⟶ R) (X : B)
    (a : ((displayEquivalence Γ J).functor.obj Q).left.obj.obj (op X)) :
    ((displayEquivalence Γ J).functor.map k).left.hom.app (op X) a =
      ⟨a.1, k.hom.app (op (Over.mk a.1)) a.2⟩ := rfl

theorem display_recovery_projection (p : Over (contextSheaf Γ J)) :
    ((displayEquivalence Γ J).counitIso.app p).hom.left ≫ p.hom =
      ((displayEquivalence Γ J).functor.obj
        ((displayEquivalence Γ J).inverse.obj p)).hom :=
  Over.w _

end Display

section DenseDisplay
universe a b
variable {D : Type a} [Category.{b} D] (G : B ⥤ D)
variable (J : GrothendieckTopology D) (Γ : D)
variable [G.Full] [G.Faithful] [J.Subcanonical]
variable [(CostructuredArrow.toOver G Γ).IsCoverDense (J.over Γ)]
variable [∀ X : (Over Γ)ᵒᵖ,
  Limits.HasLimitsOfShape (StructuredArrow X (CostructuredArrow.toOver G Γ).op) (Type b)]

/-- The complete decoder retains the total sheaf, its projection, and all maps. -/
noncomputable def codeDisplayClassification :
    LocalCode.{u,v,b} G J Γ ≌ Over (contextSheaf Γ J) :=
  (sheafOverClassification G J Γ).trans (displayEquivalence Γ J)

end DenseDisplay

section Substitution
universe a b
variable {D : Type a} [Category.{b} D] (G : B ⥤ D)
variable (J : GrothendieckTopology D) [G.Full] [G.Faithful]
variable [∀ Γ : D, (CostructuredArrow.toOver G Γ).IsCoverDense (J.over Γ)]
variable [∀ (Γ : D) (X : (Over Γ)ᵒᵖ),
  Limits.HasLimitsOfShape (StructuredArrow X (CostructuredArrow.toOver G Γ).op) (Type w)]

/-- Substitution uses the actual sheaf-over pullback and returns its coherent
local presentation. The independent code category is not defined by this operation. -/
noncomputable def reindex {Γ Δ : D} (σ : Δ ⟶ Γ) :
    LocalCode.{u,v,w} G J Γ ⥤ LocalCode.{u,v,w} G J Δ :=
  (sheafOverClassification G J Γ).functor ⋙ J.overMapPullback (Type w) σ ⋙
    (sheafOverClassification G J Δ).inverse

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
noncomputable def decodeReindex {Γ Δ : D} (σ : Δ ⟶ Γ) :
    reindex G J σ ⋙ (sheafOverClassification G J Δ).functor ≅
      (sheafOverClassification G J Γ).functor ⋙ J.overMapPullback (Type w) σ :=
  Functor.isoWhiskerLeft
    ((sheafOverClassification G J Γ).functor ⋙ J.overMapPullback (Type w) σ)
    (sheafOverClassification G J Δ).counitIso

noncomputable def reindexId (Γ : D) :
    reindex G J (𝟙 Γ) ≅ 𝟭 (LocalCode.{u,v,w} G J Γ) :=
  Functor.isoWhiskerLeft (sheafOverClassification G J Γ).functor
    (Functor.isoWhiskerRight (J.overMapPullbackId (Type w) Γ)
      (sheafOverClassification G J Γ).inverse) ≪≫
    (sheafOverClassification G J Γ).unitIso.symm

noncomputable def reindexComp {Γ Δ Θ : D} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    reindex G J σ ⋙ reindex G J τ ≅ reindex G J (τ ≫ σ) :=
  Functor.isoWhiskerLeft
    ((sheafOverClassification G J Γ).functor ⋙ J.overMapPullback (Type w) σ)
    (Functor.isoWhiskerRight (sheafOverClassification G J Δ).counitIso
      (J.overMapPullback (Type w) τ ⋙ (sheafOverClassification G J Θ).inverse)) ≪≫
    Functor.isoWhiskerLeft (sheafOverClassification G J Γ).functor
      (Functor.isoWhiskerRight (J.overMapPullbackComp (Type w) τ σ)
        (sheafOverClassification G J Θ).inverse)

theorem decodeReindex_comp {Γ Δ Θ : D} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (A : LocalCode.{u,v,w} G J Γ) :
    (sheafOverClassification G J Θ).functor.map ((reindexComp G J σ τ).hom.app A) ≫
        (decodeReindex G J (τ ≫ σ)).hom.app A =
      (decodeReindex G J τ).hom.app ((reindex G J σ).obj A) ≫
        (J.overMapPullback (Type w) τ).map ((decodeReindex G J σ).hom.app A) ≫
        (J.overMapPullbackComp (Type w) τ σ).hom.app
          ((sheafOverClassification G J Γ).functor.obj A) := by
  dsimp [reindexComp, decodeReindex, reindex]
  rw [← Functor.map_comp]
  exact (sheafOverClassification G J Θ).counitIso.hom.naturality _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem decodeReindex_id (Γ : D) (A : LocalCode.{u,v,w} G J Γ) :
    (sheafOverClassification G J Γ).functor.map ((reindexId G J Γ).hom.app A) =
      (decodeReindex G J (𝟙 Γ)).hom.app A ≫
        (J.overMapPullbackId (Type w) Γ).hom.app
          ((sheafOverClassification G J Γ).functor.obj A) := by
  change (sheafOverClassification G J Γ).functor.map
    ((sheafOverClassification G J Γ).inverse.map
      ((J.overMapPullbackId (Type w) Γ).hom.app
        ((sheafOverClassification G J Γ).functor.obj A)) ≫
      (sheafOverClassification G J Γ).unitIso.inv.app A) = _
  rw [Functor.map_comp]
  rw [← (sheafOverClassification G J Γ).counit_app_functor]
  exact (sheafOverClassification G J Γ).counitIso.hom.naturality _

end Substitution

end SquareKit.CoherentSheafOver
