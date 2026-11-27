import SquareKit.StackObjectPropertyDescent
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-! Local generation by objects of a prestack on singleton covers. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.StackLocalGeneration

open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe u v u' v'

variable {C : Type u} [Category.{v} C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

/-- Every object of the target comes from the source after a singleton cover.
The local lift includes an isomorphism, so this condition retains automorphisms. -/
def LocallyGenerating (J : GrothendieckTopology C) (η : F ⟶ B) : Prop :=
  ∀ (X : C) (b : B.obj (.mk (op X))),
    ∃ (Y : C) (p : Y ⟶ X),
      Sieve.ofArrows _ (fun _ : Unit => p) ∈ J X ∧
      ∃ a : F.obj (.mk (op Y)),
        Nonempty ((η.app (.mk (op Y))).toFunctor.obj a ≅
          (B.map p.op.toLoc).toFunctor.obj b)

/-- Restriction acts on transformations and on their modifications. -/
abbrev restriction (η : F ⟶ B) (T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) :
    (B ⟶ T) ⥤ (F ⟶ T) := Bicategory.precomp T η

/-- Equality of arrows into a prestack can be checked on one covering map. -/
theorem hom_ext_cover (J : GrothendieckTopology C) [T.IsPrestack J]
    {X Y : C} (p : Y ⟶ X)
    (hp : Sieve.ofArrows _ (fun _ : Unit => p) ∈ J X)
    {a b : T.obj (.mk (op X))} {f g : a ⟶ b}
    (h : (T.map p.op.toLoc).toFunctor.map f =
      (T.map p.op.toLoc).toFunctor.map g) : f = g := by
  apply (T.fullyFaithfulToDescentData (fun _ : Unit => p) hp).map_injective
  ext i
  exact h

/-- The identity presentation is locally generating, without a stack assumption. -/
theorem locallyGenerating_id (J : GrothendieckTopology C) :
    LocallyGenerating J (𝟙 B) := by
  intro X b
  refine ⟨X, 𝟙 X, ?_, b, ?_⟩
  · rw [(Sieve.id_mem_iff_eq_top).mp
      (Sieve.ofArrows_mk (fun _ : Unit => X) (fun _ => 𝟙 X) ())]
    exact J.top_mem X
  · exact ⟨((Cat.Hom.toNatIso (B.mapId (.mk (op X)))).app b).symm⟩

/-- Modifications into a prestack are determined on a locally generating source. -/
theorem modification_ext (J : GrothendieckTopology C) [T.IsPrestack J]
    (η : F ⟶ B) (hη : LocallyGenerating J η)
    {α β : B ⟶ T} {γ δ : α ⟶ β}
    (h : ∀ (X : C) (a : F.obj (.mk (op X))),
      (γ.as.app (.mk (op X))).toNatTrans.app ((η.app _).toFunctor.obj a) =
        (δ.as.app (.mk (op X))).toNatTrans.app ((η.app _).toFunctor.obj a)) : γ = δ := by
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro X
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext b
  obtain ⟨Y, p, hp, a, ⟨e⟩⟩ := hη X.as.unop b
  apply hom_ext_cover J p hp
  have he : (γ.as.app (.mk (op Y))).toNatTrans.app
      ((B.map p.op.toLoc).toFunctor.obj b) =
      (δ.as.app (.mk (op Y))).toNatTrans.app
        ((B.map p.op.toLoc).toFunctor.obj b) := by
    apply (cancel_epi ((α.app (.mk (op Y))).toFunctor.map e.hom)).mp
    rw [(γ.as.app (.mk (op Y))).toNatTrans.naturality,
      (δ.as.app (.mk (op Y))).toNatTrans.naturality, h Y a]
  have hγ := congrArg (fun k => k.toNatTrans.app b) (γ.as.naturality p.op.toLoc)
  have hδ := congrArg (fun k => k.toNatTrans.app b) (δ.as.naturality p.op.toLoc)
  dsimp at hγ hδ
  apply (cancel_epi ((α.naturality p.op.toLoc).hom.toNatTrans.app b)).mp
  exact hγ.symm.trans ((congrArg (fun k => k ≫
    (β.naturality p.op.toLoc).hom.toNatTrans.app b) he).trans hδ)

/-- Restriction along a locally generating presentation is faithful on modifications. -/
theorem faithfulRestriction (J : GrothendieckTopology C) [T.IsPrestack J]
    (η : F ⟶ B) (hη : LocallyGenerating J η) :
    (restriction η T).Faithful where
  map_injective {α β} γ δ h := by
    apply modification_ext J η hη
    intro X a
    exact congrArg (fun k => (k.as.app (.mk (op X))).toNatTrans.app a) h

section ModificationExtension
open StackDescentTransformation
variable (η : F ⟶ B) (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {α β : B ⟶ T} (Γ : η ≫ α ⟶ η ≫ β)

/-- A modification on the source acts on every object isomorphic to a source image. -/
def modificationOnImage {X : C} {b : B.obj (.mk (op X))}
    {a : F.obj (.mk (op X))} (e : (component η X).obj a ≅ b) :
    (component α X).obj b ⟶ (component β X).obj b :=
  (component α X).map e.inv ≫ (Γ.as.app (.mk (op X))).toNatTrans.app a ≫
    (component β X).map e.hom

include hFF in
/-- Fullness supplies the source arrow needed for naturality on image objects. -/
theorem modificationOnImage_naturality {X : C} {b c : B.obj (.mk (op X))}
    {a a' : F.obj (.mk (op X))} (e : (component η X).obj a ≅ b)
    (e' : (component η X).obj a' ≅ c) (h : b ⟶ c) :
    (component α X).map h ≫ modificationOnImage η Γ e' =
      modificationOnImage η Γ e ≫ (component β X).map h := by
  let γ : component η X ⋙ component α X ⟶ component η X ⋙ component β X :=
    (Γ.as.app (.mk (op X))).toNatTrans
  let k := (hFF X).preimage (e.hom ≫ h ≫ e'.inv)
  have hk : (component η X).map k = e.hom ≫ h ≫ e'.inv := (hFF X).map_preimage _
  have hn := γ.naturality k
  change (component α X).map ((component η X).map k) ≫ _ =
    _ ≫ (component β X).map ((component η X).map k) at hn
  rw [hk] at hn
  change (component α X).map h ≫
    ((component α X).map e'.inv ≫ γ.app a' ≫ (component β X).map e'.hom) =
    ((component α X).map e.inv ≫ γ.app a ≫ (component β X).map e.hom) ≫
      (component β X).map h
  rw [← cancel_epi ((component α X).map e.hom),
    ← cancel_mono ((component β X).map e'.inv)]
  simpa [Category.assoc] using hn

include hFF in
/-- The arrow on an image object does not depend on its chosen source lift. -/
theorem modificationOnImage_eq {X : C} {b : B.obj (.mk (op X))}
    {a a' : F.obj (.mk (op X))} (e : (component η X).obj a ≅ b)
    (e' : (component η X).obj a' ≅ b) :
    modificationOnImage η Γ e = modificationOnImage η Γ e' := by
  simpa using (modificationOnImage_naturality η hFF Γ e e' (𝟙 b)).symm

/-- Restriction transports a chosen image presentation through strong naturality. -/
def restrictedImageIso {X Y : C} (p : Y ⟶ X) {b : B.obj (.mk (op X))}
    {a : F.obj (.mk (op X))} (e : (component η X).obj a ≅ b) :
    (component η Y).obj ((F.map p.op.toLoc).toFunctor.obj a) ≅
      (B.map p.op.toLoc).toFunctor.obj b :=
  (comparison η p).app a ≪≫ (B.map p.op.toLoc).toFunctor.mapIso e

/-- The induced arrow on image objects commutes with restriction. -/
theorem modificationOnImage_restrict {X Y : C} (p : Y ⟶ X)
    {b : B.obj (.mk (op X))} {a : F.obj (.mk (op X))}
    (e : (component η X).obj a ≅ b) :
    modificationOnImage η Γ (restrictedImageIso η p e) ≫ (comparison β p).hom.app b =
      (comparison α p).hom.app b ≫
        (T.map p.op.toLoc).toFunctor.map (modificationOnImage η Γ e) := by
  have hΓ := modification_naturality Γ.as p a
  change (Γ.as.app (.mk (op Y))).toNatTrans.app ((F.map p.op.toLoc).toFunctor.obj a) ≫
      (comparison (Pseudofunctor.StrongTrans.vcomp η β) p).hom.app a =
    (comparison (Pseudofunctor.StrongTrans.vcomp η α) p).hom.app a ≫
      (T.map p.op.toLoc).toFunctor.map ((Γ.as.app (.mk (op X))).toNatTrans.app a) at hΓ
  rw [comparison_vcomp_hom, comparison_vcomp_hom] at hΓ
  have hα := (comparison α p).hom.naturality e.inv
  have hβ := (comparison β p).hom.naturality e.hom
  dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.comp_map] at hα hβ
  let γX : component η X ⋙ component α X ⟶ component η X ⋙ component β X :=
    (Γ.as.app (.mk (op X))).toNatTrans
  let γY : component η Y ⋙ component α Y ⟶ component η Y ⋙ component β Y :=
    (Γ.as.app (.mk (op Y))).toNatTrans
  change ((component α Y).map
      ((B.map p.op.toLoc).toFunctor.map e.inv ≫ (comparison η p).inv.app a) ≫
    (γY.app ((F.map p.op.toLoc).toFunctor.obj a) ≫
      (component β Y).map ((comparison η p).hom.app a ≫
        (B.map p.op.toLoc).toFunctor.map e.hom))) ≫ (comparison β p).hom.app b =
    (comparison α p).hom.app b ≫ (T.map p.op.toLoc).toFunctor.map
      ((component α X).map e.inv ≫ γX.app a ≫ (component β X).map e.hom)
  change γY.app ((F.map p.op.toLoc).toFunctor.obj a) ≫
      (component β Y).map ((comparison η p).hom.app a) ≫
        (comparison β p).hom.app ((component η X).obj a) =
    ((component α Y).map ((comparison η p).hom.app a) ≫
        (comparison α p).hom.app ((component η X).obj a)) ≫
      (T.map p.op.toLoc).toFunctor.map (γX.app a) at hΓ
  simp only [Functor.map_comp, Category.assoc]
  rw [hβ, reassoc_of% hΓ]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Cat.Hom.comp_toFunctor, Functor.comp_obj, CategoryTheory.Category.comp_id]
  rw [reassoc_of% hα]
  simp [Functor.map_comp, Category.assoc]


/-- A source modification gives an arrow between restrictions of the target objects. -/
def localModification {X Y : C} (p : Y ⟶ X) {b : B.obj (.mk (op X))}
    {a : F.obj (.mk (op Y))} (e : (component η Y).obj a ≅
      (B.map p.op.toLoc).toFunctor.obj b) :
    (T.map p.op.toLoc).toFunctor.obj ((component α X).obj b) ⟶
      (T.map p.op.toLoc).toFunctor.obj ((component β X).obj b) :=
  (comparison α p).inv.app b ≫ modificationOnImage η Γ e ≫ (comparison β p).hom.app b

/-- A chosen local image determines the entire canonical target descent comparison. -/
def localImageDescentIso {X Y : C} (p : Y ⟶ X) {b : B.obj (.mk (op X))}
    {a : F.obj (.mk (op Y))} (e : (component η Y).obj a ≅
      (B.map p.op.toLoc).toFunctor.obj b) (α : B ⟶ T) :
    (map (η ≫ α) (fun _ : Unit => p)).obj
      (liftData η hFF ((B.toDescentData (fun _ : Unit => p)).obj b) (fun _ => a) (fun _ => e)) ≅
      (T.toDescentData (fun _ : Unit => p)).obj ((component α X).obj b) :=
  mapCompObjIso η (fun _ : Unit => p) α _ ≪≫
    (map α _).mapIso (liftDataIso η hFF _ _ _) ≪≫ canonicalObjIso α _ b

/-- The modification on a local source image is compatible on every overlap. -/
def localModificationData {X Y : C} (p : Y ⟶ X) {b : B.obj (.mk (op X))}
    {a : F.obj (.mk (op Y))} (e : (component η Y).obj a ≅
      (B.map p.op.toLoc).toFunctor.obj b) :
    (T.toDescentData (fun _ : Unit => p)).obj ((component α X).obj b) ⟶
      (T.toDescentData (fun _ : Unit => p)).obj ((component β X).obj b) :=
  (localImageDescentIso η hFF p e α).inv ≫
    (mapModification (fun _ : Unit => p) Γ.as).app _ ≫
      (localImageDescentIso η hFF p e β).hom

@[simp] theorem localModificationData_hom {X Y : C} (p : Y ⟶ X)
    {b : B.obj (.mk (op X))} {a : F.obj (.mk (op Y))}
    (e : (component η Y).obj a ≅ (B.map p.op.toLoc).toFunctor.obj b) :
    (localModificationData η hFF Γ p e).hom () = localModification η Γ p e := by
  let γ : component η Y ⋙ component α Y ⟶ component η Y ⋙ component β Y :=
    (Γ.as.app (.mk (op Y))).toNatTrans
  change (((comparison α p).inv.app b ≫ (component α Y).map e.inv) ≫ 𝟙 _) ≫
    γ.app a ≫ 𝟙 _ ≫ ((component β Y).map e.hom ≫ (comparison β p).hom.app b) =
    (comparison α p).inv.app b ≫
      ((component α Y).map e.inv ≫ γ.app a ≫ (component β Y).map e.hom) ≫
        (comparison β p).hom.app b
  simp [Category.assoc]

/-- Arrow descent extends the given modification across any covering source presentation. -/
def descendModification (J : GrothendieckTopology C) [T.IsPrestack J]
    {X Y : C} (p : Y ⟶ X) (hp : Sieve.ofArrows _ (fun _ : Unit => p) ∈ J X)
    {b : B.obj (.mk (op X))} {a : F.obj (.mk (op Y))}
    (e : (component η Y).obj a ≅ (B.map p.op.toLoc).toFunctor.obj b) :
    (component α X).obj b ⟶ (component β X).obj b :=
  (T.fullyFaithfulToDescentData _ hp).preimage (localModificationData η hFF Γ p e)

/-- Restriction of the descended arrow is the specified local modification. -/
theorem descendModification_restrict (J : GrothendieckTopology C) [T.IsPrestack J]
    {X Y : C} (p : Y ⟶ X) (hp : Sieve.ofArrows _ (fun _ : Unit => p) ∈ J X)
    {b : B.obj (.mk (op X))} {a : F.obj (.mk (op Y))}
    (e : (component η Y).obj a ≅ (B.map p.op.toLoc).toFunctor.obj b) :
    (T.map p.op.toLoc).toFunctor.map (descendModification η hFF Γ J p hp e) =
      localModification η Γ p e := by
  have h := (T.fullyFaithfulToDescentData _ hp).map_preimage (localModificationData η hFF Γ p e)
  exact (congrArg (fun k => k.hom ()) h).trans (localModificationData_hom η hFF Γ p e)

/-- A second restriction presents the object over the composite parameter map. -/
def refinedImageIso {X Y Z : C} (p : Y ⟶ X) (g : Z ⟶ Y)
    {b : B.obj (.mk (op X))} {a : F.obj (.mk (op Y))}
    (e : (component η Y).obj a ≅ (B.map p.op.toLoc).toFunctor.obj b) :
    (component η Z).obj ((F.map g.op.toLoc).toFunctor.obj a) ≅
      (B.map (g ≫ p).op.toLoc).toFunctor.obj b :=
  restrictedImageIso η g e ≪≫ ((Cat.Hom.toNatIso (B.mapComp' p.op.toLoc g.op.toLoc (g ≫ p).op.toLoc (by grind))).app b).symm

include hFF in
/-- Local modification arrows commute with refinement of the presenting map. -/
theorem localModification_refine {X Y Z : C} (p : Y ⟶ X) (g : Z ⟶ Y)
    {b : B.obj (.mk (op X))} {a : F.obj (.mk (op Y))}
    (e : (component η Y).obj a ≅ (B.map p.op.toLoc).toFunctor.obj b) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (localModification η Γ p e) g
        (g ≫ p) (g ≫ p) = localModification η Γ (g ≫ p) (refinedImageIso η p g e) := by
  have hα := comparison_comp_hom α p g (g ≫ p) rfl b
  have hβ := comparison_comp_hom β p g (g ≫ p) rfl b
  have hr := modificationOnImage_restrict η Γ g e
  have hn := modificationOnImage_naturality η hFF Γ
    (refinedImageIso η p g e) (restrictedImageIso η g e)
    ((B.mapComp' p.op.toLoc g.op.toLoc (g ≫ p).op.toLoc (by grind)).hom.toNatTrans.app b)
  dsimp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  dsimp only [localModification]
  rw [← cancel_epi ((comparison α (g ≫ p)).hom.app b)]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  rw [reassoc_of% hα]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  rw [Functor.map_comp_assoc]
  rw [← reassoc_of% hr]
  rw [← cancel_mono ((T.mapComp' p.op.toLoc g.op.toLoc (g ≫ p).op.toLoc (by grind)).hom.toNatTrans.app _)]
  simp only [Category.assoc, ← Cat.Hom.toNatIso_hom, ← Cat.Hom.toNatIso_inv,
    Iso.inv_hom_id_app, Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.comp_id]
  simp only [← Cat.Hom.toNatIso_hom] at hβ hn
  rw [hβ, ← reassoc_of% hn]

include hFF in
/-- The local modification is natural in an arbitrary arrow with source lifts at both ends. -/
theorem localModification_naturality {X Y : C} (p : Y ⟶ X)
    {b c : B.obj (.mk (op X))} {a a' : F.obj (.mk (op Y))}
    (e : (component η Y).obj a ≅ (B.map p.op.toLoc).toFunctor.obj b)
    (e' : (component η Y).obj a' ≅ (B.map p.op.toLoc).toFunctor.obj c) (h : b ⟶ c) :
    (T.map p.op.toLoc).toFunctor.map ((component α X).map h) ≫ localModification η Γ p e' =
      localModification η Γ p e ≫ (T.map p.op.toLoc).toFunctor.map ((component β X).map h) := by
  have hα := (comparison α p).inv.naturality h
  have hβ := (comparison β p).hom.naturality h
  dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.comp_map] at hα hβ
  dsimp only [localModification]
  simp only [Category.assoc]
  rw [reassoc_of% hα, reassoc_of% modificationOnImage_naturality η hFF Γ e e', hβ]

/-- Refinement with a specified composite has the same source lift. -/
def refinedImageIsoOfEq {X Y Z : C} (p : Y ⟶ X) (g : Z ⟶ Y) (r : Z ⟶ X)
    (hr : g ≫ p = r) {b : B.obj (.mk (op X))} {a : F.obj (.mk (op Y))}
    (e : (component η Y).obj a ≅ (B.map p.op.toLoc).toFunctor.obj b) :
    (component η Z).obj ((F.map g.op.toLoc).toFunctor.obj a) ≅
      (B.map r.op.toLoc).toFunctor.obj b :=
  refinedImageIso η p g e ≪≫ eqToIso (congrArg (fun q => (B.map q.op.toLoc).toFunctor.obj b) hr)

/-- The descended arrow has the prescribed value on every refinement. -/
theorem descendModification_refine (J : GrothendieckTopology C) [T.IsPrestack J]
    {X Y Z : C} (p : Y ⟶ X) (hp : Sieve.ofArrows _ (fun _ : Unit => p) ∈ J X)
    {b : B.obj (.mk (op X))} {a : F.obj (.mk (op Y))}
    (e : (component η Y).obj a ≅ (B.map p.op.toLoc).toFunctor.obj b)
    (g : Z ⟶ Y) (r : Z ⟶ X) (hr : g ≫ p = r) :
    (T.map r.op.toLoc).toFunctor.map (descendModification η hFF Γ J p hp e) =
      localModification η Γ r (refinedImageIsoOfEq η p g r hr e) := by
  subst r
  simp only [refinedImageIsoOfEq, eqToIso_refl, Iso.trans_refl]
  rw [← localModification_refine η hFF Γ p g e,
    ← descendModification_restrict η hFF Γ J p hp e]
  exact (T.mapComp'_naturality_2 p.op.toLoc g.op.toLoc (g ≫ p).op.toLoc (by grind) _).symm

/-- The descended component is independent of its covering source presentation. -/
theorem descendModification_eq (J : GrothendieckTopology C) [T.IsPrestack J]
    {X Y Z : C} (p : Y ⟶ X) (q : Z ⟶ X)
    (hp : Sieve.ofArrows _ (fun _ : Unit => p) ∈ J X)
    (hq : Sieve.ofArrows _ (fun _ : Unit => q) ∈ J X) [Limits.HasPullback p q]
    {b : B.obj (.mk (op X))} {a : F.obj (.mk (op Y))} {a' : F.obj (.mk (op Z))}
    (e : (component η Y).obj a ≅ (B.map p.op.toLoc).toFunctor.obj b)
    (e' : (component η Z).obj a' ≅ (B.map q.op.toLoc).toFunctor.obj b) :
    descendModification η hFF Γ J p hp e = descendModification η hFF Γ J q hq e' := by
  apply hom_ext_cover J (Limits.pullback.fst p q ≫ p)
    (StackObjectPropertyDescent.singleton_common J p q hp hq)
  rw [descendModification_refine η hFF Γ J p hp e (Limits.pullback.fst p q) _ rfl,
    descendModification_refine η hFF Γ J q hq e' (Limits.pullback.snd p q) _
      Limits.pullback.condition.symm]
  dsimp only [localModification]
  rw [modificationOnImage_eq η hFF Γ]

include hFF in
/-- The local formula is compatible with composing arbitrary parameter maps. -/
theorem localModification_comp {X Y Z : C} (p : Y ⟶ X) (g : Z ⟶ Y)
    (r : Z ⟶ X) (hr : g ≫ p = r)
    {b : B.obj (.mk (op X))} {a : F.obj (.mk (op Z))}
    (e : (component η Z).obj a ≅
      (B.map g.op.toLoc).toFunctor.obj ((B.map p.op.toLoc).toFunctor.obj b)) :
    localModification η Γ r
        (e ≪≫ ((Cat.Hom.toNatIso (B.mapComp' p.op.toLoc g.op.toLoc r.op.toLoc
          (by grind))).app b).symm) ≫
      (T.mapComp' p.op.toLoc g.op.toLoc r.op.toLoc (by grind)).hom.toNatTrans.app
        ((component β X).obj b) =
    (T.mapComp' p.op.toLoc g.op.toLoc r.op.toLoc (by grind)).hom.toNatTrans.app
        ((component α X).obj b) ≫
      (T.map g.op.toLoc).toFunctor.map ((comparison α p).inv.app b) ≫
        localModification η Γ g e ≫
          (T.map g.op.toLoc).toFunctor.map ((comparison β p).hom.app b) := by
  have hα := comparison_comp_hom α p g r hr b
  have hβ := comparison_comp_hom β p g r hr b
  have hn := modificationOnImage_naturality η hFF Γ
    (e ≪≫ ((Cat.Hom.toNatIso (B.mapComp' p.op.toLoc g.op.toLoc r.op.toLoc
      (by grind))).app b).symm) e
    ((B.mapComp' p.op.toLoc g.op.toLoc r.op.toLoc (by grind)).hom.toNatTrans.app b)
  dsimp only [localModification]
  rw [← cancel_epi ((comparison α r).hom.app b)]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [hβ, reassoc_of% hα]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Cat.Hom.comp_toFunctor, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hn]

variable (J : GrothendieckTopology C) [T.IsPrestack J] [Limits.HasPullbacks C]
variable (hη : LocallyGenerating J η)

include hη in
/-- Local generation and arrow descent determine a component independently of its cover. -/
theorem exists_modificationComponent {X : C} (b : B.obj (.mk (op X))) :
    ∃ k : (component α X).obj b ⟶ (component β X).obj b,
      ∀ (Y : C) (p : Y ⟶ X) (hp : Sieve.ofArrows _ (fun _ : Unit => p) ∈ J X)
        (a : F.obj (.mk (op Y)))
        (e : (component η Y).obj a ≅ (B.map p.op.toLoc).toFunctor.obj b),
        k = descendModification η hFF Γ J p hp e := by
  obtain ⟨Y, p, hp, a, ⟨e⟩⟩ := hη X b
  refine ⟨descendModification η hFF Γ J p hp e, ?_⟩
  intro Z q hq a' e'
  exact descendModification_eq η hFF Γ J p q hp hq e e'

/-- The component of the extended modification at an arbitrary target object. -/
def modificationComponent {X : C} (b : B.obj (.mk (op X))) :
    (component α X).obj b ⟶ (component β X).obj b :=
  Classical.choose (exists_modificationComponent η hFF Γ J hη b)

/-- Every covering source presentation computes the same component. -/
theorem modificationComponent_eq {X Y : C} (b : B.obj (.mk (op X)))
    (p : Y ⟶ X) (hp : Sieve.ofArrows _ (fun _ : Unit => p) ∈ J X)
    (a : F.obj (.mk (op Y)))
    (e : (component η Y).obj a ≅ (B.map p.op.toLoc).toFunctor.obj b) :
    modificationComponent η hFF Γ J hη b = descendModification η hFF Γ J p hp e :=
  Classical.choose_spec (exists_modificationComponent η hFF Γ J hη b) Y p hp a e

/-- Local recovery holds on every covering source presentation. -/
theorem modificationComponent_restrict {X Y : C} (b : B.obj (.mk (op X)))
    (p : Y ⟶ X) (hp : Sieve.ofArrows _ (fun _ : Unit => p) ∈ J X)
    (a : F.obj (.mk (op Y)))
    (e : (component η Y).obj a ≅ (B.map p.op.toLoc).toFunctor.obj b) :
    (T.map p.op.toLoc).toFunctor.map (modificationComponent η hFF Γ J hη b) =
      localModification η Γ p e := by
  rw [modificationComponent_eq η hFF Γ J hη b p hp a e]
  exact descendModification_restrict η hFF Γ J p hp e

/-- The descended components are natural in every arrow of the target fiber. -/
theorem modificationComponent_naturality {X : C} {b c : B.obj (.mk (op X))} (h : b ⟶ c) :
    (component α X).map h ≫ modificationComponent η hFF Γ J hη c =
      modificationComponent η hFF Γ J hη b ≫ (component β X).map h := by
  obtain ⟨Y, p, hp, a, ⟨e⟩⟩ := hη X b
  obtain ⟨Z, q, hq, a', ⟨e'⟩⟩ := hη X c
  let r := Limits.pullback.fst p q ≫ p
  have hr := StackObjectPropertyDescent.singleton_common J p q hp hq
  let eb := refinedImageIsoOfEq η p (Limits.pullback.fst p q) r rfl e
  let ec := refinedImageIsoOfEq η q (Limits.pullback.snd p q) r Limits.pullback.condition.symm e'
  apply hom_ext_cover J r hr
  rw [Functor.map_comp, Functor.map_comp,
    modificationComponent_restrict η hFF Γ J hη c r hr _ ec,
    modificationComponent_restrict η hFF Γ J hη b r hr _ eb]
  exact localModification_naturality η hFF Γ r eb ec h

/-- On source images, extension recovers the original modification with its chosen isomorphism. -/
theorem modificationComponent_onImage {X : C} {b : B.obj (.mk (op X))}
    {a : F.obj (.mk (op X))} (e : (component η X).obj a ≅ b) :
    modificationComponent η hFF Γ J hη b = modificationOnImage η Γ e := by
  obtain ⟨Y, p, hp, a', ⟨e'⟩⟩ := hη X b
  apply hom_ext_cover J p hp
  rw [modificationComponent_restrict η hFF Γ J hη b p hp a' e']
  dsimp only [localModification]
  rw [modificationOnImage_eq η hFF Γ e' (restrictedImageIso η p e),
    modificationOnImage_restrict η Γ p e]
  simp

/-- The extended components commute with every change of parameter. -/
theorem modificationComponent_change {X Y : C} (f : Y ⟶ X)
    (b : B.obj (.mk (op X))) :
    modificationComponent η hFF Γ J hη ((B.map f.op.toLoc).toFunctor.obj b) ≫
        (comparison β f).hom.app b =
      (comparison α f).hom.app b ≫
        (T.map f.op.toLoc).toFunctor.map (modificationComponent η hFF Γ J hη b) := by
  obtain ⟨U, p, hp, a, ⟨e⟩⟩ := hη X b
  let q := Limits.pullback.fst f p
  let g := Limits.pullback.snd f p
  let r := q ≫ f
  have hq := StackObjectPropertyDescent.singleton_pullback J p f hp
  have hr : g ≫ p = r := Limits.pullback.condition.symm
  let er := refinedImageIsoOfEq η p g r hr e
  let ey := er ≪≫ (Cat.Hom.toNatIso (B.mapComp' f.op.toLoc q.op.toLoc r.op.toLoc
    (by dsimp only [r]; grind))).app b
  apply hom_ext_cover J q hq
  rw [Functor.map_comp, Functor.map_comp,
    modificationComponent_restrict η hFF Γ J hη _ q hq _ ey]
  apply (cancel_epi
    ((T.mapComp' f.op.toLoc q.op.toLoc r.op.toLoc (by dsimp only [r]; grind)).hom.toNatTrans.app
      ((component α X).obj b) ≫
      (T.map q.op.toLoc).toFunctor.map ((comparison α f).inv.app b))).mp
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Cat.Hom.comp_toFunctor, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← localModification_comp η hFF Γ f q r rfl ey,
    ← T.mapComp'_hom_naturality]
  rw [modificationComponent_eq η hFF Γ J hη b p hp a e,
    descendModification_refine η hFF Γ J p hp e g r hr]
  dsimp only [localModification]
  rw [modificationOnImage_eq η hFF Γ]

/-- A source modification extends uniquely across a fully faithful locally generating unit. -/
def extendModification : α ⟶ β where
  as.app X := Cat.Hom₂.ofNatTrans {
    app b := modificationComponent η hFF Γ J hη b
    naturality _ _ h := modificationComponent_naturality η hFF Γ J hη h }
  as.naturality {X Y} f := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext b
    exact modificationComponent_change η hFF Γ J hη f.as.unop b

/-- Restricting the extension gives the original modification, including every component. -/
theorem restriction_extendModification :
    (restriction η T).map (extendModification η hFF Γ J hη) = Γ := by
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro X
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext a
  change modificationComponent η hFF Γ J hη ((component η X.as.unop).obj a) = _
  rw [modificationComponent_onImage η hFF Γ J hη (Iso.refl _)]
  dsimp only [modificationOnImage, Iso.refl_hom, Iso.refl_inv]
  change (component α X.as.unop).map (𝟙 _) ≫
    (Γ.as.app X).toNatTrans.app a ≫ (component β X.as.unop).map (𝟙 _) = _
  rw [(component α X.as.unop).map_id, (component β X.as.unop).map_id, Category.id_comp]
  exact Category.comp_id _

include hFF hη in
/-- Restriction is full on modifications for a fully faithful locally generating unit. -/
theorem fullRestriction : (restriction η T).Full where
  map_surjective Γ := ⟨extendModification η hFF Γ J hη,
    restriction_extendModification η hFF Γ J hη⟩

/-- Restriction identifies the complete categories of modifications between fixed transformations. -/
def fullyFaithfulRestriction : (restriction η T).FullyFaithful := by
  letI := fullRestriction η hFF J hη (T := T)
  letI := faithfulRestriction J η hη (T := T)
  exact Functor.FullyFaithful.ofFullyFaithful _

end ModificationExtension

end SquareKit.StackLocalGeneration
