import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
/-! Small composition adapters for Mathlib pseudofunctors and strong transformations.
The span-interpretation client uses these to retain its chosen comparison maps. -/
noncomputable section
namespace SquareKit.PseudofunctorCoherence
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄
variable {B : Type u₁} [Bicategory.{w₁,v₁} B]
variable {C : Type u₂} [Bicategory.{w₂,v₂} C]
variable {D : Type u₃} [Bicategory.{w₃,v₃} D]
variable {E : Type u₄} [Bicategory.{w₄,v₄} E]
/-- Mathlib's invertible modifications, with the hom-category fixed explicitly. -/
abbrev ModificationIso {F G : B ⥤ᵖ C} (η θ : Pseudofunctor.StrongTrans F G) :=
  @Iso _ (Pseudofunctor.StrongTrans.homCategory (F := F) (G := G)) η θ

/-- Identity invertible modification with its category fixed before elaboration. -/
def modificationRefl {F G : B ⥤ᵖ C} (η : Pseudofunctor.StrongTrans F G) : ModificationIso η η :=
  @Iso.refl _ (Pseudofunctor.StrongTrans.homCategory (F := F) (G := G)) η

/-- Equality retains the complete maps and both comparison isomorphisms. -/
theorem ext {F G : B ⥤ᵖ C} (h : F.toPrelaxFunctor = G.toPrelaxFunctor)
    (hi : HEq F.mapId G.mapId) (hc : HEq (@F.mapComp) (@G.mapComp)) : F = G := by
  cases F
  cases G
  cases h
  cases hi
  cases hc
  rfl
set_option backward.isDefEq.respectTransparency false in
/-- Precompose a strong transformation, deriving its laws from naturality. -/
def precomp (F : B ⥤ᵖ C) {G H : C ⥤ᵖ D} (η : G ⟶ H) : F.comp G ⟶ F.comp H where
  app a := η.app (F.obj a)
  naturality f := η.naturality (F.map f)
  naturality_naturality k := η.naturality_naturality (F.map₂ k)
  naturality_id a := by
    dsimp [Pseudofunctor.comp, PrelaxFunctor.mapFunctor]
    rw [whiskerLeft_comp, ← Category.assoc, ← η.naturality_naturality (F.mapId a).hom]
    simp only [Category.assoc, η.naturality_id, comp_whiskerRight]
  naturality_comp f g := by
    dsimp [Pseudofunctor.comp, PrelaxFunctor.mapFunctor]
    rw [whiskerLeft_comp, ← Category.assoc, ← η.naturality_naturality (F.mapComp f g).hom]
    simp only [Category.assoc, η.naturality_comp, comp_whiskerRight]
    rfl
/-- Associativity includes the actual mapped comparison isomorphisms. -/
theorem comp_assoc (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) (H : D ⥤ᵖ E) :
    (F.comp G).comp H = F.comp (G.comp H) := by
  refine ext (F := (F.comp G).comp H) (G := F.comp (G.comp H)) rfl ?_ ?_
  · apply heq_of_eq
    funext a
    apply Iso.ext
    change H.map₂ (G.map₂ (F.mapId a).hom ≫ (G.mapId (F.obj a)).hom) ≫
      (H.mapId (G.obj (F.obj a))).hom =
      H.map₂ (G.map₂ (F.mapId a).hom) ≫
      (H.map₂ (G.mapId (F.obj a)).hom ≫ (H.mapId (G.obj (F.obj a))).hom)
    rw [H.map₂_comp, Category.assoc]
  · apply heq_of_eq
    funext a b c f g
    apply Iso.ext
    change H.map₂ (G.map₂ (F.mapComp f g).hom ≫ (G.mapComp (F.map f) (F.map g)).hom) ≫
      (H.mapComp (G.map (F.map f)) (G.map (F.map g))).hom =
      H.map₂ (G.map₂ (F.mapComp f g).hom) ≫
      (H.map₂ (G.mapComp (F.map f) (F.map g)).hom ≫
      (H.mapComp (G.map (F.map f)) (G.map (F.map g))).hom)
    rw [H.map₂_comp, Category.assoc]
/-- The identity on the source leaves all pseudofunctor data unchanged. -/
theorem id_comp (F : B ⥤ᵖ C) : (Pseudofunctor.id B).comp F = F := by
  refine ext (F := (Pseudofunctor.id B).comp F) (G := F) rfl ?_ ?_
  · apply heq_of_eq
    funext a
    apply Iso.ext
    change F.map₂ (𝟙 _) ≫ (F.mapId a).hom = (F.mapId a).hom
    rw [F.map₂_id, Category.id_comp]
  · apply heq_of_eq
    funext a b c f g
    apply Iso.ext
    change F.map₂ (𝟙 _) ≫ (F.mapComp f g).hom = (F.mapComp f g).hom
    rw [F.map₂_id, Category.id_comp]
/-- The identity on the target leaves all pseudofunctor data unchanged. -/
theorem comp_id (F : B ⥤ᵖ C) : F.comp (Pseudofunctor.id C) = F := by
  refine ext (F := F.comp (Pseudofunctor.id C)) (G := F) rfl ?_ ?_
  · apply heq_of_eq
    funext a
    apply Iso.ext
    change (F.mapId a).hom ≫ 𝟙 _ = (F.mapId a).hom
    exact Category.comp_id _
  · apply heq_of_eq
    funext a b c f g
    apply Iso.ext
    change (F.mapComp f g).hom ≫ 𝟙 _ = (F.mapComp f g).hom
    exact Category.comp_id _
private theorem mapId_heq {F G : B ⥤ᵖ C} (h : F = G) : HEq F.mapId G.mapId := by
  cases h; rfl
private theorem mapComp_heq {F G : B ⥤ᵖ C} (h : F = G) : HEq (@F.mapComp) (@G.mapComp) := by
  cases h; rfl

/-- Normalize a target with the same underlying maps. Equality of the full
pseudofunctors is used only for laws; it does not obstruct component reduction. -/
def retarget {F G H : B ⥤ᵖ C} (η : F ⟶ G) (h : G = H)
    (hp : G.toPrelaxFunctor = H.toPrelaxFunctor) : F ⟶ H := by
  cases G
  cases H
  cases hp
  refine {
    app := η.app
    naturality := η.naturality
    naturality_naturality := η.naturality_naturality
    naturality_id := ?_
    naturality_comp := ?_ }
  · intro a
    have hi' := mapId_heq h
    have hi := eq_of_heq hi'
    dsimp only at hi
    cases hi
    exact η.naturality_id a
  · intro a b c f g
    have hc' := mapComp_heq h
    have hc := eq_of_heq hc'
    dsimp only at hc
    cases hc
    exact η.naturality_comp f g

/-- Target normalization retains the complete component. -/
theorem retarget_app {F G H : B ⥤ᵖ C} (η : F ⟶ G) (h : G = H)
    (hp : G.toPrelaxFunctor = H.toPrelaxFunctor) (a : B) :
    HEq ((retarget η h hp).app a) (η.app a) := by
  cases G; cases H; cases hp; rfl

/-- Target normalization retains the complete naturality isomorphism. -/
theorem retarget_naturality {F G H : B ⥤ᵖ C} (η : F ⟶ G) (h : G = H)
    (hp : G.toPrelaxFunctor = H.toPrelaxFunctor) {a b : B} (f : a ⟶ b) :
    HEq ((retarget η h hp).naturality f) (η.naturality f) := by
  cases G; cases H; cases hp; rfl

/-- Evaluation of transformations and modifications at an object. -/
def evaluation (F G : B ⥤ᵖ C) (a : B) : (F ⟶ G) ⥤ (F.obj a ⟶ G.obj a) where
  obj η := η.app a
  map Γ := Γ.as.app a

/-- Precomposition retains the given invertible modification components. -/
def precompIso (F : B ⥤ᵖ C) {G H : C ⥤ᵖ D} {η θ : G ⟶ H} (i : η ≅ θ) :
    precomp F η ≅ precomp F θ :=
  Pseudofunctor.StrongTrans.isoMk (fun a => (evaluation G H (F.obj a)).mapIso i)
    (fun f => i.hom.as.naturality (F.map f))
/-- Transport an invertible modification while retaining its object components. -/
def retargetIso {F G H : B ⥤ᵖ C} (h : G = H)
    (hp : G.toPrelaxFunctor = H.toPrelaxFunctor) {η θ : F ⟶ G}
    (i : ModificationIso η θ) : ModificationIso (retarget η h hp) (retarget θ h hp) := by
  cases G
  cases H
  cases hp
  exact Pseudofunctor.StrongTrans.isoMk
    (fun a => (evaluation _ _ a).mapIso i) (fun f => i.hom.as.naturality f)
end SquareKit.PseudofunctorCoherence
