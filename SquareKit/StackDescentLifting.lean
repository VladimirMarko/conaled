import SquareKit.StackDescentTransformation

/-! Lift descent data through a componentwise fully faithful transformation. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.StackDescentTransformation

open CategoryTheory Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

universe u v u₁ v₁ t
variable {C : Type u} [Category.{v} C]
variable {F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}}
variable (η : Pseudofunctor.StrongTrans F G)
variable (hη : ∀ X : C, (component η X).FullyFaithful)

/-- Inverse transport of an arrow between restricted objects. -/
def preimageHom {X₁ X₂ Y : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (h : (G.map f₁.op.toLoc).toFunctor.obj ((component η X₁).obj M₁) ⟶
      (G.map f₂.op.toLoc).toFunctor.obj ((component η X₂).obj M₂)) :
    (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂ :=
  (hη Y).preimage ((comparison η f₁).hom.app M₁ ≫ h ≫
    (comparison η f₂).inv.app M₂)

@[simp] theorem mapHom_preimageHom {X₁ X₂ Y : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (h : (G.map f₁.op.toLoc).toFunctor.obj ((component η X₁).obj M₁) ⟶
      (G.map f₂.op.toLoc).toFunctor.obj ((component η X₂).obj M₂)) :
    mapHom η f₁ f₂ (preimageHom η hη f₁ f₂ h) = h := by
  simp [mapHom, preimageHom, Category.assoc]

@[simp] theorem preimageHom_mapHom {X₁ X₂ Y : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (h : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    preimageHom η hη f₁ f₂ (mapHom η f₁ f₂ h) = h := by
  simp [mapHom, preimageHom, Category.assoc]

include hη in
theorem mapHom_injective {X₁ X₂ Y : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) :
    Function.Injective (mapHom η f₁ f₂ (M₁ := M₁) (M₂ := M₂)) :=
  Function.LeftInverse.injective (preimageHom_mapHom η hη f₁ f₂)

@[simp] theorem mapHom_map {X Y : C} (p : Y ⟶ X)
    {a b : F.obj (.mk (op X))} (k : a ⟶ b) :
    mapHom η p p ((F.map p.op.toLoc).toFunctor.map k) =
      (G.map p.op.toLoc).toFunctor.map ((component η X).map k) := by
  have hn := (comparison η p).hom.naturality k
  dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.comp_map] at hn
  simp only [mapHom]
  rw [hn]
  simp

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

set_option backward.isDefEq.respectTransparency false in
/-- Full faithfulness on fibers gives full faithfulness on descent categories. -/
def mapFullyFaithful : (map η f).FullyFaithful where
  preimage {D E} k :=
    { hom i := (hη (X i)).preimage (k.hom i)
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        apply mapHom_injective η hη f₁ f₂
        rw [← mapHom_comp η f₁ f₁ f₂, ← mapHom_comp η f₁ f₂ f₂,
          mapHom_map, mapHom_map]
        simp only [Functor.FullyFaithful.map_preimage]
        exact k.comm q f₁ f₂ hf₁ hf₂ }
  map_preimage k := by ext i; exact (hη (X i)).map_preimage _
  preimage_map k := by ext i; exact (hη (X i)).preimage_map _

/-- Replace the local objects of descent data by isomorphic local objects. -/
def transportData (D : G.DescentData f)
    (A : ∀ i, G.obj (.mk (op (X i)))) (e : ∀ i, A i ≅ D.obj i) :
    G.DescentData f where
  obj := A
  hom _ q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    (G.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫
      D.hom q f₁ f₂ hf₁ hf₂ ≫ (G.map f₂.op.toLoc).toFunctor.map (e i₂).inv
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    dsimp [pullHom]
    simp only [Functor.map_comp, Category.assoc]
    rw [← G.mapComp'_hom_naturality_assoc, G.mapComp'_inv_naturality]
    rw [← D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
    simp [pullHom, Category.assoc]
  hom_self Y q i g hg := by simp [D.hom_self q g hg]
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    simp [Category.assoc, ← Functor.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Local lifts determine the source cocycle by full faithfulness. -/
def liftData (D : G.DescentData f)
    (A : ∀ i, F.obj (.mk (op (X i))))
    (e : ∀ i, (component η (X i)).obj (A i) ≅ D.obj i) :
    F.DescentData f where
  obj := A
  hom _ q _ _ f₁ f₂ hf₁ hf₂ := preimageHom η hη f₁ f₂
    ((transportData D _ e).hom q f₁ f₂ hf₁ hf₂)
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    apply mapHom_injective η hη gf₁ gf₂
    rw [mapHom_pullHom, mapHom_preimageHom, mapHom_preimageHom]
    exact (transportData D _ e).pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  hom_self Y q i g hg := by
    apply mapHom_injective η hη g g
    rw [mapHom_preimageHom, mapHom_id]
    exact (transportData D _ e).hom_self q g hg
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    apply mapHom_injective η hη f₁ f₃
    rw [← mapHom_comp, mapHom_preimageHom, mapHom_preimageHom, mapHom_preimageHom]
    exact (transportData D _ e).hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃

set_option backward.isDefEq.respectTransparency false in
/-- The lifted cocycle recovers the original descent data, including its arrows. -/
def liftDataIso (D : G.DescentData f)
    (A : ∀ i, F.obj (.mk (op (X i))))
    (e : ∀ i, (component η (X i)).obj (A i) ≅ D.obj i) :
    (map η f).obj (liftData η hη D A e) ≅ D :=
  Pseudofunctor.DescentData.isoMk e (by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    change _ = mapHom η f₁ f₂ (preimageHom η hη f₁ f₂ _) ≫ _
    rw [mapHom_preimageHom]
    simp [transportData, Category.assoc, ← Functor.map_comp])

/-- Lift an ambient arrow between objects represented by source descent data. -/
def liftMap {D E : F.DescentData f} {b c : G.obj (.mk (op S))}
    (e : (map η f).obj D ≅ (G.toDescentData f).obj b)
    (e' : (map η f).obj E ≅ (G.toDescentData f).obj c) (h : b ⟶ c) : D ⟶ E :=
  (mapFullyFaithful η hη).preimage (e.hom ≫ (G.toDescentData f).map h ≫ e'.inv)

@[simp] theorem map_liftMap {D E : F.DescentData f} {b c : G.obj (.mk (op S))}
    (e : (map η f).obj D ≅ (G.toDescentData f).obj b)
    (e' : (map η f).obj E ≅ (G.toDescentData f).obj c) (h : b ⟶ c) :
    (map η f).map (liftMap η hη e e' h) =
      e.hom ≫ (G.toDescentData f).map h ≫ e'.inv :=
  (mapFullyFaithful η hη).map_preimage _

@[simp] theorem liftMap_id {D : F.DescentData f} {b : G.obj (.mk (op S))}
    (e : (map η f).obj D ≅ (G.toDescentData f).obj b) :
    liftMap η hη e e (𝟙 b) = 𝟙 D := by
  simp [liftMap, Functor.FullyFaithful.preimage_id]

@[reassoc] theorem liftMap_comp {D E H : F.DescentData f}
    {b c d : G.obj (.mk (op S))}
    (e : (map η f).obj D ≅ (G.toDescentData f).obj b)
    (e' : (map η f).obj E ≅ (G.toDescentData f).obj c)
    (e'' : (map η f).obj H ≅ (G.toDescentData f).obj d) (h : b ⟶ c) (k : c ⟶ d) :
    liftMap η hη e e' h ≫ liftMap η hη e' e'' k = liftMap η hη e e'' (h ≫ k) := by
  apply (mapFullyFaithful η hη).map_injective
  simp [Category.assoc]

end SquareKit.StackDescentTransformation
