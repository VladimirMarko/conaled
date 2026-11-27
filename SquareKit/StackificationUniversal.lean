import SquareKit.StackLocalGeneration
import SquareKit.StackDescentLifting

/-! Extension along fully faithful, locally generating transformations.

`universalEquivalence` identifies maps and modifications into every target stack.
`extension` constructs a strong transformation by realizing lifted local cocycles;
`extensionRecovery` recovers its restriction. The construction only assumes that
the target is a stack. For stackification, the chosen output must separately be
a stack, as in `SheafActionPresentation.universalEquivalence`.

Local presentations, common refinements and parameter comparisons prove the
coherence needed by those public interfaces without additional coherence inputs.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.StackificationUniversal

open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration

universe u v u' v' t t'
variable {C : Type u} [Category.{v} C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable (J : GrothendieckTopology C) (η : F ⟶ B)

/-- Primitive local presentation of one object by a singleton covering map. -/
structure LocalPresentation {X : C} (b : B.obj (.mk (op X))) where
  domain : C
  cover : domain ⟶ X
  covering : Sieve.ofArrows _ (fun _ : Unit => cover) ∈ J X
  object : F.obj (.mk (op domain))
  comparison : (component η domain).obj object ≅ (B.map cover.op.toLoc).toFunctor.obj b

variable {J η}

/-- Choose local presentation data from local generation. -/
def presentation (hη : LocallyGenerating J η) {X : C} (b : B.obj (.mk (op X))) :
    LocalPresentation J η b := by
  apply Classical.choice
  obtain ⟨Y, p, hp, a, ⟨e⟩⟩ := hη X b
  exact ⟨⟨Y, p, hp, a, e⟩⟩

variable {ι : Type t} {X : C} {U : ι → C} {p : ∀ i, U i ⟶ X}

/-- Stack descent, as an equivalence on the actual descent category. -/
def descentEquivalence (T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    [T.IsStack J] (hp : Sieve.ofArrows _ p ∈ J X) :
    T.obj (.mk (op X)) ≌ T.DescentData p := by
  letI := T.isEquivalence_toDescentData p hp
  exact (T.toDescentData p).asEquivalence

namespace LocalPresentation

variable (hη : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)

/-- The local presentation has a source cocycle obtained by lifting every arrow. -/
def sourceData : F.DescentData (fun _ : Unit => P.cover) :=
  liftData η hη ((B.toDescentData (fun _ : Unit => P.cover)).obj b)
    (fun _ => P.object) (fun _ => P.comparison)

/-- Mapping the source cocycle back recovers the canonical descent of the object. -/
def sourceDataIso : (map η (fun _ : Unit => P.cover)).obj (P.sourceData hη) ≅
    (B.toDescentData (fun _ : Unit => P.cover)).obj b :=
  liftDataIso η hη _ _ _

/-- Effective target value of a local presentation under a strong transformation. -/
def value (θ : F ⟶ T) [T.IsStack J] : T.obj (.mk (op X)) :=
  (descentEquivalence T P.covering).inverse.obj
    ((map θ (fun _ : Unit => P.cover)).obj (P.sourceData hη))

/-- Target effective descent recovers the image of the whole source cocycle. -/
def valueIso (θ : F ⟶ T) [T.IsStack J] :
    (T.toDescentData (fun _ : Unit => P.cover)).obj (P.value hη θ) ≅
      (map θ (fun _ : Unit => P.cover)).obj (P.sourceData hη) :=
  (descentEquivalence T P.covering).counitIso.app _

/-- For an object already in the source, the lifted cocycle is its canonical one. -/
def sourceRecovery {a : F.obj (.mk (op X))}
    (P : LocalPresentation J η ((component η X).obj a)) :
    P.sourceData hη ≅ (F.toDescentData (fun _ : Unit => P.cover)).obj a :=
  (mapFullyFaithful η hη).preimageIso
    (P.sourceDataIso hη ≪≫ (canonicalObjIso η (fun _ : Unit => P.cover) a).symm)

/-- Effective target values recover the original image of every source object. -/
def valueRecovery {a : F.obj (.mk (op X))}
    (P : LocalPresentation J η ((component η X).obj a))
    (θ : F ⟶ T) [T.IsStack J] : P.value hη θ ≅ (component θ X).obj a :=
  (T.fullyFaithfulToDescentData _ P.covering).preimageIso
    (P.valueIso hη θ ≪≫ (map θ _).mapIso (P.sourceRecovery hη) ≪≫
      canonicalObjIso θ (fun _ : Unit => P.cover) a)

end LocalPresentation

/-- Evaluate an entire source descent category in the target stack. -/
def realization (θ : F ⟶ T) [T.IsStack J]
    (hp : Sieve.ofArrows _ p ∈ J X) : F.DescentData p ⥤ T.obj (.mk (op X)) :=
  map θ p ⋙ (descentEquivalence T hp).inverse

section Refinement
variable {ι' : Type t'} {X' : C} {U' : ι' → C} {p' : ∀ i, U' i ⟶ X'}
variable {q : X' ⟶ X} {α : ι' → ι} {r : ∀ i, U' i ⟶ U (α i)}
variable (w : ∀ i, r i ≫ p (α i) = p' i ≫ q)

/-- Effective target descent commutes with change of parameter and cover. -/
def effectivePullIso [T.IsStack J]
    (hp : Sieve.ofArrows _ p ∈ J X) (hp' : Sieve.ofArrows _ p' ∈ J X') :
    (descentEquivalence T hp).inverse ⋙ (T.map q.op.toLoc).toFunctor ≅
      Pseudofunctor.DescentData.pullFunctor T w ⋙ (descentEquivalence T hp').inverse := by
  let i := Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso T w
  exact Iso.isoCompInverse (H := descentEquivalence T hp')
    (Functor.associator _ _ _ ≪≫
      Iso.inverseCompIso (G := descentEquivalence T hp) i.symm)

/-- Evaluating a source cocycle commutes with arbitrary parameter substitution
and cover refinement. -/
def realizationPullIso (θ : F ⟶ T) [T.IsStack J]
    (hp : Sieve.ofArrows _ p ∈ J X) (hp' : Sieve.ofArrows _ p' ∈ J X') :
    Pseudofunctor.DescentData.pullFunctor F w ⋙ realization θ hp' ≅
      realization θ hp ⋙ (T.map q.op.toLoc).toFunctor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullIso θ p w) (descentEquivalence T hp').inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (map θ p) (effectivePullIso w hp hp').symm ≪≫
    (Functor.associator _ _ _).symm

/-- Refined lifted descent data still recover the restricted ambient object. -/
def pullSourceIso
    {b : B.obj (.mk (op X))} (D : F.DescentData p)
    (e : (map η p).obj D ≅ (B.toDescentData p).obj b) :
    (map η p').obj ((Pseudofunctor.DescentData.pullFunctor F w).obj D) ≅
      (B.toDescentData p').obj ((B.map q.op.toLoc).toFunctor.obj b) :=
  (pullIso η p w).app D ≪≫
    (Pseudofunctor.DescentData.pullFunctor B w).mapIso e ≪≫
    (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso B w).app b

end Refinement

namespace LocalPresentation
variable (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable {R : C} (r : R ⟶ P.domain) (k : R ⟶ X) (hr : r ≫ P.cover = k)

/-- Restrict the source cocycle to a finer singleton cover. -/
abbrev refinement : F.DescentData (fun _ : Unit => P.cover) ⥤
    F.DescentData (fun _ : Unit => k) :=
  Pseudofunctor.DescentData.pullFunctor F (p := 𝟙 X) (α := fun _ : Unit => ())
    (p' := fun _ => r) (fun _ => hr.trans (Category.comp_id k).symm)

/-- A refined source cocycle continues to represent the original ambient object. -/
def refinedSourceIso :
    (map η (fun _ : Unit => k)).obj ((P.refinement r k hr).obj (P.sourceData hFF)) ≅
      (B.toDescentData (fun _ : Unit => k)).obj b :=
  pullSourceIso (p := fun _ : Unit => P.cover) (q := 𝟙 X)
    (α := fun _ : Unit => ()) (r := fun _ => r)
    (fun _ => hr.trans (Category.comp_id k).symm) (P.sourceData hFF) (P.sourceDataIso hFF) ≪≫
    (B.toDescentData (fun _ : Unit => k)).mapIso
      ((Cat.Hom.toNatIso (B.mapId (.mk (op X)))).app b)

/-- The effective target value is unchanged, up to the specified isomorphism,
when the presentation is restricted to a finer cover. -/
def refinedValueIso (θ : F ⟶ T) [T.IsStack J]
    (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X) :
    (realization θ hk).obj ((P.refinement r k hr).obj (P.sourceData hFF)) ≅
      P.value hFF θ :=
  (realizationPullIso (p := fun _ : Unit => P.cover) (q := 𝟙 X)
    (α := fun _ : Unit => ()) (r := fun _ => r)
    (fun _ => hr.trans (Category.comp_id k).symm) θ P.covering hk).app (P.sourceData hFF) ≪≫
    (Cat.Hom.toNatIso (T.mapId (.mk (op X)))).app (P.value hFF θ)

variable {c : B.obj (.mk (op X))} (Q : LocalPresentation J η c)
variable (s : R ⟶ Q.domain) (hs : s ≫ Q.cover = k)

/-- Evaluate an ambient arrow after lifting it on a common covering refinement. -/
def mapOnRefinement (θ : F ⟶ T) [T.IsStack J]
    (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X) (h : b ⟶ c) :
    P.value hFF θ ⟶ Q.value hFF θ :=
  (P.refinedValueIso hFF r k hr θ hk).inv ≫
    (realization θ hk).map (liftMap η hFF
      (P.refinedSourceIso hFF r k hr) (Q.refinedSourceIso hFF s k hs) h) ≫
    (Q.refinedValueIso hFF s k hs θ hk).hom

end LocalPresentation

/-- The object part of extension, chosen by local generation and target descent. -/
def extensionObj (hFF : ∀ X : C, (component η X).FullyFaithful)
    (hη : LocallyGenerating J η) (θ : F ⟶ T) [T.IsStack J]
    {X : C} (b : B.obj (.mk (op X))) : T.obj (.mk (op X)) :=
  (presentation hη b).value hFF θ

/-- The object extension agrees with the given transformation on source objects. -/
def extensionObjRecovery (hFF : ∀ X : C, (component η X).FullyFaithful)
    (hη : LocallyGenerating J η) (θ : F ⟶ T) [T.IsStack J]
    {X : C} (a : F.obj (.mk (op X))) :
    extensionObj hFF hη θ ((component η X).obj a) ≅ (component θ X).obj a :=
  (presentation hη ((component η X).obj a)).valueRecovery hFF θ

/-- If the source is already a stack, local generation gives recovery on
whole fibers, rather than only after a cover. -/
def alreadyStackEquivalence
    (hFF : ∀ X : C, (component η X).FullyFaithful)
    (hη : LocallyGenerating J η) [F.IsStack J] [B.IsPrestack J] (X : C) :
    F.obj (.mk (op X)) ≌ B.obj (.mk (op X)) := by
  letI := (hFF X).full
  letI := (hFF X).faithful
  letI : (component η X).EssSurj := ⟨fun b => by
    let P := presentation hη b
    let E := descentEquivalence F P.covering
    let x := E.inverse.obj (P.sourceData hFF)
    refine ⟨x, ⟨(B.fullyFaithfulToDescentData _ P.covering).preimageIso ?_⟩⟩
    exact (canonicalObjIso η (fun _ : Unit => P.cover) x).symm ≪≫
      (map η _).mapIso (E.counitIso.app (P.sourceData hFF)) ≪≫ P.sourceDataIso hFF⟩
  letI : (component η X).IsEquivalence := {}
  exact (component η X).asEquivalence

end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v'
variable {C : Type u} [Category.{v} C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable {X : C} {b c : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable {R : C} (r : R ⟶ P.domain) (k : R ⟶ X) (hr : r ≫ P.cover = k)
variable {R' : C} (l : R' ⟶ R) (k' : R' ⟶ X) (hl : l ≫ k = k')
def compRefinementIso (H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) :
    Pseudofunctor.DescentData.pullFunctor H (p := 𝟙 X) (f := fun _ : Unit => P.cover)
      (f' := fun _ : Unit => k) (p' := fun _ => r) (α := fun _ => ())
      (fun _ => hr.trans (Category.comp_id k).symm) ⋙
    Pseudofunctor.DescentData.pullFunctor H (p := 𝟙 X) (f := fun _ : Unit => k)
      (f' := fun _ : Unit => k') (p' := fun _ => l) (α := fun _ => ())
      (fun _ => hl.trans (Category.comp_id k').symm) ≅
    Pseudofunctor.DescentData.pullFunctor H (p := 𝟙 X) (f := fun _ : Unit => P.cover)
      (f' := fun _ : Unit => k') (p' := fun _ => l ≫ r) (α := fun _ => ())
      (fun _ => by simp [Category.assoc, hr, hl]) :=
  Pseudofunctor.DescentData.pullFunctorCompIso H
    (f := fun _ : Unit => P.cover) (f' := fun _ : Unit => k)
    (f'' := fun _ : Unit => k') (p := 𝟙 X) (q := 𝟙 X)
    (α := fun _ : Unit => ()) (β := fun _ : Unit => ())
    (p' := fun _ => r) (q' := fun _ => l) (r' := fun _ => l ≫ r)
    (fun _ => hr.trans (Category.comp_id k).symm)
    (fun _ => hl.trans (Category.comp_id k').symm) (𝟙 X) (Category.id_comp _) (fun _ => rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem pullIso_comp_refinement (θ : F ⟶ T) (D : F.DescentData (fun _ : Unit => P.cover)) :
  (pullIso θ (fun _ : Unit => k)
    (p := 𝟙 X) (f' := fun _ : Unit => k') (p' := fun _ : Unit => l) (α := fun _ => ())
    (fun _ => hl.trans (Category.comp_id k').symm)).app
      ((P.refinement r k hr).obj D) ≪≫
  (Pseudofunctor.DescentData.pullFunctor T (p := 𝟙 X)
    (f := fun _ : Unit => k) (f' := fun _ : Unit => k')
    (p' := fun _ : Unit => l) (α := fun _ => ())
    (fun _ => hl.trans (Category.comp_id k').symm)).mapIso
      ((pullIso θ (fun _ : Unit => P.cover)
        (p := 𝟙 X) (f' := fun _ : Unit => k) (p' := fun _ : Unit => r) (α := fun _ => ())
        (fun _ => hr.trans (Category.comp_id k).symm)).app D) =
  (map θ (fun _ : Unit => k')).mapIso ((compRefinementIso P r k hr l k' hl F).app D) ≪≫
  (pullIso θ (fun _ : Unit => P.cover) (p := 𝟙 X)
    (f' := fun _ : Unit => k') (p' := fun _ : Unit => l ≫ r) (α := fun _ => ())
    (fun _ => by simp [Category.assoc, hr, hl])).app D ≪≫
  ((compRefinementIso P r k hr l k' hl T).app ((map θ (fun _ : Unit => P.cover)).obj D)).symm := by
  ext i
  cases i
  have hc := comparison_comp_hom θ r l (l ≫ r) rfl (D.obj ())
  dsimp [pullIso, pullObjIso, compRefinementIso,
    Pseudofunctor.DescentData.pullFunctorCompIso] at *
  dsimp [map, mapMap, mapObj, refinement,
    Pseudofunctor.DescentData.pullFunctor, Pseudofunctor.DescentData.pullFunctorObj, Pseudofunctor.DescentData.isoMk]
  simp only [Pseudofunctor.mapComp'_eq_mapComp, Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv] at *
  rw [hc]
  simp only [← Functor.map_comp_assoc, ← Cat.Hom.toNatIso_hom, ← Cat.Hom.toNatIso_inv,
    Iso.inv_hom_id_app]
  simp
end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X R : C} {b c d : B.obj (.mk (op X))}
variable (P : LocalPresentation J η b) (Q : LocalPresentation J η c)
  (H : LocalPresentation J η d)
variable (r : R ⟶ P.domain) (s : R ⟶ Q.domain) (t : R ⟶ H.domain) (k : R ⟶ X)
  (hr : r ≫ P.cover = k) (hs : s ≫ Q.cover = k) (ht : t ≫ H.cover = k)
variable (θ : F ⟶ T) [T.IsStack J]
  (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X)

@[simp] theorem mapOnRefinement_id :
    P.mapOnRefinement hFF r k hr P r hr θ hk (𝟙 b) = 𝟙 (P.value hFF θ) := by
  simp [mapOnRefinement]

@[reassoc] theorem mapOnRefinement_comp (h : b ⟶ c) (l : c ⟶ d) :
    P.mapOnRefinement hFF r k hr Q s hs θ hk h ≫
      Q.mapOnRefinement hFF s k hs H t ht θ hk l =
    P.mapOnRefinement hFF r k hr H t ht θ hk (h ≫ l) := by
  simp only [mapOnRefinement, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, liftMap_comp]

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v' t t'
variable {C : Type u} [Category.{v} C]
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable (η : F ⟶ B) (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {ι : Type t} {X : C} {U : ι → C} {p : ∀ i, U i ⟶ X}
variable {ι' : Type t'} {X' : C} {U' : ι' → C} {p' : ∀ i, U' i ⟶ X'}
variable {q : X' ⟶ X} {α : ι' → ι} {r : ∀ i, U' i ⟶ U (α i)}
variable (w : ∀ i, r i ≫ p (α i) = p' i ≫ q)
variable {b c : B.obj (.mk (op X))} (D E : F.DescentData p)
variable (e : (map η p).obj D ≅ (B.toDescentData p).obj b)
variable (e' : (map η p).obj E ≅ (B.toDescentData p).obj c)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem liftMap_pull (h : b ⟶ c) :
    (Pseudofunctor.DescentData.pullFunctor F w).map (liftMap η hFF e e' h) =
      liftMap η hFF (pullSourceIso w D e) (pullSourceIso w E e')
        ((B.map q.op.toLoc).toFunctor.map h) := by
  apply (mapFullyFaithful η hFF).map_injective
  have hn := (pullIso η p w).hom.naturality (liftMap η hFF e e' h)
  have hc := (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso B w).hom.naturality h
  dsimp only [Functor.comp_map] at hn hc
  rw [← cancel_mono ((pullIso η p w).hom.app E)]
  rw [hn]
  simp only [map_liftMap, pullSourceIso, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [← reassoc_of% hc]
  simp only [Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.map_comp]
end SquareKit.StackificationUniversal

namespace SquareKit.StackDescentTransformation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v u' v' t t'
variable {C : Type u} [Category.{v} C]
variable {F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable (η : F ⟶ G)
variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
variable {ι' : Type t'} {S' : C} {X' : ι' → C} {f' : ∀ i, X' i ⟶ S'}
variable {p : S' ⟶ S} {α β : ι' → ι} {r : ∀ i, X' i ⟶ X (α i)}
  {s : ∀ i, X' i ⟶ X (β i)}
variable (w : ∀ i, r i ≫ f (α i) = f' i ≫ p)
  (w' : ∀ i, s i ≫ f (β i) = f' i ≫ p)

set_option backward.isDefEq.respectTransparency false in
theorem pullIso_change (D : F.DescentData f) :
    (map η f').map ((Pseudofunctor.DescentData.pullFunctorIso F w w').hom.app D) ≫
      (pullIso η f w').hom.app D =
    (pullIso η f w).hom.app D ≫
      (Pseudofunctor.DescentData.pullFunctorIso G w w').hom.app ((map η f).obj D) := by
  ext i
  dsimp [map, mapMap, mapObj, pullIso, pullObjIso,
    Pseudofunctor.DescentData.pullFunctorIso, Pseudofunctor.DescentData.iso, mapHom]
  simp

end SquareKit.StackDescentTransformation

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
universe u v u' v' t t'
variable {C : Type u} [Category.{v} C]
variable (T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
variable {ι' : Type t'} {S' : C} {X' : ι' → C} {f' : ∀ i, X' i ⟶ S'}
variable {p : S' ⟶ S} {α β : ι' → ι} {r : ∀ i, X' i ⟶ X (α i)}
  {s : ∀ i, X' i ⟶ X (β i)}
variable (w : ∀ i, r i ≫ f (α i) = f' i ≫ p)
  (w' : ∀ i, s i ≫ f (β i) = f' i ≫ p)

set_option backward.isDefEq.respectTransparency false in
theorem canonicalPullIso_change (b : T.obj (.mk (op S))) :
    (Pseudofunctor.DescentData.pullFunctorIso T w w').hom.app ((T.toDescentData f).obj b) ≫
      (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso T w').hom.app b =
    (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso T w).hom.app b := by
  ext i
  dsimp [Pseudofunctor.DescentData.pullFunctorIso,
    Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso,
    Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj,
    Pseudofunctor.DescentData.iso, Pseudofunctor.DescentData.isoMk]
  have hw : (f (α i)).op.toLoc ≫ (r i).op.toLoc =
      p.op.toLoc ≫ (f' i).op.toLoc := by
    simpa using congrArg (fun k => k.op.toLoc) (w i)
  rw [T.isoMapOfCommSq_eq _ _ hw.symm, T.isoMapOfCommSq_eq _ _ hw.symm]
  simp

variable {J : GrothendieckTopology C} [T.IsStack J]

set_option backward.isDefEq.respectTransparency false in
theorem effectivePullIso_change
    (hf : Sieve.ofArrows _ f ∈ J S) (hf' : Sieve.ofArrows _ f' ∈ J S')
    (D : T.DescentData f) :
    (effectivePullIso w hf hf').hom.app D ≫
      (descentEquivalence T hf').inverse.map
        ((Pseudofunctor.DescentData.pullFunctorIso T w w').hom.app D) =
      (effectivePullIso w' hf hf').hom.app D := by
  dsimp [effectivePullIso, Iso.isoCompInverse, Iso.inverseCompIso]
  simp only [Category.id_comp, Category.comp_id, Category.assoc, ← Functor.map_comp]
  rw [(Pseudofunctor.DescentData.pullFunctorIso T w w').hom.naturality]
  simp only [← Category.assoc]
  congr 2
  have hc := canonicalPullIso_change T f w w'
    ((descentEquivalence T hf).inverse.obj D)
  congr 1
  exact (Iso.inv_comp_eq _).mpr ((Iso.eq_comp_inv _).mpr hc)

end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v' t t'
variable {C : Type u} [Category.{v} C]
variable {F T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable (θ : F ⟶ T)
variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
variable {ι' : Type t'} {S' : C} {X' : ι' → C} {f' : ∀ i, X' i ⟶ S'}
variable {p : S' ⟶ S} {α β : ι' → ι} {r : ∀ i, X' i ⟶ X (α i)}
  {s : ∀ i, X' i ⟶ X (β i)}
variable (w : ∀ i, r i ≫ f (α i) = f' i ≫ p)
  (w' : ∀ i, s i ≫ f (β i) = f' i ≫ p)
variable {J : GrothendieckTopology C} [T.IsStack J]

set_option backward.isDefEq.respectTransparency false in
theorem realizationPullIso_change
    (hf : Sieve.ofArrows _ f ∈ J S) (hf' : Sieve.ofArrows _ f' ∈ J S')
    (D : F.DescentData f) :
    (realization θ hf').map ((Pseudofunctor.DescentData.pullFunctorIso F w w').hom.app D) ≫
      (realizationPullIso w' θ hf hf').hom.app D =
    (realizationPullIso w θ hf hf').hom.app D := by
  dsimp [realizationPullIso, realization]
  simp only [Category.id_comp, Category.comp_id]
  rw [← Functor.map_comp_assoc, pullIso_change θ f w w', Functor.map_comp, Category.assoc]
  congr 1
  apply (cancel_epi ((effectivePullIso w hf hf').hom.app ((map θ f).obj D))).mp
  rw [← Category.assoc, effectivePullIso_change T f w w']
  simp

end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable {R : C} (r s : R ⟶ P.domain) (k : R ⟶ X)
  (hr : r ≫ P.cover = k) (hs : s ≫ P.cover = k)
variable (θ : F ⟶ T) [T.IsStack J]

set_option backward.isDefEq.respectTransparency false in
def refinementChange : P.refinement r k hr ≅ P.refinement s k hs :=
  Pseudofunctor.DescentData.pullFunctorIso F (p := 𝟙 X) (f := fun _ : Unit => P.cover) (f' := fun _ : Unit => k)
    (α := fun _ : Unit => ()) (β := fun _ : Unit => ())
    (p' := fun _ => r) (p'' := fun _ => s)
    (fun _ => hr.trans (Category.comp_id k).symm)
    (fun _ => hs.trans (Category.comp_id k).symm)

set_option backward.isDefEq.respectTransparency false in
theorem refinedValueIso_change (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X) :
    (realization θ hk).map ((P.refinementChange r s k hr hs).hom.app (P.sourceData hFF)) ≫
      (P.refinedValueIso hFF s k hs θ hk).hom =
    (P.refinedValueIso hFF r k hr θ hk).hom := by
  dsimp [refinedValueIso]
  rw [← Category.assoc]
  congr 1
  exact realizationPullIso_change (J := J) θ _ _ _ P.covering hk (P.sourceData hFF)

end SquareKit.StackificationUniversal.LocalPresentation
namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v' t t'
variable {C : Type u} [Category.{v} C]
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B}
variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
variable {ι' : Type t'} {S' : C} {X' : ι' → C} {f' : ∀ i, X' i ⟶ S'}
variable {p : S' ⟶ S} {α β : ι' → ι} {r : ∀ i, X' i ⟶ X (α i)}
  {s : ∀ i, X' i ⟶ X (β i)}
variable (w : ∀ i, r i ≫ f (α i) = f' i ≫ p)
  (w' : ∀ i, s i ≫ f (β i) = f' i ≫ p)

set_option backward.isDefEq.respectTransparency false in
theorem pullSourceIso_change {b : B.obj (.mk (op S))} (D : F.DescentData f)
    (e : (map η f).obj D ≅ (B.toDescentData f).obj b) :
    (map η f').map ((Pseudofunctor.DescentData.pullFunctorIso F w w').hom.app D) ≫
      (pullSourceIso w' D e).hom = (pullSourceIso w D e).hom := by
  simp only [pullSourceIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc, pullIso_change]
  simp only [Category.assoc]
  rw [← (Pseudofunctor.DescentData.pullFunctorIso B w w').hom.naturality_assoc]
  rw [canonicalPullIso_change]

end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable {R : C} (r s : R ⟶ P.domain) (k : R ⟶ X)
  (hr : r ≫ P.cover = k) (hs : s ≫ P.cover = k)

set_option backward.isDefEq.respectTransparency false in
theorem refinedSourceIso_change :
    (map η (fun _ : Unit => k)).map
        ((P.refinementChange r s k hr hs).hom.app (P.sourceData hFF)) ≫
      (P.refinedSourceIso hFF s k hs).hom =
    (P.refinedSourceIso hFF r k hr).hom := by
  dsimp [refinedSourceIso]
  rw [← Category.assoc]
  congr 1
  exact pullSourceIso_change _ _ _ (P.sourceData hFF) (P.sourceDataIso hFF)

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {b c : B.obj (.mk (op X))}
variable (P : LocalPresentation J η b) (Q : LocalPresentation J η c)
variable {R : C} (r r' : R ⟶ P.domain) (s s' : R ⟶ Q.domain) (k : R ⟶ X)
  (hr : r ≫ P.cover = k) (hr' : r' ≫ P.cover = k)
  (hs : s ≫ Q.cover = k) (hs' : s' ≫ Q.cover = k)

set_option backward.isDefEq.respectTransparency false in
theorem liftMap_change (h : b ⟶ c) :
    (P.refinementChange r r' k hr hr').hom.app (P.sourceData hFF) ≫
      liftMap η hFF (P.refinedSourceIso hFF r' k hr') (Q.refinedSourceIso hFF s' k hs') h =
    liftMap η hFF (P.refinedSourceIso hFF r k hr) (Q.refinedSourceIso hFF s k hs) h ≫
      (Q.refinementChange s s' k hs hs').hom.app (Q.sourceData hFF) := by
  apply (mapFullyFaithful η hFF).map_injective
  simp only [Functor.map_comp, map_liftMap]
  apply (cancel_mono (Q.refinedSourceIso hFF s' k hs').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Q.refinedSourceIso_change hFF s s' k hs hs']
  simp only [Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, P.refinedSourceIso_change hFF r r' k hr hr']

variable (θ : F ⟶ T) [T.IsStack J]
set_option backward.isDefEq.respectTransparency false in
theorem mapOnRefinement_change
    (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X) (h : b ⟶ c) :
    P.mapOnRefinement hFF r k hr Q s hs θ hk h =
      P.mapOnRefinement hFF r' k hr' Q s' hs' θ hk h := by
  apply (cancel_epi (P.refinedValueIso hFF r k hr θ hk).hom).mp
  simp only [mapOnRefinement, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← P.refinedValueIso_change hFF r r' k hr hr' θ hk]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, P.liftMap_change hFF Q r r' s s' k hr hr' hs hs']
  rw [Functor.map_comp, Category.assoc, Q.refinedValueIso_change hFF s s' k hs hs' θ hk]

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
universe u v u' v'
variable {C : Type u} [Category.{v} C]
variable (H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
variable {X Y R : C} (f : Y ⟶ X) (r : R ⟶ Y) (k : R ⟶ X) (hr : r ≫ f = k)

def canonicalRefinementIso :
    H.toDescentData (fun _ : Unit => f) ⋙
      Pseudofunctor.DescentData.pullFunctor H (p := 𝟙 X)
        (f' := fun _ : Unit => k) (α := fun _ : Unit => ()) (p' := fun _ => r)
        (fun _ => hr.trans (Category.comp_id k).symm) ≅
      H.toDescentData (fun _ : Unit => k) :=
  Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso H
    (fun _ => hr.trans (Category.comp_id k).symm) ≪≫
    Functor.isoWhiskerRight (Cat.Hom.toNatIso (H.mapId (.mk (op X))))
      (H.toDescentData (fun _ : Unit => k)) ≪≫
    (H.toDescentData (fun _ : Unit => k)).leftUnitor

set_option backward.isDefEq.respectTransparency false in
theorem canonicalRefinementIso_hom (b : H.obj (.mk (op X))) :
    ((canonicalRefinementIso H f r k hr).hom.app b).hom () =
      (H.mapComp' f.op.toLoc r.op.toLoc k.op.toLoc (by simpa using congrArg (fun g => g.op.toLoc) hr)).inv.toNatTrans.app b := by
  dsimp [canonicalRefinementIso,
    Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso,
    Pseudofunctor.DescentData.isoMk]
  rw [H.isoMapOfCommSq_eq _ k.op.toLoc (by simp)]
  simp [Pseudofunctor.toDescentData, Pseudofunctor.mapComp'_id_comp_hom_app,
    ← Functor.map_comp]

end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v'
variable {C : Type u} [Category.{v} C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable {X : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable {R : C} (r : R ⟶ P.domain) (k : R ⟶ X) (hr : r ≫ P.cover = k)
variable {R' : C} (l : R' ⟶ R) (k' : R' ⟶ X) (hl : l ≫ k = k')
variable (H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem canonicalRefinementIso_comp (a : H.obj (.mk (op X))) :
    (Pseudofunctor.DescentData.pullFunctor H (p := 𝟙 X)
      (f := fun _ : Unit => k) (f' := fun _ : Unit => k')
      (p' := fun _ : Unit => l) (α := fun _ => ())
      (fun _ => hl.trans (Category.comp_id k').symm)).map
        ((canonicalRefinementIso H P.cover r k hr).hom.app a) ≫
      (canonicalRefinementIso H k l k' hl).hom.app a =
    ((P.compRefinementIso r k hr l k' hl H).hom.app
      ((H.toDescentData (fun _ : Unit => P.cover)).obj a)) ≫
      (canonicalRefinementIso H P.cover (l ≫ r) k'
        (by rw [Category.assoc, hr, hl])).hom.app a := by
  ext i
  cases i
  change (H.map l.op.toLoc).toFunctor.map
      (((canonicalRefinementIso H P.cover r k hr).hom.app a).hom ()) ≫
      ((canonicalRefinementIso H k l k' hl).hom.app a).hom () = _
  rw [canonicalRefinementIso_hom, canonicalRefinementIso_hom]
  simp only [Pseudofunctor.DescentData.comp_hom, canonicalRefinementIso_hom]
  dsimp [compRefinementIso, Pseudofunctor.DescentData.pullFunctorCompIso,
    Pseudofunctor.DescentData.isoMk, Pseudofunctor.toDescentData,
    Pseudofunctor.DescentData.ofObj]
  simpa using H.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app
    P.cover.op.toLoc r.op.toLoc l.op.toLoc k.op.toLoc (l ≫ r).op.toLoc k'.op.toLoc
    (by simpa using congrArg (fun g => g.op.toLoc) hr) rfl
    (by simpa using congrArg (fun g => g.op.toLoc) hl) a

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable {R : C} (r : R ⟶ P.domain) (k : R ⟶ X) (hr : r ≫ P.cover = k)
variable {R' : C} (l : R' ⟶ R) (k' : R' ⟶ X) (hl : l ≫ k = k')

set_option backward.isDefEq.respectTransparency false in
theorem refinedSourceIso_hom :
    (P.refinedSourceIso hFF r k hr).hom =
      (pullIso η (fun _ : Unit => P.cover) (p := 𝟙 X)
        (f' := fun _ : Unit => k) (p' := fun _ => r) (α := fun _ => ())
        (fun _ => hr.trans (Category.comp_id k).symm)).hom.app (P.sourceData hFF) ≫
      (Pseudofunctor.DescentData.pullFunctor B (p := 𝟙 X)
        (f := fun _ : Unit => P.cover) (f' := fun _ : Unit => k)
        (p' := fun _ => r) (α := fun _ => ())
        (fun _ => hr.trans (Category.comp_id k).symm)).map (P.sourceDataIso hFF).hom ≫
      (canonicalRefinementIso B P.cover r k hr).hom.app b := by
  simp [refinedSourceIso, pullSourceIso, canonicalRefinementIso]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem refinedSourceIso_comp :
    (pullIso η (fun _ : Unit => k) (p := 𝟙 X)
      (f' := fun _ : Unit => k') (p' := fun _ => l) (α := fun _ => ())
      (fun _ => hl.trans (Category.comp_id k').symm)).hom.app
        ((P.refinement r k hr).obj (P.sourceData hFF)) ≫
    (Pseudofunctor.DescentData.pullFunctor B (p := 𝟙 X)
      (f := fun _ : Unit => k) (f' := fun _ : Unit => k')
      (p' := fun _ => l) (α := fun _ => ())
      (fun _ => hl.trans (Category.comp_id k').symm)).map
        (P.refinedSourceIso hFF r k hr).hom ≫
      (canonicalRefinementIso B k l k' hl).hom.app b =
    (map η (fun _ : Unit => k')).map
      ((P.compRefinementIso r k hr l k' hl F).hom.app (P.sourceData hFF)) ≫
      (P.refinedSourceIso hFF (l ≫ r) k' (by rw [Category.assoc, hr, hl])).hom := by
  rw [P.refinedSourceIso_hom hFF r k hr, P.refinedSourceIso_hom hFF (l ≫ r) k']
  simp only [Functor.map_comp, ← Category.assoc]
  have hc := congrArg Iso.hom (P.pullIso_comp_refinement r k hr l k' hl η (P.sourceData hFF))
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv] at hc
  rw [hc]
  simp only [Category.assoc]
  rw [P.canonicalRefinementIso_comp r k hr l k' hl B b]
  have hn := (P.compRefinementIso r k hr l k' hl B).inv.naturality (P.sourceDataIso hFF).hom
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  simp

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {b c : B.obj (.mk (op X))}
variable (P : LocalPresentation J η b) (Q : LocalPresentation J η c)
variable {R : C} (r : R ⟶ P.domain) (s : R ⟶ Q.domain) (k : R ⟶ X)
  (hr : r ≫ P.cover = k) (hs : s ≫ Q.cover = k)
variable {R' : C} (l : R' ⟶ R) (k' : R' ⟶ X) (hl : l ≫ k = k')

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem liftMap_refinement (h : b ⟶ c) :
    (P.compRefinementIso r k hr l k' hl F).hom.app (P.sourceData hFF) ≫
      liftMap η hFF
        (P.refinedSourceIso hFF (l ≫ r) k' (by rw [Category.assoc, hr, hl]))
        (Q.refinedSourceIso hFF (l ≫ s) k' (by rw [Category.assoc, hs, hl])) h =
    (Pseudofunctor.DescentData.pullFunctor F (p := 𝟙 X)
      (f := fun _ : Unit => k) (f' := fun _ : Unit => k')
      (p' := fun _ => l) (α := fun _ => ())
      (fun _ => hl.trans (Category.comp_id k').symm)).map
        (liftMap η hFF (P.refinedSourceIso hFF r k hr) (Q.refinedSourceIso hFF s k hs) h) ≫
      (Q.compRefinementIso s k hs l k' hl F).hom.app (Q.sourceData hFF) := by
  apply (mapFullyFaithful η hFF).map_injective
  simp only [Functor.map_comp, map_liftMap]
  apply (cancel_mono (Q.refinedSourceIso hFF (l ≫ s) k'
    (by rw [Category.assoc, hs, hl])).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Q.refinedSourceIso_comp hFF s k hs l k' hl]
  rw [← Category.assoc, ← P.refinedSourceIso_comp hFF r k hr l k' hl]
  have hn := (pullIso η (fun _ : Unit => k) (p := 𝟙 X)
    (f' := fun _ : Unit => k') (p' := fun _ => l) (α := fun _ => ())
    (fun _ => hl.trans (Category.comp_id k').symm)).hom.naturality
      (liftMap η hFF (P.refinedSourceIso hFF r k hr) (Q.refinedSourceIso hFF s k hs) h)
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [reassoc_of% hn, map_liftMap, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc _ (Q.refinedSourceIso hFF s k hs).inv (Q.refinedSourceIso hFF s k hs).hom]
  simp only [Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have hc := (canonicalRefinementIso B k l k' hl).hom.naturality h
  dsimp only [Functor.comp_map] at hc
  rw [hc]

end SquareKit.StackificationUniversal.LocalPresentation

namespace CategoryTheory
universe u v u₀ v₀ u₁ v₁ u₂ v₂
variable {A : Type u} [Category.{v} A]
variable {D₀ : Type u₀} [Category.{v₀} D₀]
variable {D₁ : Type u₁} [Category.{v₁} D₁]
variable {D₂ : Type u₂} [Category.{v₂} D₂]
variable (E₀ : A ≌ D₀) (E₁ : A ≌ D₁) (E₂ : A ≌ D₂)
variable (R₀₁ : D₀ ⥤ D₁) (R₁₂ : D₁ ⥤ D₂) (R₀₂ : D₀ ⥤ D₂)
variable (i₀₁ : E₀.functor ⋙ R₀₁ ≅ E₁.functor)
variable (i₁₂ : E₁.functor ⋙ R₁₂ ≅ E₂.functor)
variable (i₀₂ : E₀.functor ⋙ R₀₂ ≅ E₂.functor)

def inverseSquare : R₀₁ ⋙ E₁.inverse ≅ E₀.inverse :=
  (Iso.isoCompInverse (H := E₁) (Iso.inverseCompIso (G := E₀) i₀₁.symm)).symm

@[reassoc] theorem inverseSquare_spec (d : D₀) :
    E₁.counitIso.inv.app (R₀₁.obj d) ≫ E₁.functor.map ((inverseSquare E₀ E₁ R₀₁ i₀₁).hom.app d) =
      R₀₁.map (E₀.counitIso.inv.app d) ≫ i₀₁.hom.app (E₀.inverse.obj d) := by
  dsimp [inverseSquare, Iso.isoCompInverse, Iso.inverseCompIso]
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  rw [← E₁.counit_app_functor]
  simp [Equivalence.fun_inv_map, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem inverseSquare_comp (c : R₀₁ ⋙ R₁₂ ≅ R₀₂)
    (hc : ∀ x : A, R₁₂.map (i₀₁.hom.app x) ≫ i₁₂.hom.app x =
      c.hom.app (E₀.functor.obj x) ≫ i₀₂.hom.app x) (d : D₀) :
    (inverseSquare E₁ E₂ R₁₂ i₁₂).hom.app (R₀₁.obj d) ≫
      (inverseSquare E₀ E₁ R₀₁ i₀₁).hom.app d =
    E₂.inverse.map (c.hom.app d) ≫ (inverseSquare E₀ E₂ R₀₂ i₀₂).hom.app d := by
  apply E₂.functor.map_injective
  apply (cancel_epi (E₂.counitIso.inv.app (R₁₂.obj (R₀₁.obj d)))).mp
  simp only [Functor.map_comp]
  rw [inverseSquare_spec_assoc]
  simp only [Equivalence.fun_inv_map, Category.assoc, Equivalence.counit, Equivalence.counitInv]
  rw [inverseSquare_spec]
  rw [← i₁₂.hom.naturality]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, inverseSquare_spec]
  rw [Functor.map_comp, Category.assoc, hc]
  have hn := c.hom.naturality (E₀.counitIso.inv.app d)
  dsimp at hn
  rw [← Category.assoc, hn]
  simp [Functor.comp_obj]


variable (L : A ⥤ A) (l : L ≅ 𝟭 A) (j : E₀.functor ⋙ R₀₁ ≅ L ⋙ E₁.functor)

def normalizedSquare : E₀.functor ⋙ R₀₁ ≅ E₁.functor :=
  j ≪≫ Functor.isoWhiskerRight l E₁.functor ≪≫ E₁.functor.leftUnitor

def inverseSquareOver : R₀₁ ⋙ E₁.inverse ≅ E₀.inverse ⋙ L :=
  (Iso.isoCompInverse (H := E₁) (Functor.associator _ _ _ ≪≫
    Iso.inverseCompIso (G := E₀) j.symm)).symm

theorem inverseSquare_normalize (d : D₀) :
    (inverseSquare E₀ E₁ R₀₁ (normalizedSquare E₀ E₁ R₀₁ L l j)).hom.app d =
      (inverseSquareOver E₀ E₁ R₀₁ L j).hom.app d ≫ l.hom.app (E₀.inverse.obj d) := by
  dsimp [inverseSquare, normalizedSquare, inverseSquareOver, Iso.isoCompInverse, Iso.inverseCompIso]
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  have hn := E₁.unitIso.inv.naturality (l.hom.app (E₀.inverse.obj d))
  dsimp at hn
  rw [hn]

end CategoryTheory

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) [T.IsStack J]
variable {X Y R : C} (f : Y ⟶ X) (r : R ⟶ Y) (k : R ⟶ X) (hr : r ≫ f = k)
variable (hf : Sieve.ofArrows _ (fun _ : Unit => f) ∈ J X)
  (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X)

set_option backward.isDefEq.respectTransparency false in
def effectiveRefinementIso :
    Pseudofunctor.DescentData.pullFunctor T (p := 𝟙 X)
      (f := fun _ : Unit => f) (f' := fun _ : Unit => k)
      (p' := fun _ : Unit => r) (α := fun _ => ())
      (fun _ => hr.trans (Category.comp_id k).symm) ⋙ (descentEquivalence T hk).inverse ≅
    (descentEquivalence T hf).inverse :=
  inverseSquare (descentEquivalence T hf) (descentEquivalence T hk) _
    (canonicalRefinementIso T f r k hr)

set_option backward.isDefEq.respectTransparency false in
theorem effectiveRefinementIso_hom (D : T.DescentData (fun _ : Unit => f)) :
    (effectiveRefinementIso T f r k hr hf hk).hom.app D =
      (effectivePullIso (p := fun _ : Unit => f) (q := 𝟙 X)
        (p' := fun _ : Unit => k) (r := fun _ : Unit => r) (α := fun _ => ())
        (fun _ => hr.trans (Category.comp_id k).symm) hf hk).inv.app D ≫
      (Cat.Hom.toNatIso (T.mapId (.mk (op X)))).hom.app ((descentEquivalence T hf).inverse.obj D) :=
  inverseSquare_normalize (descentEquivalence T hf) (descentEquivalence T hk) _ _
    (Cat.Hom.toNatIso (T.mapId (.mk (op X)))) _ D

end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} {X : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable {R : C} (r : R ⟶ P.domain) (k : R ⟶ X) (hr : r ≫ P.cover = k)
variable {R' : C} (l : R' ⟶ R) (k' : R' ⟶ X) (hl : l ≫ k = k')
variable [T.IsStack J]
variable (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X)
  (hk' : Sieve.ofArrows _ (fun _ : Unit => k') ∈ J X)

set_option backward.isDefEq.respectTransparency false in
theorem effectiveRefinementIso_comp (D : T.DescentData (fun _ : Unit => P.cover)) :
    (effectiveRefinementIso T k l k' hl hk hk').hom.app
      ((Pseudofunctor.DescentData.pullFunctor T (p := 𝟙 X)
        (f := fun _ : Unit => P.cover) (f' := fun _ : Unit => k)
        (p' := fun _ => r) (α := fun _ => ())
        (fun _ => hr.trans (Category.comp_id k).symm)).obj D) ≫
    (effectiveRefinementIso T P.cover r k hr P.covering hk).hom.app D =
    (descentEquivalence T hk').inverse.map ((P.compRefinementIso r k hr l k' hl T).hom.app D) ≫
      (effectiveRefinementIso T P.cover (l ≫ r) k' (by rw [Category.assoc, hr, hl])
        P.covering hk').hom.app D :=
  inverseSquare_comp (descentEquivalence T P.covering) (descentEquivalence T hk)
    (descentEquivalence T hk') _ _ _ _ _ _ _
    (P.canonicalRefinementIso_comp r k hr l k' hl T) D

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} [T.IsStack J]
variable (θ : F ⟶ T)
variable {X Y R : C} (f : Y ⟶ X) (r : R ⟶ Y) (k : R ⟶ X) (hr : r ≫ f = k)
variable (hf : Sieve.ofArrows _ (fun _ : Unit => f) ∈ J X)
  (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X)

def realizationRefinementIso :
    Pseudofunctor.DescentData.pullFunctor F (p := 𝟙 X)
      (f := fun _ : Unit => f) (f' := fun _ : Unit => k)
      (p' := fun _ : Unit => r) (α := fun _ => ())
      (fun _ => hr.trans (Category.comp_id k).symm) ⋙ realization θ hk ≅ realization θ hf :=
  realizationPullIso (fun _ => hr.trans (Category.comp_id k).symm) θ hf hk ≪≫
    Functor.isoWhiskerLeft (realization θ hf) (Cat.Hom.toNatIso (T.mapId (.mk (op X)))) ≪≫
    (realization θ hf).rightUnitor

set_option backward.isDefEq.respectTransparency false in
theorem realizationRefinementIso_hom (D : F.DescentData (fun _ : Unit => f)) :
    (realizationRefinementIso θ f r k hr hf hk).hom.app D =
      (descentEquivalence T hk).inverse.map
        ((pullIso θ (fun _ : Unit => f) (p := 𝟙 X)
          (f' := fun _ : Unit => k) (p' := fun _ => r) (α := fun _ => ())
          (fun _ => hr.trans (Category.comp_id k).symm)).hom.app D) ≫
        (effectiveRefinementIso T f r k hr hf hk).hom.app ((map θ (fun _ : Unit => f)).obj D) := by
  rw [effectiveRefinementIso_hom]
  dsimp [realizationRefinementIso, realizationPullIso, realization]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]

end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} {X : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable {R : C} (r : R ⟶ P.domain) (k : R ⟶ X) (hr : r ≫ P.cover = k)
variable {R' : C} (l : R' ⟶ R) (k' : R' ⟶ X) (hl : l ≫ k = k')
variable (θ : F ⟶ T) [T.IsStack J]
variable (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X)
  (hk' : Sieve.ofArrows _ (fun _ : Unit => k') ∈ J X)

set_option backward.isDefEq.respectTransparency false in
theorem realizationRefinementIso_comp (D : F.DescentData (fun _ : Unit => P.cover)) :
    (realizationRefinementIso θ k l k' hl hk hk').hom.app ((P.refinement r k hr).obj D) ≫
      (realizationRefinementIso θ P.cover r k hr P.covering hk).hom.app D =
    (realization θ hk').map ((P.compRefinementIso r k hr l k' hl F).hom.app D) ≫
      (realizationRefinementIso θ P.cover (l ≫ r) k' (by rw [Category.assoc, hr, hl])
        P.covering hk').hom.app D := by
  rw [realizationRefinementIso_hom, realizationRefinementIso_hom, realizationRefinementIso_hom]
  simp only [Category.assoc]
  have hn := (effectiveRefinementIso T k l k' hl hk hk').hom.naturality
    ((pullIso θ (fun _ : Unit => P.cover) (p := 𝟙 X)
      (f' := fun _ : Unit => k) (p' := fun _ => r) (α := fun _ => ())
      (fun _ => hr.trans (Category.comp_id k).symm)).hom.app D)
  dsimp at hn
  rw [← reassoc_of% hn]
  rw [← Functor.map_comp_assoc]
  have hc := congrArg Iso.hom (P.pullIso_comp_refinement r k hr l k' hl θ D)
  dsimp at hc
  rw [hc]
  simp only [Functor.map_comp, Category.assoc]
  rw [P.effectiveRefinementIso_comp r k hr l k' hl hk hk']
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  simp only [realization, Functor.comp_map, Functor.map_comp, Category.assoc]


set_option backward.isDefEq.respectTransparency false in
theorem refinedValueIso_comp
    (hFF : ∀ X : C, (component η X).FullyFaithful) :
    (realizationRefinementIso θ k l k' hl hk hk').hom.app
        ((P.refinement r k hr).obj (P.sourceData hFF)) ≫
      (P.refinedValueIso hFF r k hr θ hk).hom =
    (realization θ hk').map
        ((P.compRefinementIso r k hr l k' hl F).hom.app (P.sourceData hFF)) ≫
      (P.refinedValueIso hFF (l ≫ r) k' (by rw [Category.assoc, hr, hl]) θ hk').hom := by
  simpa [realizationRefinementIso, refinedValueIso, realization, value, Category.assoc] using
    P.realizationRefinementIso_comp r k hr l k' hl θ hk hk' (P.sourceData hFF)

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {b c : B.obj (.mk (op X))}
variable (P : LocalPresentation J η b) (Q : LocalPresentation J η c)
variable {R : C} (r : R ⟶ P.domain) (s : R ⟶ Q.domain) (k : R ⟶ X)
  (hr : r ≫ P.cover = k) (hs : s ≫ Q.cover = k)
variable {R' : C} (l : R' ⟶ R) (k' : R' ⟶ X) (hl : l ≫ k = k')
variable (θ : F ⟶ T) [T.IsStack J]
variable (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X)
  (hk' : Sieve.ofArrows _ (fun _ : Unit => k') ∈ J X)

set_option backward.isDefEq.respectTransparency false in
theorem mapOnRefinement_refine (h : b ⟶ c) :
    P.mapOnRefinement hFF r k hr Q s hs θ hk h =
    P.mapOnRefinement hFF (l ≫ r) k' (by rw [Category.assoc, hr, hl])
      Q (l ≫ s) (by rw [Category.assoc, hs, hl]) θ hk' h := by
  apply (cancel_epi (P.refinedValueIso hFF r k hr θ hk).hom).mp
  apply (cancel_epi ((realizationRefinementIso θ k l k' hl hk hk').hom.app
    ((P.refinement r k hr).obj (P.sourceData hFF)))).mp
  simp only [mapOnRefinement, Iso.hom_inv_id_assoc]
  rw [← Category.assoc _ (P.refinedValueIso hFF r k hr θ hk).hom,
    P.refinedValueIso_comp r k hr l k' hl θ hk hk' hFF]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, P.liftMap_refinement hFF Q r s k hr hs l k' hl h,
    Functor.map_comp, Category.assoc, ← Q.refinedValueIso_comp s k hs l k' hl θ hk hk' hFF]
  have hn := (realizationRefinementIso θ k l k' hl hk hk').hom.naturality
    (liftMap η hFF (P.refinedSourceIso hFF r k hr) (Q.refinedSourceIso hFF s k hs) h)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackObjectPropertyDescent
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {b c : B.obj (.mk (op X))}
variable (P : LocalPresentation J η b) (Q : LocalPresentation J η c)
variable (θ : F ⟶ T) [T.IsStack J]
theorem mapOnRefinement_independent {R R' : C}
    (r : R ⟶ P.domain) (s : R ⟶ Q.domain) (k : R ⟶ X)
    (hr : r ≫ P.cover = k) (hs : s ≫ Q.cover = k)
    (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X)
    (r' : R' ⟶ P.domain) (s' : R' ⟶ Q.domain) (k' : R' ⟶ X)
    (hr' : r' ≫ P.cover = k') (hs' : s' ≫ Q.cover = k')
    (hk' : Sieve.ofArrows _ (fun _ : Unit => k') ∈ J X) (h : b ⟶ c) :
    P.mapOnRefinement hFF r k hr Q s hs θ hk h =
      P.mapOnRefinement hFF r' k' hr' Q s' hs' θ hk' h := by
  have hc := singleton_common J k k' hk hk'
  have he := pullback.condition (f := k) (g := k')
  have hc' : Sieve.ofArrows _ (fun _ : Unit => pullback.snd k k' ≫ k') ∈ J X := by
    rw [← he]
    exact hc
  rw [P.mapOnRefinement_refine hFF Q r s k hr hs (pullback.fst k k') _ rfl θ hk hc h,
    P.mapOnRefinement_refine hFF Q r' s' k' hr' hs' (pullback.snd k k') _ rfl θ hk' hc' h]
  simpa only [he] using P.mapOnRefinement_change hFF Q
    (pullback.fst k k' ≫ r) (pullback.snd k k' ≫ r')
    (pullback.fst k k' ≫ s) (pullback.snd k k' ≫ s')
    (pullback.snd k k' ≫ k')
    (by rw [Category.assoc, hr, he]) (by rw [Category.assoc, hr'])
    (by rw [Category.assoc, hs, he]) (by rw [Category.assoc, hs']) θ hc' h
end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackObjectPropertyDescent
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {b c : B.obj (.mk (op X))}
variable (P : LocalPresentation J η b) (Q : LocalPresentation J η c)
variable (θ : F ⟶ T) [T.IsStack J]

def mapTo (h : b ⟶ c) : P.value hFF θ ⟶ Q.value hFF θ :=
  P.mapOnRefinement hFF (pullback.fst P.cover Q.cover)
    (pullback.fst P.cover Q.cover ≫ P.cover) rfl Q
    (pullback.snd P.cover Q.cover) pullback.condition.symm θ
    (singleton_common J P.cover Q.cover P.covering Q.covering) h

theorem mapTo_eq {R : C} (r : R ⟶ P.domain) (s : R ⟶ Q.domain)
    (k : R ⟶ X) (hr : r ≫ P.cover = k) (hs : s ≫ Q.cover = k)
    (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X) (h : b ⟶ c) :
    P.mapTo hFF Q θ h = P.mapOnRefinement hFF r k hr Q s hs θ hk h :=
  P.mapOnRefinement_independent hFF Q θ _ _ _ _ _ _ r s k hr hs hk h

theorem mapTo_id : P.mapTo hFF P θ (𝟙 b) = 𝟙 (P.value hFF θ) := by
  rw [P.mapTo_eq hFF P θ (𝟙 P.domain) (𝟙 P.domain) P.cover
    (Category.id_comp _) (Category.id_comp _) P.covering]
  exact P.mapOnRefinement_id hFF (𝟙 P.domain) P.cover (Category.id_comp _) θ P.covering

theorem mapTo_comp {d : B.obj (.mk (op X))} (H : LocalPresentation J η d)
    (h : b ⟶ c) (g : c ⟶ d) :
    P.mapTo hFF Q θ h ≫ Q.mapTo hFF H θ g = P.mapTo hFF H θ (h ≫ g) := by
  let k₀ := pullback.fst P.cover Q.cover ≫ P.cover
  let R := pullback k₀ H.cover
  let r : R ⟶ P.domain := pullback.fst k₀ H.cover ≫ pullback.fst P.cover Q.cover
  let s : R ⟶ Q.domain := pullback.fst k₀ H.cover ≫ pullback.snd P.cover Q.cover
  let t : R ⟶ H.domain := pullback.snd k₀ H.cover
  let k : R ⟶ X := pullback.fst k₀ H.cover ≫ k₀
  have hr : r ≫ P.cover = k := Category.assoc _ _ _
  have hs : s ≫ Q.cover = k := by
    dsimp [s, k, k₀]
    rw [Category.assoc, ← pullback.condition]
  have ht : t ≫ H.cover = k := pullback.condition.symm
  have hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X :=
    singleton_common J k₀ H.cover
      (singleton_common J P.cover Q.cover P.covering Q.covering) H.covering
  rw [P.mapTo_eq hFF Q θ r s k hr hs hk,
    Q.mapTo_eq hFF H θ s t k hs ht hk,
    P.mapTo_eq hFF H θ r t k hr ht hk]
  exact P.mapOnRefinement_comp hFF Q H r s t k hr hs ht θ hk h g
end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration StackObjectPropertyDescent
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable (hFF : ∀ X : C, (component η X).FullyFaithful)
variable (θ : F ⟶ T) [T.IsStack J]
variable {X : C}
def extensionFunctor (hη : LocallyGenerating J η) :
    B.obj (.mk (op X)) ⥤ T.obj (.mk (op X)) where
  obj := extensionObj hFF hη θ
  map {b c} h := (presentation hη b).mapTo hFF (presentation hη c) θ h
  map_id b := (presentation hη b).mapTo_id hFF θ
  map_comp {b c d} h g := ((presentation hη b).mapTo_comp hFF (presentation hη c)
    θ (presentation hη d) h g).symm

namespace LocalPresentation
variable {b c : B.obj (.mk (op X))}
variable (P : LocalPresentation J η b) (Q : LocalPresentation J η c)

def mapToIso (e : b ≅ c) : P.value hFF θ ≅ Q.value hFF θ where
  hom := P.mapTo hFF Q θ e.hom
  inv := Q.mapTo hFF P θ e.inv
  hom_inv_id := by
    rw [P.mapTo_comp hFF Q θ P, e.hom_inv_id, P.mapTo_id hFF θ]
  inv_hom_id := by
    rw [Q.mapTo_comp hFF P θ Q, e.inv_hom_id, Q.mapTo_id hFF θ]
end LocalPresentation
end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration StackObjectPropertyDescent
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable {X Y : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable (q : Y ⟶ X)

/-- Pull a local presentation back along an arbitrary parameter map. -/
def pull : LocalPresentation J η ((B.map q.op.toLoc).toFunctor.obj b) where
  domain := pullback q P.cover
  cover := pullback.fst q P.cover
  covering := singleton_pullback J P.cover q P.covering
  object := (F.map (pullback.snd q P.cover).op.toLoc).toFunctor.obj P.object
  comparison := restrictedImageIso η (pullback.snd q P.cover) P.comparison ≪≫
    ((Cat.Hom.toNatIso (B.isoMapOfCommSq
      (CommSq.mk (pullback.condition (f := q) (g := P.cover)).symm).op.toLoc)).symm.app b)

/-- The functor on source descent data for the cartesian change of parameter. -/
abbrev parameterPull : F.DescentData (fun _ : Unit => P.cover) ⥤
    F.DescentData (fun _ : Unit => (P.pull q).cover) :=
  Pseudofunctor.DescentData.pullFunctor F (p := q) (α := fun _ : Unit => ())
    (p' := fun _ => pullback.snd q P.cover) (fun _ => pullback.condition.symm)

variable (hFF : ∀ X : C, (component η X).FullyFaithful)

/-- Pulling a presentation transports its entire lifted source cocycle. -/
def pullSourceDataIso : (P.pull q).sourceData hFF ≅
    (P.parameterPull q).obj (P.sourceData hFF) :=
  (mapFullyFaithful η hFF).preimageIso
    ((P.pull q).sourceDataIso hFF ≪≫
      (pullSourceIso (p := fun _ : Unit => P.cover) (q := q)
        (α := fun _ : Unit => ()) (r := fun _ => pullback.snd q P.cover)
        (fun _ => pullback.condition.symm) (P.sourceData hFF) (P.sourceDataIso hFF)).symm)

/-- Effective values of pulled presentations agree with restriction in the target stack. -/
def pullValueIso (θ : F ⟶ T) [T.IsStack J] :
    (P.pull q).value hFF θ ≅ (T.map q.op.toLoc).toFunctor.obj (P.value hFF θ) :=
  (realization θ (P.pull q).covering).mapIso (P.pullSourceDataIso q hFF) ≪≫
    (realizationPullIso (p := fun _ : Unit => P.cover) (q := q)
      (α := fun _ : Unit => ()) (r := fun _ => pullback.snd q P.cover)
      (fun _ => pullback.condition.symm) θ P.covering (P.pull q).covering).app (P.sourceData hFF)

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)

/-- Realizing a presentation's source cocycle recovers its ambient object. -/
def ambientRecovery [B.IsPrestack J] (a : F.obj (.mk (op X)))
    (e : (F.toDescentData (fun _ : Unit => P.cover)).obj a ≅ P.sourceData hFF) :
    (component η X).obj a ≅ b :=
  (B.fullyFaithfulToDescentData _ P.covering).preimageIso
    ((canonicalObjIso η (fun _ : Unit => P.cover) a).symm ≪≫
      (map η _).mapIso e ≪≫ P.sourceDataIso hFF)
end SquareKit.StackificationUniversal.LocalPresentation

namespace CategoryTheory
universe u v u₀ v₀ u₁ v₁
variable {A : Type u} [Category.{v} A]
variable {D₀ : Type u₀} [Category.{v₀} D₀] {D₁ : Type u₁} [Category.{v₁} D₁]
variable (E₀ : A ≌ D₀) (E₁ : A ≌ D₁) (R : D₀ ⥤ D₁)
variable (i : E₀.functor ⋙ R ≅ E₁.functor)

theorem inverseSquare_canonical (a : A) :
    E₁.inverse.map (i.hom.app a) ≫ E₁.unitIso.inv.app a =
      (inverseSquare E₀ E₁ R i).hom.app (E₀.functor.obj a) ≫ E₀.unitIso.inv.app a := by
  apply E₁.functor.map_injective
  apply (cancel_epi (E₁.counitIso.inv.app (R.obj (E₀.functor.obj a)))).mp
  simp only [Functor.map_comp]
  rw [inverseSquare_spec_assoc]
  rw [← E₁.counit_app_functor]
  simp only [Equivalence.fun_inv_map, Equivalence.counit, Equivalence.counitInv,
    Category.assoc, Iso.inv_hom_id_app]
  have hn := i.hom.naturality (E₀.unitIso.inv.app a)
  dsimp at hn
  rw [← hn, ← Functor.map_comp_assoc, ← E₀.counit_app_functor]
  simp

end CategoryTheory

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v' t
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable (θ : F ⟶ T) [T.IsStack J]
variable {ι : Type t} {X : C} {U : ι → C} {p : ∀ i, U i ⟶ X}

def effectiveCanonical (hp : Sieve.ofArrows _ p ∈ J X) (a : F.obj (.mk (op X))) :
    (realization θ hp).obj ((F.toDescentData p).obj a) ≅ (component θ X).obj a :=
  (descentEquivalence T hp).inverse.mapIso (canonicalObjIso θ p a) ≪≫
    (descentEquivalence T hp).unitIso.symm.app ((component θ X).obj a)

variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {a : F.obj (.mk (op X))} (P : LocalPresentation J η ((component η X).obj a))

set_option backward.isDefEq.respectTransparency false in
theorem LocalPresentation.valueRecovery_hom :
    (P.valueRecovery hFF θ).hom =
      (realization θ P.covering).map (P.sourceRecovery hFF).hom ≫
        (effectiveCanonical θ P.covering a).hom := by
  apply (T.fullyFaithfulToDescentData _ P.covering).map_injective
  simp only [LocalPresentation.valueRecovery, Functor.FullyFaithful.preimageIso, Functor.FullyFaithful.map_preimage,
    Iso.trans_hom, Functor.mapIso_hom, canonicalObjIso,
    effectiveCanonical, Functor.map_comp]
  change (P.valueIso hFF θ).hom ≫ _ ≫ _ = _
  dsimp [LocalPresentation.valueIso, realization]
  let E := descentEquivalence T P.covering
  change E.counitIso.hom.app _ ≫ _ ≫ _ =
    E.functor.map (E.inverse.map _) ≫ E.functor.map (E.inverse.map _) ≫
      E.functor.map (E.unitIso.inv.app _)
  rw [← E.counit_app_functor]
  simp [Equivalence.fun_inv_map, Category.assoc]

end SquareKit.StackificationUniversal
namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C]
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable (η : F ⟶ B)
variable {X Y R : C} (f : Y ⟶ X) (r : R ⟶ Y) (k : R ⟶ X) (hr : r ≫ f = k)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem canonicalObjIso_refinement (a : F.obj (.mk (op X))) :
    (map η (fun _ : Unit => k)).map ((canonicalRefinementIso F f r k hr).hom.app a) ≫
      (canonicalObjIso η (fun _ : Unit => k) a).hom =
    (pullIso η (fun _ : Unit => f) (p := 𝟙 X)
      (f' := fun _ : Unit => k) (p' := fun _ => r) (α := fun _ => ())
      (fun _ => hr.trans (Category.comp_id k).symm)).hom.app ((F.toDescentData (fun _ : Unit => f)).obj a) ≫
    (Pseudofunctor.DescentData.pullFunctor B (p := 𝟙 X)
      (f := fun _ : Unit => f) (f' := fun _ : Unit => k)
      (p' := fun _ => r) (α := fun _ => ())
      (fun _ => hr.trans (Category.comp_id k).symm)).map (canonicalObjIso η (fun _ : Unit => f) a).hom ≫
      (canonicalRefinementIso B f r k hr).hom.app ((component η X).obj a) := by
  ext i
  cases i
  change (component η R).map (((canonicalRefinementIso F f r k hr).hom.app a).hom ()) ≫
      (comparison η k).hom.app a =
    (comparison η r).hom.app ((F.map f.op.toLoc).toFunctor.obj a) ≫
      (B.map r.op.toLoc).toFunctor.map ((comparison η f).hom.app a) ≫
        ((canonicalRefinementIso B f r k hr).hom.app ((component η X).obj a)).hom ()
  rw [canonicalRefinementIso_hom, canonicalRefinementIso_hom]
  have hc := comparison_comp_hom η f r k hr a
  rw [← cancel_epi ((component η R).map
    ((F.mapComp' f.op.toLoc r.op.toLoc k.op.toLoc (by simpa using congrArg (fun g => g.op.toLoc) hr)).hom.toNatTrans.app a))]
  rw [← Functor.map_comp_assoc]
  simp only [← Cat.Hom.toNatIso_hom, ← Cat.Hom.toNatIso_inv, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [← Cat.Hom.toNatIso_hom] at hc
  rw [← reassoc_of% hc]
  simp

end SquareKit.StackificationUniversal
namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {a : F.obj (.mk (op X))}
variable (P : LocalPresentation J η ((component η X).obj a))
variable {R : C} (r : R ⟶ P.domain) (k : R ⟶ X) (hr : r ≫ P.cover = k)

/-- Recovery of canonical source descent data after refining a presentation. -/
def refinedSourceRecovery :
    (P.refinement r k hr).obj (P.sourceData hFF) ≅ (F.toDescentData (fun _ : Unit => k)).obj a :=
  (P.refinement r k hr).mapIso (P.sourceRecovery hFF) ≪≫
    (canonicalRefinementIso F P.cover r k hr).app a

set_option backward.isDefEq.respectTransparency false in
theorem sourceRecovery_hom :
    (map η (fun _ : Unit => P.cover)).map (P.sourceRecovery hFF).hom ≫
      (canonicalObjIso η (fun _ : Unit => P.cover) a).hom = (P.sourceDataIso hFF).hom := by
  simp [sourceRecovery]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem refinedSourceRecovery_hom :
    (map η (fun _ : Unit => k)).map (P.refinedSourceRecovery hFF r k hr).hom ≫
      (canonicalObjIso η (fun _ : Unit => k) a).hom =
    (P.refinedSourceIso hFF r k hr).hom := by
  simp only [refinedSourceRecovery, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [canonicalObjIso_refinement]
  have hn := (pullIso η (fun _ : Unit => P.cover) (p := 𝟙 X)
    (f' := fun _ : Unit => k) (p' := fun _ => r) (α := fun _ => ())
    (fun _ => hr.trans (Category.comp_id k).symm)).hom.naturality (P.sourceRecovery hFF).hom
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, P.sourceRecovery_hom hFF]
  exact (P.refinedSourceIso_hom hFF r k hr).symm

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable (θ : F ⟶ T) [T.IsStack J]
variable {X Y R : C} (f : Y ⟶ X) (r : R ⟶ Y) (k : R ⟶ X) (hr : r ≫ f = k)
variable (hf : Sieve.ofArrows _ (fun _ : Unit => f) ∈ J X)
  (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X)

set_option backward.isDefEq.respectTransparency false in
theorem effectiveCanonical_refinement (a : F.obj (.mk (op X))) :
    (realization θ hk).map ((canonicalRefinementIso F f r k hr).hom.app a) ≫
      (effectiveCanonical θ hk a).hom =
    (realizationRefinementIso θ f r k hr hf hk).hom.app
        ((F.toDescentData (fun _ : Unit => f)).obj a) ≫
      (effectiveCanonical θ hf a).hom := by
  rw [realizationRefinementIso_hom]
  dsimp only [effectiveCanonical, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    realization, Functor.comp_map]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, canonicalObjIso_refinement]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (effectiveRefinementIso T f r k hr hf hk).hom.naturality
    (canonicalObjIso θ (fun _ : Unit => f) a).hom
  dsimp at hn
  rw [← reassoc_of% hn]
  congr 1
  congr 1
  exact inverseSquare_canonical (descentEquivalence T hf) (descentEquivalence T hk) _ _
    ((component θ X).obj a)

variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {a : F.obj (.mk (op X))} (P : LocalPresentation J η ((component η X).obj a))
variable (r : R ⟶ P.domain) (hr : r ≫ P.cover = k)

set_option backward.isDefEq.respectTransparency false in
theorem LocalPresentation.refinedValueRecovery_hom :
    (realization θ hk).map (P.refinedSourceRecovery hFF r k hr).hom ≫
      (effectiveCanonical θ hk a).hom =
    (P.refinedValueIso hFF r k hr θ hk).hom ≫ (P.valueRecovery hFF θ).hom := by
  simp only [LocalPresentation.refinedSourceRecovery, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [effectiveCanonical_refinement θ P.cover r k hr P.covering hk]
  have hn := (realizationRefinementIso θ P.cover r k hr P.covering hk).hom.naturality
    (P.sourceRecovery hFF).hom
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← P.valueRecovery_hom θ hFF]
  congr 1
  simp [realizationRefinementIso, LocalPresentation.refinedValueIso,
    realization, LocalPresentation.value]

end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {a a' : F.obj (.mk (op X))}
variable (P : LocalPresentation J η ((component η X).obj a))
  (Q : LocalPresentation J η ((component η X).obj a'))
variable {R : C} (r : R ⟶ P.domain) (s : R ⟶ Q.domain) (k : R ⟶ X)
  (hr : r ≫ P.cover = k) (hs : s ≫ Q.cover = k)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem liftMap_recovery (h : a ⟶ a') :
    liftMap η hFF (P.refinedSourceIso hFF r k hr) (Q.refinedSourceIso hFF s k hs)
        ((component η X).map h) ≫ (Q.refinedSourceRecovery hFF s k hs).hom =
    (P.refinedSourceRecovery hFF r k hr).hom ≫ (F.toDescentData (fun _ : Unit => k)).map h := by
  apply (mapFullyFaithful η hFF).map_injective
  simp only [Functor.map_comp, map_liftMap]
  apply (cancel_mono (canonicalObjIso η (fun _ : Unit => k) a').hom).mp
  simp only [Category.assoc]
  rw [Q.refinedSourceRecovery_hom hFF s k hs]
  simp only [Iso.inv_hom_id, Category.comp_id]
  have hn := (canonicalIso η (fun _ : Unit => k)).hom.naturality h
  dsimp only [Functor.comp_map] at hn
  change _ = _ ≫ _ ≫ (canonicalIso η (fun _ : Unit => k)).hom.app a'
  rw [hn, ← Category.assoc]
  congr 1
  exact (P.refinedSourceRecovery_hom hFF r k hr).symm

end SquareKit.StackificationUniversal.LocalPresentation
namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v' t
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable (θ : F ⟶ T) [T.IsStack J]
variable {ι : Type t} {X : C} {U : ι → C} {p : ∀ i, U i ⟶ X}
variable (hp : Sieve.ofArrows _ p ∈ J X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem effectiveCanonical_naturality {a a' : F.obj (.mk (op X))} (h : a ⟶ a') :
    (realization θ hp).map ((F.toDescentData p).map h) ≫
      (effectiveCanonical θ hp a').hom =
    (effectiveCanonical θ hp a).hom ≫ (component θ X).map h := by
  have hn := (canonicalIso θ p).hom.naturality h
  dsimp only [Functor.comp_map] at hn
  dsimp [effectiveCanonical, realization]
  rw [← Functor.map_comp_assoc]
  change (descentEquivalence T hp).inverse.map
    ((map θ p).map ((F.toDescentData p).map h) ≫ (canonicalIso θ p).hom.app a') ≫ _ = _
  rw [hn, Functor.map_comp, Category.assoc]
  simp only [Category.assoc]
  change _ ≫ _ = (descentEquivalence T hp).inverse.map
    ((canonicalIso θ p).hom.app a) ≫ _
  congr 1
  exact (descentEquivalence T hp).unitIso.inv.naturality ((component θ X).map h)

end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {a a' : F.obj (.mk (op X))}
variable (P : LocalPresentation J η ((component η X).obj a))
  (Q : LocalPresentation J η ((component η X).obj a'))
variable {R : C} (r : R ⟶ P.domain) (s : R ⟶ Q.domain) (k : R ⟶ X)
  (hr : r ≫ P.cover = k) (hs : s ≫ Q.cover = k)
variable (θ : F ⟶ T) [T.IsStack J]
  (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X)

set_option backward.isDefEq.respectTransparency false in
theorem mapOnRefinement_recovery (h : a ⟶ a') :
    P.mapOnRefinement hFF r k hr Q s hs θ hk ((component η X).map h) ≫
      (Q.valueRecovery hFF θ).hom =
    (P.valueRecovery hFF θ).hom ≫ (component θ X).map h := by
  apply (cancel_epi (P.refinedValueIso hFF r k hr θ hk).hom).mp
  simp only [mapOnRefinement, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  simp only [Category.assoc]
  rw [← Q.refinedValueRecovery_hom θ k hk hFF s hs,
    ← Functor.map_comp_assoc, P.liftMap_recovery hFF Q r s k hr hs,
    Functor.map_comp, Category.assoc, effectiveCanonical_naturality]
  rw [← Category.assoc, P.refinedValueRecovery_hom θ k hk hFF r hr]
  simp only [Category.assoc]

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration StackObjectPropertyDescent
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C] {J : GrothendieckTopology C}
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {a a' : F.obj (.mk (op X))}
variable (θ : F ⟶ T) [T.IsStack J]

theorem LocalPresentation.mapTo_recovery
    (P : LocalPresentation J η ((component η X).obj a))
    (Q : LocalPresentation J η ((component η X).obj a')) (h : a ⟶ a') :
    P.mapTo hFF Q θ ((component η X).map h) ≫ (Q.valueRecovery hFF θ).hom =
      (P.valueRecovery hFF θ).hom ≫ (component θ X).map h :=
  P.mapOnRefinement_recovery hFF Q (pullback.fst P.cover Q.cover)
    (pullback.snd P.cover Q.cover) (pullback.fst P.cover Q.cover ≫ P.cover)
    rfl pullback.condition.symm θ
    (singleton_common J P.cover Q.cover P.covering Q.covering) h

/-- The extended functor recovers the given functor on each source fiber. -/
def extensionFunctorRecovery (hη : LocallyGenerating J η) :
    component η X ⋙ extensionFunctor hFF θ hη ≅ component θ X :=
  NatIso.ofComponents (fun a => (presentation hη ((component η X).obj a)).valueRecovery hFF θ)
    (fun h => (presentation hη _).mapTo_recovery hFF θ (presentation hη _) h)

end SquareKit.StackificationUniversal
namespace SquareKit.StackificationUniversal.ParameterComposition
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C]
variable (H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
variable {X₀ X₁ X₂ U₀ U₁ U₂ : C}
variable (f₀ : U₀ ⟶ X₀) (f₁ : U₁ ⟶ X₁) (f₂ : U₂ ⟶ X₂)
variable (q₀₁ : X₁ ⟶ X₀) (q₁₂ : X₂ ⟶ X₁)
variable (r₀₁ : U₁ ⟶ U₀) (r₁₂ : U₂ ⟶ U₁)
variable (w₀₁ : r₀₁ ≫ f₀ = f₁ ≫ q₀₁) (w₁₂ : r₁₂ ≫ f₁ = f₂ ≫ q₁₂)

abbrev firstPull := Pseudofunctor.DescentData.pullFunctor H (p := q₀₁)
  (f := fun _ : Unit => f₀) (f' := fun _ : Unit => f₁)
  (α := fun _ : Unit => ()) (p' := fun _ => r₀₁) (fun _ => w₀₁)
abbrev secondPull := Pseudofunctor.DescentData.pullFunctor H (p := q₁₂)
  (f := fun _ : Unit => f₁) (f' := fun _ : Unit => f₂)
  (α := fun _ : Unit => ()) (p' := fun _ => r₁₂) (fun _ => w₁₂)
abbrev compositePull := Pseudofunctor.DescentData.pullFunctor H (p := q₁₂ ≫ q₀₁)
  (f := fun _ : Unit => f₀) (f' := fun _ : Unit => f₂)
  (α := fun _ : Unit => ()) (p' := fun _ => r₁₂ ≫ r₀₁)
  (fun _ => by simp only [Category.assoc, w₀₁, reassoc_of% w₁₂])

def pullCompIso : firstPull H f₀ f₁ q₀₁ r₀₁ w₀₁ ⋙ secondPull H f₁ f₂ q₁₂ r₁₂ w₁₂ ≅
    compositePull H f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂ :=
  Pseudofunctor.DescentData.pullFunctorCompIso H
    (f := fun _ : Unit => f₀) (f' := fun _ : Unit => f₁) (f'' := fun _ : Unit => f₂)
    (p := q₀₁) (q := q₁₂) (α := fun _ : Unit => ()) (β := fun _ : Unit => ())
    (p' := fun _ => r₀₁) (q' := fun _ => r₁₂) (r' := fun _ => r₁₂ ≫ r₀₁)
    (fun _ => w₀₁) (fun _ => w₁₂) (q₁₂ ≫ q₀₁) rfl (fun _ => rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem canonicalPullComp (b : H.obj (.mk (op X₀))) :
    (secondPull H f₁ f₂ q₁₂ r₁₂ w₁₂).map
        ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso H
          (f := fun _ : Unit => f₀) (f' := fun _ : Unit => f₁)
          (p := q₀₁) (p' := fun _ => r₀₁) (α := fun _ : Unit => ())
          (fun _ => w₀₁)).hom.app b) ≫
      (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso H
        (f := fun _ : Unit => f₁) (f' := fun _ : Unit => f₂)
        (p := q₁₂) (p' := fun _ => r₁₂) (α := fun _ : Unit => ())
        (fun _ => w₁₂)).hom.app ((H.map q₀₁.op.toLoc).toFunctor.obj b) ≫
      (H.toDescentData (fun _ : Unit => f₂)).map
        ((H.mapComp' q₀₁.op.toLoc q₁₂.op.toLoc (q₁₂ ≫ q₀₁).op.toLoc (by grind)).inv.toNatTrans.app b) =
    (pullCompIso H f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂).hom.app
        ((H.toDescentData (fun _ : Unit => f₀)).obj b) ≫
      (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso H
        (f := fun _ : Unit => f₀) (f' := fun _ : Unit => f₂)
        (p := q₁₂ ≫ q₀₁) (p' := fun _ => r₁₂ ≫ r₀₁) (α := fun _ : Unit => ())
        (fun _ => by simp only [Category.assoc, w₀₁, reassoc_of% w₁₂])).hom.app b := by
  ext i
  cases i
  dsimp [firstPull, secondPull, pullCompIso, Pseudofunctor.DescentData.pullFunctor,
    Pseudofunctor.DescentData.pullFunctorObj,
    Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso,
    Pseudofunctor.DescentData.pullFunctorCompIso, Pseudofunctor.DescentData.isoMk,
    Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj]
  rw [H.isoMapOfCommSq_eq _ (r₀₁ ≫ f₀).op.toLoc (by grind),
    H.isoMapOfCommSq_eq _ (r₁₂ ≫ f₁).op.toLoc (by grind),
    H.isoMapOfCommSq_eq _ ((r₁₂ ≫ r₀₁) ≫ f₀).op.toLoc (by grind)]
  simp only [Iso.trans_inv, Iso.symm_inv, Cat.Hom.toNatIso_inv, Cat.Hom₂.comp_app,
    Functor.map_comp, Category.assoc]

  have hm₀ := H.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app
    q₀₁.op.toLoc f₁.op.toLoc r₁₂.op.toLoc (r₀₁ ≫ f₀).op.toLoc
    (r₁₂ ≫ f₁).op.toLoc ((r₁₂ ≫ r₀₁) ≫ f₀).op.toLoc
    (by grind) (by grind) (by grind) b
  have hm := congrArg (fun h =>
    (H.mapComp' (r₀₁ ≫ f₀).op.toLoc r₁₂.op.toLoc ((r₁₂ ≫ r₀₁) ≫ f₀).op.toLoc
      (by grind)).inv.toNatTrans.app b ≫ h ≫
    (H.mapComp' f₁.op.toLoc r₁₂.op.toLoc (r₁₂ ≫ f₁).op.toLoc
      (by grind)).inv.toNatTrans.app ((H.map q₀₁.op.toLoc).toFunctor.obj b)) hm₀
  simp only [Category.assoc, ← Cat.Hom.toNatIso_hom, ← Cat.Hom.toNatIso_inv,
    Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app, Category.comp_id] at hm
  simp only [Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv] at hm
  rw [reassoc_of% hm]
  rw [H.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc
    f₀.op.toLoc r₀₁.op.toLoc r₁₂.op.toLoc (r₀₁ ≫ f₀).op.toLoc
    (r₀₁.op.toLoc ≫ r₁₂.op.toLoc) ((r₁₂ ≫ r₀₁) ≫ f₀).op.toLoc
    (by grind) rfl (by grind)]
  rw [H.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app_assoc
    q₀₁.op.toLoc q₁₂.op.toLoc f₂.op.toLoc (q₀₁.op.toLoc ≫ q₁₂.op.toLoc)
    (r₁₂ ≫ f₁).op.toLoc ((r₁₂ ≫ r₀₁) ≫ f₀).op.toLoc
    rfl (by grind) (by grind)]
  simp only [← Functor.map_comp, ← Cat.Hom.toNatIso_hom, ← Cat.Hom.toNatIso_inv,
    Iso.hom_inv_id_app, Cat.Hom.comp_toFunctor, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.comp_id]

variable {F T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} (θ : F ⟶ T)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Strong transformations respect the compositor of arbitrary parameter pullbacks. -/
theorem transformationPullComp (D : F.DescentData (fun _ : Unit => f₀)) :
    (pullIso θ (fun _ : Unit => f₁) (p := q₁₂)
      (f' := fun _ : Unit => f₂) (p' := fun _ => r₁₂) (α := fun _ : Unit => ())
      (fun _ => w₁₂)).app ((firstPull F f₀ f₁ q₀₁ r₀₁ w₀₁).obj D) ≪≫
    (secondPull T f₁ f₂ q₁₂ r₁₂ w₁₂).mapIso
      ((pullIso θ (fun _ : Unit => f₀) (p := q₀₁)
        (f' := fun _ : Unit => f₁) (p' := fun _ => r₀₁) (α := fun _ : Unit => ())
        (fun _ => w₀₁)).app D) =
    (map θ (fun _ : Unit => f₂)).mapIso
      ((pullCompIso F f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂).app D) ≪≫
    (pullIso θ (fun _ : Unit => f₀) (p := q₁₂ ≫ q₀₁)
      (f' := fun _ : Unit => f₂) (p' := fun _ => r₁₂ ≫ r₀₁) (α := fun _ : Unit => ())
      (fun _ => by simp only [Category.assoc, w₀₁, reassoc_of% w₁₂])).app D ≪≫
    ((pullCompIso T f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂).app
      ((map θ (fun _ : Unit => f₀)).obj D)).symm := by
  ext i
  cases i
  have hc := comparison_comp_hom θ r₀₁ r₁₂ (r₁₂ ≫ r₀₁) rfl (D.obj ())
  dsimp [pullIso, pullObjIso, pullCompIso,
    Pseudofunctor.DescentData.pullFunctorCompIso] at *
  dsimp [map, mapMap, mapObj, firstPull, secondPull,
    Pseudofunctor.DescentData.pullFunctor, Pseudofunctor.DescentData.pullFunctorObj,
    Pseudofunctor.DescentData.isoMk]
  simp only [Pseudofunctor.mapComp'_eq_mapComp, Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv] at *
  rw [hc]
  simp only [← Functor.map_comp_assoc, ← Cat.Hom.toNatIso_hom, ← Cat.Hom.toNatIso_inv,
    Iso.inv_hom_id_app]
  simp

end SquareKit.StackificationUniversal.ParameterComposition
namespace SquareKit.StackificationUniversal.ParameterComposition
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C]
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} (η : F ⟶ B)
variable {X₀ X₁ X₂ U₀ U₁ U₂ : C}
variable (f₀ : U₀ ⟶ X₀) (f₁ : U₁ ⟶ X₁) (f₂ : U₂ ⟶ X₂)
variable (q₀₁ : X₁ ⟶ X₀) (q₁₂ : X₂ ⟶ X₁)
variable (r₀₁ : U₁ ⟶ U₀) (r₁₂ : U₂ ⟶ U₁)
variable (w₀₁ : r₀₁ ≫ f₀ = f₁ ≫ q₀₁) (w₁₂ : r₁₂ ≫ f₁ = f₂ ≫ q₁₂)
variable {b : B.obj (.mk (op X₀))} (D : F.DescentData (fun _ : Unit => f₀))
variable (e : (map η (fun _ : Unit => f₀)).obj D ≅
  (B.toDescentData (fun _ : Unit => f₀)).obj b)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem pullSourceIso_comp :
    (pullSourceIso (p := fun _ : Unit => f₁) (p' := fun _ : Unit => f₂)
      (q := q₁₂) (α := fun _ : Unit => ()) (r := fun _ => r₁₂) (fun _ => w₁₂)
      ((firstPull F f₀ f₁ q₀₁ r₀₁ w₀₁).obj D)
      (pullSourceIso (p := fun _ : Unit => f₀) (p' := fun _ : Unit => f₁)
        (q := q₀₁) (α := fun _ : Unit => ()) (r := fun _ => r₀₁) (fun _ => w₀₁) D e)).hom ≫
    (B.toDescentData (fun _ : Unit => f₂)).map
      ((B.mapComp' q₀₁.op.toLoc q₁₂.op.toLoc (q₁₂ ≫ q₀₁).op.toLoc (by grind)).inv.toNatTrans.app b) =
    (map η (fun _ : Unit => f₂)).map
      ((pullCompIso F f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂).hom.app D) ≫
    (pullSourceIso (p := fun _ : Unit => f₀) (p' := fun _ : Unit => f₂)
      (q := q₁₂ ≫ q₀₁) (α := fun _ : Unit => ()) (r := fun _ => r₁₂ ≫ r₀₁)
      (fun _ => by simp only [Category.assoc, w₀₁, reassoc_of% w₁₂]) D e).hom := by
  simp only [pullSourceIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  have ht := congrArg Iso.hom
    (transformationPullComp f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂ η D)
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv] at ht
  rw [← Category.assoc _ ((secondPull B f₁ f₂ q₁₂ r₁₂ w₁₂).map
      ((pullIso η (fun _ : Unit => f₀) (p := q₀₁)
        (f' := fun _ : Unit => f₁) (p' := fun _ => r₀₁) (α := fun _ : Unit => ())
        (fun _ => w₀₁)).hom.app D)), ht]
  simp only [Category.assoc]
  rw [canonicalPullComp B f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂ b]
  have hn := (pullCompIso B f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂).inv.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  simp
end SquareKit.StackificationUniversal.ParameterComposition

namespace CategoryTheory
universe u v u' v'
variable {A : Type u} [Category.{v} A] {D : Type u'} [Category.{v'} D]
variable (L : A ⥤ A) (R : D ⥤ D) (K : A ⥤ D)
variable (u : L ≅ 𝟭 A) (v : R ≅ 𝟭 D) (c : L ⋙ K ≅ K ⋙ R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An invertible comparison preserving composition also preserves the units. -/
theorem unit_of_composition
    (hc : ∀ x, c.hom.app x ≫ R.map (v.inv.app (K.obj x)) =
      K.map (L.map (u.inv.app x)) ≫ c.hom.app (L.obj x) ≫ R.map (c.hom.app x))
    (x : A) : c.hom.app x ≫ v.hom.app (K.obj x) = K.map (u.hom.app x) := by
  have hn := c.hom.naturality (u.inv.app x)
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  have hh := hc x
  rw [← Category.assoc, hn, Category.assoc] at hh
  have hm := (cancel_epi (c.hom.app x)).mp hh
  rw [← Functor.map_comp] at hm
  have hv := congrArg (fun f => f ≫ v.hom.app (R.obj (K.obj x))) hm
  have hv' := v.hom.naturality (K.map (u.inv.app x) ≫ c.hom.app x)
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj] at hv'
  rw [hv', v.hom.naturality] at hv
  dsimp only [Functor.id_map] at hv
  have he := (cancel_epi (v.hom.app (K.obj x))).mp hv
  apply (cancel_epi (K.map (u.inv.app x))).mp
  rw [← Category.assoc, ← he, ← Functor.map_comp]
  simp
end CategoryTheory

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v' t t'
variable {C : Type u} [Category.{v} C]
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable (η : F ⟶ B)
variable {ι : Type t} {X : C} {U : ι → C} {p : ∀ i, U i ⟶ X}
variable {ι' : Type t'} {X' : C} {U' : ι' → C} {p' : ∀ i, U' i ⟶ X'}
variable {q : X' ⟶ X} {α : ι' → ι} {r : ∀ i, U' i ⟶ U (α i)}
variable (w : ∀ i, r i ≫ p (α i) = p' i ≫ q)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem canonicalObjIso_pull (a : F.obj (.mk (op X))) :
    (map η p').map ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso F w).hom.app a) ≫
      (canonicalObjIso η p' ((F.map q.op.toLoc).toFunctor.obj a)).hom ≫
      (B.toDescentData p').map ((StackDescentTransformation.comparison η q).hom.app a) =
    (pullIso η p w).hom.app ((F.toDescentData p).obj a) ≫
      (Pseudofunctor.DescentData.pullFunctor B w).map (canonicalObjIso η p a).hom ≫
      (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso B w).hom.app ((component η X).obj a) := by
  ext i
  dsimp [map, mapMap, canonicalObjIso, pullIso, pullObjIso,
    Pseudofunctor.DescentData.pullFunctor, Pseudofunctor.DescentData.pullFunctorObj,
    Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso,
    Pseudofunctor.DescentData.isoMk, Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj]
  rw [F.isoMapOfCommSq_eq _ (p' i ≫ q).op.toLoc rfl,
    B.isoMapOfCommSq_eq _ (p' i ≫ q).op.toLoc rfl]
  have h₁ := comparison_comp_hom η (p (α i)) (r i) (p' i ≫ q) (w i) a
  have h₂ := comparison_comp_hom η q (p' i) (p' i ≫ q) rfl a
  simp only [Cat.Hom.toNatIso_inv, Iso.trans_inv, Iso.symm_inv, Cat.Hom.toNatTrans_comp, NatTrans.comp_app]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← h₂]
  rw [← cancel_epi ((component η (U' i)).map
    ((F.mapComp' (p (α i)).op.toLoc (r i).op.toLoc (p' i ≫ q).op.toLoc (by simpa using congrArg (fun g => g.op.toLoc) (w i))).hom.toNatTrans.app a))]
  rw [← Functor.map_comp_assoc]
  simp only [← Cat.Hom.toNatIso_hom, ← Cat.Hom.toNatIso_inv,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [← Cat.Hom.toNatIso_hom] at h₁
  rw [← reassoc_of% h₁]
  simp

end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {a : F.obj (.mk (op X))} {b : B.obj (.mk (op X))}
variable (Q : LocalPresentation J η b)
variable (e : Q.sourceData hFF ≅ (F.toDescentData (fun _ : Unit => Q.cover)).obj a)
variable (h : (component η X).obj a ≅ b)
variable (he : (map η (fun _ : Unit => Q.cover)).map e.hom ≫
  (canonicalObjIso η (fun _ : Unit => Q.cover) a).hom ≫
  (B.toDescentData (fun _ : Unit => Q.cover)).map h.hom = (Q.sourceDataIso hFF).hom)
variable {R : C} (s : R ⟶ Q.domain) (k : R ⟶ X) (hs : s ≫ Q.cover = k)

def recoveryAlongRefinement :
    (Q.refinement s k hs).obj (Q.sourceData hFF) ≅ (F.toDescentData (fun _ : Unit => k)).obj a :=
  (Q.refinement s k hs).mapIso e ≪≫ (canonicalRefinementIso F Q.cover s k hs).app a

include he in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem recoveryAlongRefinement_hom :
    (map η (fun _ : Unit => k)).map (Q.recoveryAlongRefinement hFF e s k hs).hom ≫
      (canonicalObjIso η (fun _ : Unit => k) a).hom ≫
      (B.toDescentData (fun _ : Unit => k)).map h.hom =
    (Q.refinedSourceIso hFF s k hs).hom := by
  simp only [recoveryAlongRefinement, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% (canonicalObjIso_refinement η Q.cover s k hs a)]
  have hc := (canonicalRefinementIso B Q.cover s k hs).hom.naturality h.hom
  dsimp only [Functor.comp_map] at hc
  rw [← hc]
  have hn := (pullIso η (fun _ : Unit => Q.cover) (p := 𝟙 X)
    (f' := fun _ : Unit => k) (p' := fun _ => s) (α := fun _ => ())
    (fun _ => hs.trans (Category.comp_id k).symm)).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, he]
  exact (Q.refinedSourceIso_hom hFF s k hs).symm

variable (θ : F ⟶ T) [T.IsStack J]
  (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X)

set_option backward.isDefEq.respectTransparency false in
theorem recoveryAlongRefinement_value :
    (realization θ hk).map (Q.recoveryAlongRefinement hFF e s k hs).hom ≫
      (effectiveCanonical θ hk a).hom =
    (Q.refinedValueIso hFF s k hs θ hk).hom ≫
      (realization θ Q.covering).map e.hom ≫ (effectiveCanonical θ Q.covering a).hom := by
  simp only [recoveryAlongRefinement, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [effectiveCanonical_refinement θ Q.cover s k hs Q.covering hk]
  have hn := (realizationRefinementIso θ Q.cover s k hs Q.covering hk).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc]
  congr 1
  simp [realizationRefinementIso, refinedValueIso, realization, value]

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {a : F.obj (.mk (op X))} {b : B.obj (.mk (op X))}
variable (P : LocalPresentation J η ((component η X).obj a)) (Q : LocalPresentation J η b)
variable (e : Q.sourceData hFF ≅ (F.toDescentData (fun _ : Unit => Q.cover)).obj a)
variable (h : (component η X).obj a ≅ b)
variable (he : (map η (fun _ : Unit => Q.cover)).map e.hom ≫
  (canonicalObjIso η (fun _ : Unit => Q.cover) a).hom ≫
  (B.toDescentData (fun _ : Unit => Q.cover)).map h.hom = (Q.sourceDataIso hFF).hom)
variable {R : C} (r : R ⟶ P.domain) (s : R ⟶ Q.domain) (k : R ⟶ X)
  (hr : r ≫ P.cover = k) (hs : s ≫ Q.cover = k)

include he in
set_option backward.isDefEq.respectTransparency false in
theorem liftMap_recoveryAlong :
    liftMap η hFF (P.refinedSourceIso hFF r k hr) (Q.refinedSourceIso hFF s k hs) h.hom ≫
      (Q.recoveryAlongRefinement hFF e s k hs).hom =
    (P.refinedSourceRecovery hFF r k hr).hom := by
  apply (mapFullyFaithful η hFF).map_injective
  simp only [Functor.map_comp, map_liftMap]
  apply (cancel_mono ((canonicalObjIso η (fun _ : Unit => k) a).hom ≫
    (B.toDescentData (fun _ : Unit => k)).map h.hom)).mp
  simp only [Category.assoc]
  rw [Q.recoveryAlongRefinement_hom hFF e h he s k hs]
  simp only [Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, P.refinedSourceRecovery_hom hFF r k hr]

variable (θ : F ⟶ T) [T.IsStack J]
  (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X)
include he in
set_option backward.isDefEq.respectTransparency false in
theorem mapOnRefinement_recoveryAlong :
    P.mapOnRefinement hFF r k hr Q s hs θ hk h.hom ≫
      (realization θ Q.covering).map e.hom ≫ (effectiveCanonical θ Q.covering a).hom =
    (P.valueRecovery hFF θ).hom := by
  apply (cancel_epi (P.refinedValueIso hFF r k hr θ hk).hom).mp
  simp only [mapOnRefinement, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  simp only [Category.assoc]
  rw [← Q.recoveryAlongRefinement_value hFF e s k hs θ hk,
    ← Functor.map_comp_assoc, P.liftMap_recoveryAlong hFF Q e h he r s k hr hs]
  exact P.refinedValueRecovery_hom θ k hk hFF r hr

variable [Limits.HasPullbacks C]
include he in
theorem mapTo_recoveryAlong :
    P.mapTo hFF Q θ h.hom ≫
      (realization θ Q.covering).map e.hom ≫ (effectiveCanonical θ Q.covering a).hom =
    (P.valueRecovery hFF θ).hom :=
  P.mapOnRefinement_recoveryAlong hFF Q e h he
    (Limits.pullback.fst P.cover Q.cover) (Limits.pullback.snd P.cover Q.cover)
    (Limits.pullback.fst P.cover Q.cover ≫ P.cover) rfl Limits.pullback.condition.symm θ
    (StackObjectPropertyDescent.singleton_common J P.cover Q.cover P.covering Q.covering)

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C] {J : GrothendieckTopology C}
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X Y : C} {a : F.obj (.mk (op X))}
variable (P : LocalPresentation J η ((component η X).obj a)) (q : Y ⟶ X)

def pullRecoveryDataIso :
    (P.pull q).sourceData hFF ≅
      (F.toDescentData (fun _ : Unit => (P.pull q).cover)).obj ((F.map q.op.toLoc).toFunctor.obj a) :=
  P.pullSourceDataIso q hFF ≪≫ (P.parameterPull q).mapIso (P.sourceRecovery hFF) ≪≫
    (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso F
      (p := q) (f := fun _ : Unit => P.cover) (f' := fun _ : Unit => (P.pull q).cover)
      (p' := fun _ => pullback.snd q P.cover) (α := fun _ => ())
      (fun _ => pullback.condition.symm)).app a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem pullRecoveryDataIso_hom :
    (map η (fun _ : Unit => (P.pull q).cover)).map (P.pullRecoveryDataIso hFF q).hom ≫
      (canonicalObjIso η (fun _ : Unit => (P.pull q).cover) ((F.map q.op.toLoc).toFunctor.obj a)).hom ≫
      (B.toDescentData (fun _ : Unit => (P.pull q).cover)).map ((StackDescentTransformation.comparison η q).hom.app a) =
    ((P.pull q).sourceDataIso hFF).hom := by
  simp only [pullRecoveryDataIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [canonicalObjIso_pull]
  have hn := (pullIso η (fun _ : Unit => P.cover) (p := q)
    (f' := fun _ : Unit => (P.pull q).cover) (p' := fun _ => pullback.snd q P.cover) (α := fun _ => ())
    (fun _ => pullback.condition.symm)).hom.naturality (P.sourceRecovery hFF).hom
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, P.sourceRecovery_hom hFF]
  change (map η (fun _ : Unit => (P.pull q).cover)).map (P.pullSourceDataIso q hFF).hom ≫
    (pullSourceIso (q := q) (p := fun _ : Unit => P.cover)
      (p' := fun _ : Unit => (P.pull q).cover) (r := fun _ => pullback.snd q P.cover) (α := fun _ => ())
      (fun _ => pullback.condition.symm) (P.sourceData hFF) (P.sourceDataIso hFF)).hom = _
  simp [pullSourceDataIso]

end SquareKit.StackificationUniversal.LocalPresentation

namespace CategoryTheory
universe u₀ v₀ u₁ v₁ u₂ v₂ w₀ z₀ w₁ z₁ w₂ z₂
variable {A₀ : Type u₀} [Category.{v₀} A₀]
variable {A₁ : Type u₁} [Category.{v₁} A₁]
variable {A₂ : Type u₂} [Category.{v₂} A₂]
variable {D₀ : Type w₀} [Category.{z₀} D₀]
variable {D₁ : Type w₁} [Category.{z₁} D₁]
variable {D₂ : Type w₂} [Category.{z₂} D₂]
variable (E₀ : A₀ ≌ D₀) (E₁ : A₁ ≌ D₁) (E₂ : A₂ ≌ D₂)
variable (R₀₁ : D₀ ⥤ D₁) (R₁₂ : D₁ ⥤ D₂) (R₀₂ : D₀ ⥤ D₂)
variable (L₀₁ : A₀ ⥤ A₁) (L₁₂ : A₁ ⥤ A₂) (L₀₂ : A₀ ⥤ A₂)
variable (i₀₁ : E₀.functor ⋙ R₀₁ ≅ L₀₁ ⋙ E₁.functor)
variable (i₁₂ : E₁.functor ⋙ R₁₂ ≅ L₁₂ ⋙ E₂.functor)
variable (i₀₂ : E₀.functor ⋙ R₀₂ ≅ L₀₂ ⋙ E₂.functor)

def inverseSquareAcross : R₀₁ ⋙ E₁.inverse ≅ E₀.inverse ⋙ L₀₁ :=
  (Iso.isoCompInverse (H := E₁) (Functor.associator _ _ _ ≪≫
    Iso.inverseCompIso (G := E₀) i₀₁.symm)).symm

@[reassoc] theorem inverseSquareAcross_spec (d : D₀) :
    E₁.counitIso.inv.app (R₀₁.obj d) ≫
        E₁.functor.map ((inverseSquareAcross E₀ E₁ R₀₁ L₀₁ i₀₁).hom.app d) =
      R₀₁.map (E₀.counitIso.inv.app d) ≫ i₀₁.hom.app (E₀.inverse.obj d) := by
  dsimp [inverseSquareAcross, Iso.isoCompInverse, Iso.inverseCompIso]
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  rw [← E₁.counit_app_functor]
  simp [Equivalence.fun_inv_map, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem inverseSquareAcross_comp (c : R₀₁ ⋙ R₁₂ ≅ R₀₂) (l : L₀₁ ⋙ L₁₂ ≅ L₀₂)
    (hc : ∀ a : A₀, R₁₂.map (i₀₁.hom.app a) ≫ i₁₂.hom.app (L₀₁.obj a) ≫
      E₂.functor.map (l.hom.app a) = c.hom.app (E₀.functor.obj a) ≫ i₀₂.hom.app a)
    (d : D₀) :
    (inverseSquareAcross E₁ E₂ R₁₂ L₁₂ i₁₂).hom.app (R₀₁.obj d) ≫
      L₁₂.map ((inverseSquareAcross E₀ E₁ R₀₁ L₀₁ i₀₁).hom.app d) ≫
      l.hom.app (E₀.inverse.obj d) =
    E₂.inverse.map (c.hom.app d) ≫
      (inverseSquareAcross E₀ E₂ R₀₂ L₀₂ i₀₂).hom.app d := by
  apply E₂.functor.map_injective
  apply (cancel_epi (E₂.counitIso.inv.app (R₁₂.obj (R₀₁.obj d)))).mp
  simp only [Functor.map_comp]
  rw [inverseSquareAcross_spec_assoc]
  simp only [Equivalence.fun_inv_map, Category.assoc, Equivalence.counit, Equivalence.counitInv]
  rw [inverseSquareAcross_spec]
  have hn := i₁₂.hom.naturality ((inverseSquareAcross E₀ E₁ R₀₁ L₀₁ i₀₁).hom.app d)
  dsimp at hn
  rw [← reassoc_of% hn]
  rw [← Functor.map_comp_assoc, inverseSquareAcross_spec]
  rw [Functor.map_comp, Category.assoc, hc]
  have hn := c.hom.naturality (E₀.counitIso.inv.app d)
  dsimp at hn
  rw [← Category.assoc, hn]
  simp [Functor.comp_obj]


theorem inverseSquareAcross_canonical (a : A₀) :
    E₁.inverse.map (i₀₁.hom.app a) ≫ E₁.unitIso.inv.app (L₀₁.obj a) =
      (inverseSquareAcross E₀ E₁ R₀₁ L₀₁ i₀₁).hom.app (E₀.functor.obj a) ≫
        L₀₁.map (E₀.unitIso.inv.app a) := by
  apply E₁.functor.map_injective
  apply (cancel_epi (E₁.counitIso.inv.app (R₀₁.obj (E₀.functor.obj a)))).mp
  simp only [Functor.map_comp]
  rw [inverseSquareAcross_spec_assoc]
  rw [← E₁.counit_app_functor]
  simp only [Equivalence.fun_inv_map, Equivalence.counit, Equivalence.counitInv,
    Category.assoc]
  have hn := i₀₁.hom.naturality (E₀.unitIso.inv.app a)
  dsimp at hn
  rw [← hn, ← Functor.map_comp_assoc, ← E₀.counit_app_functor]
  simp

end CategoryTheory

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v' t t'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable (θ : F ⟶ T) [T.IsStack J]
variable {ι : Type t} {X : C} {U : ι → C} {p : ∀ i, U i ⟶ X}
variable {ι' : Type t'} {X' : C} {U' : ι' → C} {p' : ∀ i, U' i ⟶ X'}
variable {q : X' ⟶ X} {α : ι' → ι} {r : ∀ i, U' i ⟶ U (α i)}
variable (w : ∀ i, r i ≫ p (α i) = p' i ≫ q)
variable (hp : Sieve.ofArrows _ p ∈ J X) (hp' : Sieve.ofArrows _ p' ∈ J X')

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem effectiveCanonical_pull (a : F.obj (.mk (op X))) :
    (realization θ hp').map
        ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso F w).hom.app a) ≫
      (effectiveCanonical θ hp' ((F.map q.op.toLoc).toFunctor.obj a)).hom ≫
      (comparison θ q).hom.app a =
    (realizationPullIso w θ hp hp').hom.app ((F.toDescentData p).obj a) ≫
      (T.map q.op.toLoc).toFunctor.map (effectiveCanonical θ hp a).hom := by
  dsimp [effectiveCanonical, realizationPullIso, realization]
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  have hn := (descentEquivalence T hp').unitIso.inv.naturality ((comparison θ q).hom.app a)
  dsimp at hn
  change (descentEquivalence T hp').inverse.map ((T.toDescentData p').map ((comparison θ q).hom.app a)) ≫ _ = _ at hn
  rw [← hn, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [canonicalObjIso_pull θ w a]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (effectivePullIso w hp hp').inv.naturality (canonicalObjIso θ p a).hom
  dsimp at hn
  rw [← reassoc_of% hn]
  congr 1
  congr 1
  exact inverseSquareAcross_canonical (descentEquivalence T hp) (descentEquivalence T hp') _ _ _
    ((component θ X).obj a)

end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C] {J : GrothendieckTopology C}
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X Y : C} {a : F.obj (.mk (op X))}
variable (P : LocalPresentation J η ((component η X).obj a)) (q : Y ⟶ X)
variable (θ : F ⟶ T) [T.IsStack J]

set_option backward.isDefEq.respectTransparency false in
theorem pullRecoveryValue_hom :
    (realization θ (P.pull q).covering).map (P.pullRecoveryDataIso hFF q).hom ≫
      (effectiveCanonical θ (P.pull q).covering ((F.map q.op.toLoc).toFunctor.obj a)).hom ≫
      (StackDescentTransformation.comparison θ q).hom.app a =
    (P.pullValueIso q hFF θ).hom ≫
      (T.map q.op.toLoc).toFunctor.map (P.valueRecovery hFF θ).hom := by
  simp only [pullRecoveryDataIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [effectiveCanonical_pull θ _ P.covering (P.pull q).covering]
  have hn := (realizationPullIso (p := fun _ : Unit => P.cover) (q := q)
    (p' := fun _ : Unit => (P.pull q).cover) (r := fun _ => pullback.snd q P.cover) (α := fun _ => ())
    (fun _ => pullback.condition.symm) θ P.covering (P.pull q).covering).hom.naturality
      (P.sourceRecovery hFF).hom
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← Functor.map_comp, ← P.valueRecovery_hom θ hFF]
  simp [pullValueIso, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem pullValueIso_recovery
    (Q : LocalPresentation J η ((component η Y).obj ((F.map q.op.toLoc).toFunctor.obj a))) :
    Q.mapTo hFF (P.pull q) θ ((StackDescentTransformation.comparison η q).hom.app a) ≫
      (P.pullValueIso q hFF θ).hom ≫
      (T.map q.op.toLoc).toFunctor.map (P.valueRecovery hFF θ).hom =
    (Q.valueRecovery hFF θ).hom ≫ (StackDescentTransformation.comparison θ q).hom.app a := by
  rw [← P.pullRecoveryValue_hom hFF q θ]
  rw [← Category.assoc, ← Category.assoc]
  have he := Q.mapTo_recoveryAlong hFF (P.pull q) (P.pullRecoveryDataIso hFF q)
    ((StackDescentTransformation.comparison η q).app a) (P.pullRecoveryDataIso_hom hFF q) θ
  simpa only [Category.assoc, Iso.app_hom, Cat.Hom.comp_toFunctor, Functor.comp_obj] using
    congrArg (· ≫ (StackDescentTransformation.comparison θ q).hom.app a) he

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal.ParameterComposition
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} [T.IsStack J]
variable {X₀ X₁ X₂ U₀ U₁ U₂ : C}
variable (f₀ : U₀ ⟶ X₀) (f₁ : U₁ ⟶ X₁) (f₂ : U₂ ⟶ X₂)
variable (q₀₁ : X₁ ⟶ X₀) (q₁₂ : X₂ ⟶ X₁)
variable (r₀₁ : U₁ ⟶ U₀) (r₁₂ : U₂ ⟶ U₁)
variable (w₀₁ : r₀₁ ≫ f₀ = f₁ ≫ q₀₁) (w₁₂ : r₁₂ ≫ f₁ = f₂ ≫ q₁₂)
variable (hf₀ : Sieve.ofArrows _ (fun _ : Unit => f₀) ∈ J X₀)
  (hf₁ : Sieve.ofArrows _ (fun _ : Unit => f₁) ∈ J X₁)
  (hf₂ : Sieve.ofArrows _ (fun _ : Unit => f₂) ∈ J X₂)

abbrev firstEffective := effectivePullIso (T := T) (p := fun _ : Unit => f₀)
  (p' := fun _ : Unit => f₁) (q := q₀₁) (r := fun _ => r₀₁) (α := fun _ => ())
  (fun _ => w₀₁) hf₀ hf₁
abbrev secondEffective := effectivePullIso (T := T) (p := fun _ : Unit => f₁)
  (p' := fun _ : Unit => f₂) (q := q₁₂) (r := fun _ => r₁₂) (α := fun _ => ())
  (fun _ => w₁₂) hf₁ hf₂
abbrev compositeEffective := effectivePullIso (T := T) (p := fun _ : Unit => f₀)
  (p' := fun _ : Unit => f₂) (q := q₁₂ ≫ q₀₁) (r := fun _ => r₁₂ ≫ r₀₁) (α := fun _ => ())
  (fun _ => by simp only [Category.assoc, w₀₁, reassoc_of% w₁₂]) hf₀ hf₂

set_option backward.isDefEq.respectTransparency false in
theorem effectivePullComp (D : T.DescentData (fun _ : Unit => f₀)) :
    (secondEffective f₁ f₂ q₁₂ r₁₂ w₁₂ hf₁ hf₂).inv.app
        ((firstPull T f₀ f₁ q₀₁ r₀₁ w₀₁).obj D) ≫
      (T.map q₁₂.op.toLoc).toFunctor.map
        ((firstEffective f₀ f₁ q₀₁ r₀₁ w₀₁ hf₀ hf₁).inv.app D) ≫
      (T.mapComp' q₀₁.op.toLoc q₁₂.op.toLoc (q₁₂ ≫ q₀₁).op.toLoc (by grind)).inv.toNatTrans.app
        ((descentEquivalence T hf₀).inverse.obj D) =
    (descentEquivalence T hf₂).inverse.map
        ((pullCompIso T f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂).hom.app D) ≫
      (compositeEffective f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂ hf₀ hf₂).inv.app D :=
  inverseSquareAcross_comp (descentEquivalence T hf₀) (descentEquivalence T hf₁)
    (descentEquivalence T hf₂) _ _ _ _ _ _ _ _ _ _
    (Cat.Hom.toNatIso (T.mapComp' q₀₁.op.toLoc q₁₂.op.toLoc (q₁₂ ≫ q₀₁).op.toLoc (by grind))).symm
    (canonicalPullComp T f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂) D

end SquareKit.StackificationUniversal.ParameterComposition

namespace SquareKit.StackificationUniversal.ParameterComposition
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} [T.IsStack J]
variable {X₀ X₁ X₂ U₀ U₁ U₂ : C}
variable (f₀ : U₀ ⟶ X₀) (f₁ : U₁ ⟶ X₁) (f₂ : U₂ ⟶ X₂)
variable (q₀₁ : X₁ ⟶ X₀) (q₁₂ : X₂ ⟶ X₁)
variable (r₀₁ : U₁ ⟶ U₀) (r₁₂ : U₂ ⟶ U₁)
variable (w₀₁ : r₀₁ ≫ f₀ = f₁ ≫ q₀₁) (w₁₂ : r₁₂ ≫ f₁ = f₂ ≫ q₁₂)
variable (θ : F ⟶ T)
variable (hf₀ : Sieve.ofArrows _ (fun _ : Unit => f₀) ∈ J X₀)
  (hf₁ : Sieve.ofArrows _ (fun _ : Unit => f₁) ∈ J X₁)
  (hf₂ : Sieve.ofArrows _ (fun _ : Unit => f₂) ∈ J X₂)

abbrev firstRealization := realizationPullIso (p := fun _ : Unit => f₀)
  (p' := fun _ : Unit => f₁) (q := q₀₁) (r := fun _ => r₀₁) (α := fun _ => ())
  (fun _ => w₀₁) θ hf₀ hf₁
abbrev secondRealization := realizationPullIso (p := fun _ : Unit => f₁)
  (p' := fun _ : Unit => f₂) (q := q₁₂) (r := fun _ => r₁₂) (α := fun _ => ())
  (fun _ => w₁₂) θ hf₁ hf₂
abbrev compositeRealization := realizationPullIso (p := fun _ : Unit => f₀)
  (p' := fun _ : Unit => f₂) (q := q₁₂ ≫ q₀₁) (r := fun _ => r₁₂ ≫ r₀₁) (α := fun _ => ())
  (fun _ => by simp only [Category.assoc, w₀₁, reassoc_of% w₁₂]) θ hf₀ hf₂

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem realizationPullComp (D : F.DescentData (fun _ : Unit => f₀)) :
    (secondRealization f₁ f₂ q₁₂ r₁₂ w₁₂ θ hf₁ hf₂).hom.app
        ((firstPull F f₀ f₁ q₀₁ r₀₁ w₀₁).obj D) ≫
      (T.map q₁₂.op.toLoc).toFunctor.map
        ((firstRealization f₀ f₁ q₀₁ r₀₁ w₀₁ θ hf₀ hf₁).hom.app D) ≫
      (T.mapComp' q₀₁.op.toLoc q₁₂.op.toLoc (q₁₂ ≫ q₀₁).op.toLoc (by grind)).inv.toNatTrans.app
        ((realization θ hf₀).obj D) =
    (realization θ hf₂).map
        ((pullCompIso F f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂).hom.app D) ≫
      (compositeRealization f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂ θ hf₀ hf₂).hom.app D := by
  dsimp [firstRealization, secondRealization, compositeRealization, realizationPullIso, realization]
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  have hn := (secondEffective (T := T) f₁ f₂ q₁₂ r₁₂ w₁₂ hf₁ hf₂).inv.naturality
    ((pullIso θ (fun _ : Unit => f₀) (p := q₀₁)
      (f' := fun _ : Unit => f₁) (p' := fun _ => r₀₁) (α := fun _ => ())
      (fun _ => w₀₁)).hom.app D)
  dsimp at hn
  rw [← reassoc_of% hn, ← Functor.map_comp_assoc]
  have hc := congrArg Iso.hom (transformationPullComp f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂ θ D)
  dsimp at hc
  rw [hc]
  simp only [Functor.map_comp, Category.assoc]
  have he := effectivePullComp (T := T) f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂ hf₀ hf₁ hf₂ ((map θ (fun _ : Unit => f₀)).obj D)
  dsimp only [firstEffective, secondEffective, compositeEffective, firstPull] at he
  dsimp at he
  rw [he]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem realizationPullComp' (q₀₂ : X₂ ⟶ X₀) (hq : q₁₂ ≫ q₀₁ = q₀₂)
    (r₀₂ : U₂ ⟶ U₀) (hr : r₁₂ ≫ r₀₁ = r₀₂)
    (D : F.DescentData (fun _ : Unit => f₀)) :
    (secondRealization f₁ f₂ q₁₂ r₁₂ w₁₂ θ hf₁ hf₂).hom.app
        ((firstPull F f₀ f₁ q₀₁ r₀₁ w₀₁).obj D) ≫
      (T.map q₁₂.op.toLoc).toFunctor.map
        ((firstRealization f₀ f₁ q₀₁ r₀₁ w₀₁ θ hf₀ hf₁).hom.app D) ≫
      (T.mapComp' q₀₁.op.toLoc q₁₂.op.toLoc q₀₂.op.toLoc
        (by simpa using congrArg (fun g => g.op.toLoc) hq)).inv.toNatTrans.app
          ((realization θ hf₀).obj D) =
    (realization θ hf₂).map
      ((Pseudofunctor.DescentData.pullFunctorCompIso F
        (f := fun _ : Unit => f₀) (f' := fun _ : Unit => f₁) (f'' := fun _ : Unit => f₂)
        (p := q₀₁) (q := q₁₂) (α := fun _ : Unit => ()) (β := fun _ : Unit => ())
        (p' := fun _ => r₀₁) (q' := fun _ => r₁₂) (r' := fun _ => r₀₂)
        (fun _ => w₀₁) (fun _ => w₁₂) q₀₂ hq (fun _ => hr)).hom.app D) ≫
      (realizationPullIso (p := fun _ : Unit => f₀) (p' := fun _ : Unit => f₂)
        (q := q₀₂) (r := fun _ => r₀₂) (α := fun _ => ())
        (fun _ => by rw [← hq, ← hr]; simp only [Category.assoc, w₀₁, reassoc_of% w₁₂])
        θ hf₀ hf₂).hom.app D := by
  subst q₀₂
  subst r₀₂
  exact realizationPullComp f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂ θ hf₀ hf₁ hf₂ D

end SquareKit.StackificationUniversal.ParameterComposition

namespace SquareKit.StackificationUniversal.ParameterComposition
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C]
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} (η : F ⟶ B)
variable {X₀ X₁ X₂ U₀ U₁ U₂ : C}
variable (f₀ : U₀ ⟶ X₀) (f₁ : U₁ ⟶ X₁) (f₂ : U₂ ⟶ X₂)
variable (q₀₁ : X₁ ⟶ X₀) (q₁₂ : X₂ ⟶ X₁)
variable (r₀₁ : U₁ ⟶ U₀) (r₁₂ : U₂ ⟶ U₁)
variable (w₀₁ : r₀₁ ≫ f₀ = f₁ ≫ q₀₁) (w₁₂ : r₁₂ ≫ f₁ = f₂ ≫ q₁₂)
variable {b : B.obj (.mk (op X₀))} (D : F.DescentData (fun _ : Unit => f₀))
variable (e : (map η (fun _ : Unit => f₀)).obj D ≅
  (B.toDescentData (fun _ : Unit => f₀)).obj b)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem pullSourceIso_comp' (q₀₂ : X₂ ⟶ X₀) (hq : q₁₂ ≫ q₀₁ = q₀₂)
    (r₀₂ : U₂ ⟶ U₀) (hr : r₁₂ ≫ r₀₁ = r₀₂) :
    (pullSourceIso (p := fun _ : Unit => f₁) (p' := fun _ : Unit => f₂)
      (q := q₁₂) (α := fun _ : Unit => ()) (r := fun _ => r₁₂) (fun _ => w₁₂)
      ((firstPull F f₀ f₁ q₀₁ r₀₁ w₀₁).obj D)
      (pullSourceIso (p := fun _ : Unit => f₀) (p' := fun _ : Unit => f₁)
        (q := q₀₁) (α := fun _ : Unit => ()) (r := fun _ => r₀₁) (fun _ => w₀₁) D e)).hom ≫
    (B.toDescentData (fun _ : Unit => f₂)).map
      ((B.mapComp' q₀₁.op.toLoc q₁₂.op.toLoc q₀₂.op.toLoc (by simpa using congrArg (fun g => g.op.toLoc) hq)).inv.toNatTrans.app b) =
    (map η (fun _ : Unit => f₂)).map
      ((Pseudofunctor.DescentData.pullFunctorCompIso F
        (f := fun _ : Unit => f₀) (f' := fun _ : Unit => f₁) (f'' := fun _ : Unit => f₂)
        (p := q₀₁) (q := q₁₂) (α := fun _ : Unit => ()) (β := fun _ : Unit => ())
        (p' := fun _ => r₀₁) (q' := fun _ => r₁₂) (r' := fun _ => r₀₂)
        (fun _ => w₀₁) (fun _ => w₁₂) q₀₂ hq (fun _ => hr)).hom.app D) ≫
    (pullSourceIso (p := fun _ : Unit => f₀) (p' := fun _ : Unit => f₂)
      (q := q₀₂) (α := fun _ : Unit => ()) (r := fun _ => r₀₂)
      (fun _ => by rw [← hq, ← hr]; simp only [Category.assoc, w₀₁, reassoc_of% w₁₂]) D e).hom := by
  subst q₀₂
  subst r₀₂
  exact pullSourceIso_comp η f₀ f₁ f₂ q₀₁ q₁₂ r₀₁ r₁₂ w₀₁ w₁₂ D e
end SquareKit.StackificationUniversal.ParameterComposition

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v' t t'
variable {C : Type u} [Category.{v} C]
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B}
variable {ι : Type t} {X : C} {U : ι → C} {p : ∀ i, U i ⟶ X}
variable {ι' : Type t'} {X' : C} {U' : ι' → C} {p' : ∀ i, U' i ⟶ X'}
variable {q : X' ⟶ X} {α : ι' → ι} {r : ∀ i, U' i ⟶ U (α i)}
variable (w : ∀ i, r i ≫ p (α i) = p' i ≫ q)
variable {b : B.obj (.mk (op X))} {D E : F.DescentData p}
variable (e : (map η p).obj D ≅ (B.toDescentData p).obj b)
variable (e' : (map η p).obj E ≅ (B.toDescentData p).obj b)

set_option backward.isDefEq.respectTransparency false in
theorem pullSourceIso_naturality (h : D ⟶ E)
    (he : (map η p).map h ≫ e'.hom = e.hom) :
    (map η p').map ((Pseudofunctor.DescentData.pullFunctor F w).map h) ≫
      (pullSourceIso w E e').hom = (pullSourceIso w D e).hom := by
  simp only [pullSourceIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc]
  have hn := (pullIso η p w).hom.naturality h
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, he]
end SquareKit.StackificationUniversal
namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v' t t'
variable {C : Type u} [Category.{v} C]
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B}
variable {ι : Type t} {X : C} {U : ι → C} {p : ∀ i, U i ⟶ X}
variable {ι' : Type t'} {X' : C} {U' : ι' → C} {p' : ∀ i, U' i ⟶ X'}
variable {q : X' ⟶ X} {α : ι' → ι} {r : ∀ i, U' i ⟶ U (α i)}
variable (w : ∀ i, r i ≫ p (α i) = p' i ≫ q)
variable {b c : B.obj (.mk (op X))} (D : F.DescentData p)
variable (e : (map η p).obj D ≅ (B.toDescentData p).obj b) (t : b ≅ c)
set_option backward.isDefEq.respectTransparency false in
theorem pullSourceIso_postcomp :
    (pullSourceIso w D (e ≪≫ (B.toDescentData p).mapIso t)).hom =
    (pullSourceIso w D e).hom ≫ (B.toDescentData p').map
      ((B.map q.op.toLoc).toFunctor.map t.hom) := by
  simp only [pullSourceIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  have hn := (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso B w).hom.naturality t.hom
  dsimp only [Functor.comp_map] at hn
  rw [hn]
end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable {X Y R : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable (r : R ⟶ P.domain) (k : R ⟶ X) (hr : r ≫ P.cover = k) (q : Y ⟶ X)

def pullRefinementMap : pullback q k ⟶ (P.pull q).domain :=
  pullback.lift (pullback.fst q k) (pullback.snd q k ≫ r)
    (by simp only [Category.assoc, hr, pullback.condition])

theorem pullRefinementMap_cover : P.pullRefinementMap r k hr q ≫ (P.pull q).cover =
    pullback.fst q k := pullback.lift_fst _ _ _

theorem pullRefinementMap_snd : P.pullRefinementMap r k hr q ≫ pullback.snd q P.cover =
    pullback.snd q k ≫ r := pullback.lift_snd _ _ _

abbrev commonParameterPull (H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) :=
  Pseudofunctor.DescentData.pullFunctor H (p := q)
    (f := fun _ : Unit => k) (f' := fun _ : Unit => pullback.fst q k)
    (p' := fun _ => pullback.snd q k) (α := fun _ : Unit => ())
    (fun _ => pullback.condition.symm)

def parameterThenRefinement (H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) :=
  Pseudofunctor.DescentData.pullFunctorCompIso H
    (p := q) (q := 𝟙 Y) (f := fun _ : Unit => P.cover)
    (f' := fun _ : Unit => (P.pull q).cover) (f'' := fun _ : Unit => pullback.fst q k)
    (p' := fun _ => pullback.snd q P.cover) (q' := fun _ => P.pullRefinementMap r k hr q)
    (r' := fun _ => pullback.snd q k ≫ r) (α := fun _ : Unit => ()) (β := fun _ : Unit => ())
    (fun _ => pullback.condition.symm)
    (fun _ => (P.pullRefinementMap_cover r k hr q).trans (Category.comp_id _).symm)
    q (Category.id_comp _) (fun _ => P.pullRefinementMap_snd r k hr q)

def refinementThenParameter (H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) :=
  Pseudofunctor.DescentData.pullFunctorCompIso H
    (p := 𝟙 X) (q := q) (f := fun _ : Unit => P.cover)
    (f' := fun _ : Unit => k) (f'' := fun _ : Unit => pullback.fst q k)
    (p' := fun _ => r) (q' := fun _ => pullback.snd q k)
    (r' := fun _ => pullback.snd q k ≫ r) (α := fun _ : Unit => ()) (β := fun _ : Unit => ())
    (fun _ => hr.trans (Category.comp_id _).symm)
    (fun _ => pullback.condition.symm)
    q (Category.comp_id _) (fun _ => rfl)

variable (hFF : ∀ X : C, (component η X).FullyFaithful)

/-- Pulling the parameter and refining the local source presentation commute. -/
def pullRefinementIso :
    ((P.pull q).refinement (P.pullRefinementMap r k hr q) (pullback.fst q k)
      (P.pullRefinementMap_cover r k hr q)).obj ((P.pull q).sourceData hFF) ≅
      (commonParameterPull k q F).obj ((P.refinement r k hr).obj (P.sourceData hFF)) :=
  ((P.pull q).refinement (P.pullRefinementMap r k hr q) (pullback.fst q k)
    (P.pullRefinementMap_cover r k hr q)).mapIso (P.pullSourceDataIso q hFF) ≪≫
      (P.parameterThenRefinement r k hr q F).app (P.sourceData hFF) ≪≫
        ((P.refinementThenParameter r k hr q F).app (P.sourceData hFF)).symm

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration ParameterComposition
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable {X Y R : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable (r : R ⟶ P.domain) (k : R ⟶ X) (hr : r ≫ P.cover = k) (q : Y ⟶ X)
variable (hFF : ∀ X : C, (component η X).FullyFaithful)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem pullRefinementIso_source :
    (map η (fun _ : Unit => pullback.fst q k)).map (P.pullRefinementIso r k hr q hFF).hom ≫
      (pullSourceIso (p := fun _ : Unit => k) (p' := fun _ : Unit => pullback.fst q k)
        (q := q) (r := fun _ => pullback.snd q k) (α := fun _ => ())
        (fun _ => pullback.condition.symm) ((P.refinement r k hr).obj (P.sourceData hFF))
        (P.refinedSourceIso hFF r k hr)).hom =
    ((P.pull q).refinedSourceIso hFF (P.pullRefinementMap r k hr q) (pullback.fst q k)
      (P.pullRefinementMap_cover r k hr q)).hom := by
  have hA := pullSourceIso_comp' η P.cover (P.pull q).cover (pullback.fst q k)
    q (𝟙 Y) (pullback.snd q P.cover) (P.pullRefinementMap r k hr q)
    pullback.condition.symm
    ((P.pullRefinementMap_cover r k hr q).trans (Category.comp_id _).symm)
    (P.sourceData hFF) (P.sourceDataIso hFF) q (Category.id_comp _)
    (pullback.snd q k ≫ r) (P.pullRefinementMap_snd r k hr q)
  have hB := pullSourceIso_comp' η P.cover k (pullback.fst q k)
    (𝟙 X) q r (pullback.snd q k) (hr.trans (Category.comp_id _).symm)
    pullback.condition.symm (P.sourceData hFF) (P.sourceDataIso hFF)
    q (Category.comp_id _) (pullback.snd q k ≫ r) rfl
  simp only [op_id, Quiver.Hom.id_toLoc, Pseudofunctor.mapComp'_comp_id_inv_app] at hA
  simp only [op_id, Quiver.Hom.id_toLoc, Pseudofunctor.mapComp'_id_comp_inv_app] at hB
  have hb :
      (pullSourceIso (p := fun _ : Unit => k) (p' := fun _ : Unit => pullback.fst q k)
        (q := q) (r := fun _ => pullback.snd q k) (α := fun _ => ())
        (fun _ => pullback.condition.symm) ((P.refinement r k hr).obj (P.sourceData hFF))
        (P.refinedSourceIso hFF r k hr)).hom =
      (map η (fun _ : Unit => pullback.fst q k)).map
        ((P.refinementThenParameter r k hr q F).hom.app (P.sourceData hFF)) ≫
      (pullSourceIso (p := fun _ : Unit => P.cover) (p' := fun _ : Unit => pullback.fst q k)
        (q := q) (r := fun _ => pullback.snd q k ≫ r) (α := fun _ => ())
        (fun _ => by simp [Category.assoc, hr, pullback.condition])
        (P.sourceData hFF) (P.sourceDataIso hFF)).hom := by
    dsimp only [refinedSourceIso]
    rw [pullSourceIso_postcomp]
    exact hB
  rw [hb]
  simp only [pullRefinementIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc _
    ((P.refinementThenParameter r k hr q F).inv.app (P.sourceData hFF))
    ((P.refinementThenParameter r k hr q F).hom.app (P.sourceData hFF))]
  simp only [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  dsimp only [parameterThenRefinement]
  rw [← hA]
  have hn := pullSourceIso_naturality
    (p := fun _ : Unit => (P.pull q).cover) (p' := fun _ : Unit => pullback.fst q k)
    (q := 𝟙 Y) (r := fun _ => P.pullRefinementMap r k hr q) (α := fun _ => ())
    (fun _ => (P.pullRefinementMap_cover r k hr q).trans (Category.comp_id _).symm)
    ((P.pull q).sourceDataIso hFF)
    (pullSourceIso (p := fun _ : Unit => P.cover) (p' := fun _ : Unit => (P.pull q).cover)
      (q := q) (r := fun _ => pullback.snd q P.cover) (α := fun _ => ())
      (fun _ => pullback.condition.symm) (P.sourceData hFF) (P.sourceDataIso hFF))
    (P.pullSourceDataIso q hFF).hom (by simp [pullSourceDataIso])
  rw [← Category.assoc, hn]
  rfl

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable {X Y R : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable (r : R ⟶ P.domain) (k : R ⟶ X) (hr : r ≫ P.cover = k) (q : Y ⟶ X)
variable (θ : F ⟶ T) [T.IsStack J]
variable (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X)
  (hk' : Sieve.ofArrows _ (fun _ : Unit => pullback.fst q k) ∈ J Y)

def refinementCompositeRealization :=
  realizationPullIso (p := fun _ : Unit => P.cover)
    (p' := fun _ : Unit => pullback.fst q k) (q := q)
    (r := fun _ => pullback.snd q k ≫ r) (α := fun _ => ())
    (fun _ => by simp only [Category.assoc, hr, pullback.condition]) θ P.covering hk'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem parameterThenRefinement_value (D : F.DescentData (fun _ : Unit => P.cover)) :
    (realizationRefinementIso θ (P.pull q).cover (P.pullRefinementMap r k hr q)
      (pullback.fst q k) (P.pullRefinementMap_cover r k hr q) (P.pull q).covering hk').hom.app
        ((P.parameterPull q).obj D) ≫
      (realizationPullIso (p := fun _ : Unit => P.cover) (q := q)
        (p' := fun _ : Unit => (P.pull q).cover) (r := fun _ => pullback.snd q P.cover)
        (α := fun _ => ()) (fun _ => pullback.condition.symm)
        θ P.covering (P.pull q).covering).hom.app D =
    (realization θ hk').map ((P.parameterThenRefinement r k hr q F).hom.app D) ≫
      (P.refinementCompositeRealization r k hr q θ hk').hom.app D := by
  have hc := ParameterComposition.realizationPullComp' P.cover (P.pull q).cover
    (pullback.fst q k) q (𝟙 Y) (pullback.snd q P.cover) (P.pullRefinementMap r k hr q)
    pullback.condition.symm ((P.pullRefinementMap_cover r k hr q).trans (Category.comp_id _).symm)
    θ P.covering (P.pull q).covering hk' q (Category.id_comp q)
    (pullback.snd q k ≫ r) (P.pullRefinementMap_snd r k hr q) D
  dsimp [ParameterComposition.firstRealization, ParameterComposition.secondRealization,
    realizationRefinementIso, refinementCompositeRealization, parameterThenRefinement] at hc ⊢
  simp only [Pseudofunctor.mapComp'_comp_id_inv_app] at hc
  have hn := (Cat.Hom.toNatIso (T.mapId (.mk (op Y)))).hom.naturality
    ((realizationPullIso (p := fun _ : Unit => P.cover) (q := q)
      (p' := fun _ : Unit => (P.pull q).cover) (r := fun _ => pullback.snd q P.cover)
      (α := fun _ => ()) (fun _ => pullback.condition.symm)
      θ P.covering (P.pull q).covering).hom.app D)
  dsimp at hn
  simp only [Category.comp_id, Category.assoc]
  rw [← hn]
  exact hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem refinementThenParameter_value (D : F.DescentData (fun _ : Unit => P.cover)) :
    (realizationPullIso (p := fun _ : Unit => k) (q := q)
      (p' := fun _ : Unit => pullback.fst q k) (r := fun _ => pullback.snd q k)
      (α := fun _ => ()) (fun _ => pullback.condition.symm) θ hk hk').hom.app
        ((P.refinement r k hr).obj D) ≫
      (T.map q.op.toLoc).toFunctor.map
        ((realizationRefinementIso θ P.cover r k hr P.covering hk).hom.app D) =
    (realization θ hk').map ((P.refinementThenParameter r k hr q F).hom.app D) ≫
      (P.refinementCompositeRealization r k hr q θ hk').hom.app D := by
  have hc := ParameterComposition.realizationPullComp' P.cover k (pullback.fst q k)
    (𝟙 X) q r (pullback.snd q k) (hr.trans (Category.comp_id k).symm) pullback.condition.symm
    θ P.covering hk hk' q (Category.comp_id q) (pullback.snd q k ≫ r) rfl D
  simpa [ParameterComposition.firstRealization, ParameterComposition.secondRealization,
    realizationRefinementIso, refinementCompositeRealization, refinementThenParameter,
    Pseudofunctor.mapComp'_id_comp_inv_app, Category.assoc] using hc


variable (hFF : ∀ X : C, (component η X).FullyFaithful)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem pullRefinementIso_value :
    (realization θ hk').map (P.pullRefinementIso r k hr q hFF).hom ≫
      (realizationPullIso (p := fun _ : Unit => k) (q := q)
        (p' := fun _ : Unit => pullback.fst q k) (r := fun _ => pullback.snd q k)
        (α := fun _ => ()) (fun _ => pullback.condition.symm) θ hk hk').hom.app
          ((P.refinement r k hr).obj (P.sourceData hFF)) ≫
      (T.map q.op.toLoc).toFunctor.map (P.refinedValueIso hFF r k hr θ hk).hom =
    ((P.pull q).refinedValueIso hFF (P.pullRefinementMap r k hr q)
      (pullback.fst q k) (P.pullRefinementMap_cover r k hr q) θ hk').hom ≫
      (P.pullValueIso q hFF θ).hom := by
  have ha := P.parameterThenRefinement_value r k hr q θ hk' (P.sourceData hFF)
  have hb := P.refinementThenParameter_value r k hr q θ hk hk' (P.sourceData hFF)
  have hn := (realizationRefinementIso θ (P.pull q).cover (P.pullRefinementMap r k hr q)
    (pullback.fst q k) (P.pullRefinementMap_cover r k hr q)
    (P.pull q).covering hk').hom.naturality (P.pullSourceDataIso q hFF).hom
  change (realization θ hk').map
    (((P.pull q).refinement (P.pullRefinementMap r k hr q) (pullback.fst q k)
      (P.pullRefinementMap_cover r k hr q)).map (P.pullSourceDataIso q hFF).hom) ≫ _ = _ at hn
  have he (D : F.DescentData (fun _ : Unit => P.cover)) :
      (P.refinedValueIso hFF r k hr θ hk).hom =
      (realizationRefinementIso θ P.cover r k hr P.covering hk).hom.app (P.sourceData hFF) := by
    simp [refinedValueIso, realizationRefinementIso, value, realization]
  rw [he (P.sourceData hFF), hb]
  dsimp only [pullRefinementIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  rw [Functor.map_comp, Category.assoc, ← ha, ← Category.assoc, hn]
  dsimp [pullValueIso, refinedValueIso, realizationRefinementIso, value, realization]
  simp only [Category.comp_id, Category.assoc]

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C]
variable (H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
variable {X U : C} (f : U ⟶ X)

def identityRefinementIso :
    Pseudofunctor.DescentData.pullFunctor H (p := 𝟙 X) (α := fun _ : Unit => ())
      (f := fun _ : Unit => f) (f' := fun _ : Unit => f)
      (p' := fun _ => 𝟙 U) (fun _ => by simp) ≅ 𝟭 (H.DescentData (fun _ : Unit => f)) :=
  Pseudofunctor.DescentData.pullFunctorIdIso H X

set_option backward.isDefEq.respectTransparency false in
theorem canonicalRefinementIso_id (b : H.obj (.mk (op X))) :
    (canonicalRefinementIso H f (𝟙 U) f (Category.id_comp _)).hom.app b =
    (identityRefinementIso H f).hom.app ((H.toDescentData (fun _ : Unit => f)).obj b) := by
  ext i
  cases i
  rw [canonicalRefinementIso_hom]
  dsimp [identityRefinementIso, Pseudofunctor.DescentData.pullFunctorIdIso,
    Pseudofunctor.DescentData.isoMk]
  simp [Pseudofunctor.mapComp'_comp_id_inv_app, Pseudofunctor.toDescentData,
    Pseudofunctor.DescentData.ofObj]
end SquareKit.StackificationUniversal
namespace CategoryTheory
universe u v u' v'
variable {A : Type u} [Category.{v} A] {D : Type u'} [Category.{v'} D]
variable (E : A ≌ D) (R : D ⥤ D) (i : E.functor ⋙ R ≅ E.functor) (r : R ≅ 𝟭 D)
theorem inverseSquare_identity (hi : ∀ a, i.hom.app a = r.hom.app (E.functor.obj a))
    (d : D) : (inverseSquare E E R i).hom.app d = E.inverse.map (r.hom.app d) := by
  apply E.functor.map_injective
  apply (cancel_epi (E.counitIso.inv.app (R.obj d))).mp
  rw [inverseSquare_spec, hi]
  have hn := r.hom.naturality (E.counitIso.inv.app d)
  dsimp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hn
  rw [hn]
  simpa only [Functor.id_map, Functor.id_obj, Functor.comp_map] using E.counitIso.inv.naturality (r.hom.app d)
end CategoryTheory

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C]
variable {F T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {X U : C} (f : U ⟶ X) (θ : F ⟶ T)

set_option backward.isDefEq.respectTransparency false in
theorem pullIso_identity (D : F.DescentData (fun _ : Unit => f)) :
    (pullIso θ (fun _ : Unit => f) (p := 𝟙 X) (f' := fun _ : Unit => f)
      (p' := fun _ => 𝟙 U) (α := fun _ : Unit => ()) (fun _ => by simp)).hom.app D ≫
      (identityRefinementIso T f).hom.app ((map θ _).obj D) =
    (map θ _).map ((identityRefinementIso F f).hom.app D) := by
  ext i
  cases i
  dsimp [pullIso, pullObjIso, identityRefinementIso, Pseudofunctor.DescentData.pullFunctorIdIso,
    Pseudofunctor.DescentData.isoMk, map, mapMap, mapObj]
  have h := congrArg (fun h => h.toNatTrans.app (D.obj ())) (θ.naturality_id (.mk (op U)))
  dsimp at h
  simpa only [comparison, component, op_id, Quiver.Hom.id_toLoc, Cat.Hom.toNatIso_hom, Category.comp_id, Category.id_comp] using h

variable {J : GrothendieckTopology C} [T.IsStack J]
variable (hf : Sieve.ofArrows _ (fun _ : Unit => f) ∈ J X)
set_option backward.isDefEq.respectTransparency false in
theorem realizationRefinementIso_id (D : F.DescentData (fun _ : Unit => f)) :
    (realizationRefinementIso θ f (𝟙 U) f (Category.id_comp _) hf hf).hom.app D =
    (realization θ hf).map ((identityRefinementIso F f).hom.app D) := by
  rw [realizationRefinementIso_hom]
  have hi := inverseSquare_identity (descentEquivalence T hf) _
    (canonicalRefinementIso T f (𝟙 U) f (Category.id_comp _))
    (identityRefinementIso T f) (canonicalRefinementIso_id T f) ((map θ _).obj D)
  dsimp only [effectiveRefinementIso]
  rw [hi, ← Functor.map_comp, pullIso_identity]
  rfl
end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X : C} {b c : B.obj (.mk (op X))}
variable (P : LocalPresentation J η b) (Q : LocalPresentation J η c)
variable (θ : F ⟶ T) [T.IsStack J]

set_option backward.isDefEq.respectTransparency false in
theorem refinedSourceIso_id :
    (P.refinedSourceIso hFF (𝟙 P.domain) P.cover (Category.id_comp _)).hom =
    (map η (fun _ : Unit => P.cover)).map
      ((identityRefinementIso F P.cover).hom.app (P.sourceData hFF)) ≫
      (P.sourceDataIso hFF).hom := by
  rw [P.refinedSourceIso_hom, canonicalRefinementIso_id]
  have hn := (identityRefinementIso B P.cover).hom.naturality (P.sourceDataIso hFF).hom
  dsimp only [Functor.id_map] at hn
  rw [hn, ← Category.assoc, pullIso_identity]

set_option backward.isDefEq.respectTransparency false in
theorem refinedValueIso_id :
    (P.refinedValueIso hFF (𝟙 P.domain) P.cover (Category.id_comp _) θ P.covering).hom =
    (realization θ P.covering).map
      ((identityRefinementIso F P.cover).hom.app (P.sourceData hFF)) := by
  simpa [realizationRefinementIso, refinedValueIso, realization, value, Category.assoc] using
    realizationRefinementIso_id P.cover θ P.covering (P.sourceData hFF)

variable [HasPullbacks C]
variable (s : P.domain ⟶ Q.domain) (hs : s ≫ Q.cover = P.cover)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem mapTo_from_sourceMap (h : b ⟶ c)
    (e : P.sourceData hFF ⟶ (Q.refinement s P.cover hs).obj (Q.sourceData hFF))
    (he : (map η (fun _ : Unit => P.cover)).map e ≫
        (Q.refinedSourceIso hFF s P.cover hs).hom =
      (P.sourceDataIso hFF).hom ≫ (B.toDescentData (fun _ : Unit => P.cover)).map h) :
    P.mapTo hFF Q θ h = (realization θ P.covering).map e ≫
      (Q.refinedValueIso hFF s P.cover hs θ P.covering).hom := by
  rw [P.mapTo_eq hFF Q θ (𝟙 P.domain) s P.cover (Category.id_comp _) hs P.covering]
  have hm : liftMap η hFF
      (P.refinedSourceIso hFF (𝟙 P.domain) P.cover (Category.id_comp _))
      (Q.refinedSourceIso hFF s P.cover hs) h =
      (identityRefinementIso F P.cover).hom.app (P.sourceData hFF) ≫ e := by
    apply (mapFullyFaithful η hFF).map_injective
    rw [map_liftMap, Functor.map_comp]
    apply (cancel_mono (Q.refinedSourceIso hFF s P.cover hs).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [he, P.refinedSourceIso_id]
    simp only [Category.assoc]
  dsimp only [mapOnRefinement]
  rw [hm, Functor.map_comp, ← P.refinedValueIso_id hFF θ]
  simp
end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackDescentTransformation
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v u' v' t
variable {C : Type u} [Category.{v} C]
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable (η : F ⟶ B) (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {ι : Type t} {X : C} {U : ι → C} {p : ∀ i, U i ⟶ X}
variable {D D' E E' : F.DescentData p} {b c : B.obj (.mk (op X))}
variable (eD : (map η p).obj D ≅ (B.toDescentData p).obj b)
  (eD' : (map η p).obj D' ≅ (B.toDescentData p).obj b)
  (eE : (map η p).obj E ≅ (B.toDescentData p).obj c)
  (eE' : (map η p).obj E' ≅ (B.toDescentData p).obj c)
variable (d : D ≅ D') (e : E ≅ E')

/-- Lifting an ambient arrow respects a change of its source cocycle representatives. -/
theorem liftMap_transport
    (hd : (map η p).map d.hom ≫ eD'.hom = eD.hom)
    (he : (map η p).map e.hom ≫ eE'.hom = eE.hom) (h : b ⟶ c) :
    d.hom ≫ liftMap η hFF eD' eE' h = liftMap η hFF eD eE h ≫ e.hom := by
  apply (mapFullyFaithful η hFF).map_injective
  simp only [Functor.map_comp, map_liftMap]
  apply (cancel_mono eE'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% hd, he]
  simp

end SquareKit.StackDescentTransformation

namespace CategoryTheory
universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃
variable {D : Type u₀} [Category.{v₀} D] {E : Type u₁} [Category.{v₁} E]
variable {T : Type u₂} [Category.{v₂} T] {T' : Type u₃} [Category.{v₃} T']
variable (R : D ⥤ E) (A : D ⥤ T) (B : E ⥤ T') (L : T ⥤ T')
variable (n : R ⋙ B ≅ A ⋙ L)
variable {d₀ d₁ : D} {e₀ e₁ : E} (d : e₀ ≅ R.obj d₀) (e : e₁ ≅ R.obj d₁)
variable (f : d₀ ⟶ d₁) (g : e₀ ⟶ e₁)
variable {v₀ v₁ : T} {w₀ w₁ : T'}
variable (i₀ : A.obj d₀ ≅ v₀) (i₁ : A.obj d₁ ≅ v₁)
variable (j₀ : B.obj e₀ ≅ w₀) (j₁ : B.obj e₁ ≅ w₁)
variable (k₀ : w₀ ≅ L.obj v₀) (k₁ : w₁ ≅ L.obj v₁)

/-- Conjugating a functorial square by its effective-value comparisons preserves its arrows. -/
theorem conjugate_map_square
    (h : d.hom ≫ R.map f = g ≫ e.hom)
    (h₀ : B.map d.hom ≫ n.hom.app d₀ ≫ L.map i₀.hom = j₀.hom ≫ k₀.hom)
    (h₁ : B.map e.hom ≫ n.hom.app d₁ ≫ L.map i₁.hom = j₁.hom ≫ k₁.hom) :
    (j₀.inv ≫ B.map g ≫ j₁.hom) ≫ k₁.hom =
      k₀.hom ≫ L.map (i₀.inv ≫ A.map f ≫ i₁.hom) := by
  apply (cancel_epi j₀.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← h₁, ← reassoc_of% h₀]
  simp only [Functor.map_comp]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_assoc]
  rw [← h, Functor.map_comp_assoc]
  have hn := n.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
end CategoryTheory

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable (hFF : ∀ X : C, (component η X).FullyFaithful)
variable {X Y R : C} {b c : B.obj (.mk (op X))}
variable (P : LocalPresentation J η b) (Q : LocalPresentation J η c)
variable (r : R ⟶ P.domain) (s : R ⟶ Q.domain) (k : R ⟶ X)
variable (hr : r ≫ P.cover = k) (hs : s ≫ Q.cover = k) (q : Y ⟶ X)

abbrev pulledRefinedSource (P : LocalPresentation J η b)
    (r : R ⟶ P.domain) (hr : r ≫ P.cover = k) :=
  pullSourceIso (p := fun _ : Unit => k) (p' := fun _ : Unit => pullback.fst q k)
    (q := q) (r := fun _ => pullback.snd q k) (α := fun _ : Unit => ())
    (fun _ => pullback.condition.symm) ((P.refinement r k hr).obj (P.sourceData hFF))
    (P.refinedSourceIso hFF r k hr)

theorem liftMap_pullRefinement (h : b ⟶ c) :
    (P.pullRefinementIso r k hr q hFF).hom ≫
      (commonParameterPull k q F).map
        (liftMap η hFF (P.refinedSourceIso hFF r k hr) (Q.refinedSourceIso hFF s k hs) h) =
    liftMap η hFF
      ((P.pull q).refinedSourceIso hFF (P.pullRefinementMap r k hr q) (pullback.fst q k)
        (P.pullRefinementMap_cover r k hr q))
      ((Q.pull q).refinedSourceIso hFF (Q.pullRefinementMap s k hs q) (pullback.fst q k)
        (Q.pullRefinementMap_cover s k hs q))
      ((B.map q.op.toLoc).toFunctor.map h) ≫ (Q.pullRefinementIso s k hs q hFF).hom := by
  rw [liftMap_pull]
  exact liftMap_transport η hFF _ _ _ _ _ _
    (P.pullRefinementIso_source r k hr q hFF)
    (Q.pullRefinementIso_source s k hs q hFF) _

variable (θ : F ⟶ T) [T.IsStack J]
variable (hk : Sieve.ofArrows _ (fun _ : Unit => k) ∈ J X)

abbrev commonRealizationPull := realizationPullIso
    (p := fun _ : Unit => k) (p' := fun _ : Unit => pullback.fst q k)
    (q := q) (r := fun _ => pullback.snd q k) (α := fun _ : Unit => ())
    (fun _ => pullback.condition.symm) θ hk
      (StackObjectPropertyDescent.singleton_pullback J k q hk)

theorem mapOnRefinement_pull (h : b ⟶ c) :
    (P.pull q).mapOnRefinement hFF (P.pullRefinementMap r k hr q) (pullback.fst q k)
      (P.pullRefinementMap_cover r k hr q) (Q.pull q) (Q.pullRefinementMap s k hs q)
      (Q.pullRefinementMap_cover s k hs q) θ
      (StackObjectPropertyDescent.singleton_pullback J k q hk)
      ((B.map q.op.toLoc).toFunctor.map h) ≫ (Q.pullValueIso q hFF θ).hom =
    (P.pullValueIso q hFF θ).hom ≫
      (T.map q.op.toLoc).toFunctor.map (P.mapOnRefinement hFF r k hr Q s hs θ hk h) := by
  exact conjugate_map_square (commonParameterPull k q F) (realization θ hk)
    (realization θ (StackObjectPropertyDescent.singleton_pullback J k q hk))
    (T.map q.op.toLoc).toFunctor (commonRealizationPull k q θ hk)
    (P.pullRefinementIso r k hr q hFF) (Q.pullRefinementIso s k hs q hFF)
    _ _ (P.refinedValueIso hFF r k hr θ hk) (Q.refinedValueIso hFF s k hs θ hk)
    _ _ (P.pullValueIso q hFF θ) (Q.pullValueIso q hFF θ)
    (P.liftMap_pullRefinement hFF Q r s k hr hs q h)
    (P.pullRefinementIso_value r k hr q θ hk _ hFF)
    (Q.pullRefinementIso_value s k hs q θ hk _ hFF)

/-- Effective presentation maps commute with arbitrary parameter substitution. -/
theorem mapTo_pull (h : b ⟶ c) :
    (P.pull q).mapTo hFF (Q.pull q) θ ((B.map q.op.toLoc).toFunctor.map h) ≫
      (Q.pullValueIso q hFF θ).hom =
    (P.pullValueIso q hFF θ).hom ≫ (T.map q.op.toLoc).toFunctor.map (P.mapTo hFF Q θ h) := by
  let k := pullback.fst P.cover Q.cover ≫ P.cover
  let r := pullback.fst P.cover Q.cover
  let s := pullback.snd P.cover Q.cover
  have hr : r ≫ P.cover = k := rfl
  have hs : s ≫ Q.cover = k := pullback.condition.symm
  have hk := StackObjectPropertyDescent.singleton_common J P.cover Q.cover P.covering Q.covering
  rw [(P.pull q).mapTo_eq hFF (Q.pull q) θ
    (P.pullRefinementMap r k hr q) (Q.pullRefinementMap s k hs q) (pullback.fst q k)
    (P.pullRefinementMap_cover r k hr q) (Q.pullRefinementMap_cover s k hs q)
    (StackObjectPropertyDescent.singleton_pullback J k q hk)]
  exact P.mapOnRefinement_pull hFF Q r s k hr hs q θ hk h

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable (hFF : ∀ X : C, (component η X).FullyFaithful)
variable (θ : F ⟶ T) [T.IsStack J] (hη : LocallyGenerating J η)
variable {X Y : C} (q : Y ⟶ X)

/-- The extension compares change of parameter with effective local presentation. -/
def extensionComparisonObj (b : B.obj (.mk (op X))) :
    (extensionFunctor hFF θ hη).obj ((B.map q.op.toLoc).toFunctor.obj b) ≅
      (T.map q.op.toLoc).toFunctor.obj ((extensionFunctor hFF θ hη).obj b) :=
  (presentation hη ((B.map q.op.toLoc).toFunctor.obj b)).mapToIso hFF θ
    ((presentation hη b).pull q) (Iso.refl _) ≪≫
      (presentation hη b).pullValueIso q hFF θ

/-- The comparison of parameter substitution is natural in every ambient arrow. -/
theorem extensionComparison_naturality {b c : B.obj (.mk (op X))} (h : b ⟶ c) :
    (extensionFunctor hFF θ hη).map ((B.map q.op.toLoc).toFunctor.map h) ≫
      (extensionComparisonObj hFF θ hη q c).hom =
    (extensionComparisonObj hFF θ hη q b).hom ≫
      (T.map q.op.toLoc).toFunctor.map ((extensionFunctor hFF θ hη).map h) := by
  let P := presentation hη b
  let Q := presentation hη c
  let P' := presentation hη ((B.map q.op.toLoc).toFunctor.obj b)
  let Q' := presentation hη ((B.map q.op.toLoc).toFunctor.obj c)
  change P'.mapTo hFF Q' θ ((B.map q.op.toLoc).toFunctor.map h) ≫
      (Q'.mapTo hFF (Q.pull q) θ (𝟙 _) ≫ (Q.pullValueIso q hFF θ).hom) =
    (P'.mapTo hFF (P.pull q) θ (𝟙 _) ≫ (P.pullValueIso q hFF θ).hom) ≫
      (T.map q.op.toLoc).toFunctor.map (P.mapTo hFF Q θ h)
  simp only [Category.assoc]
  rw [← P.mapTo_pull hFF Q q θ h]
  rw [reassoc_of% P'.mapTo_comp hFF Q' θ (Q.pull q),
    reassoc_of% P'.mapTo_comp hFF (P.pull q) θ (Q.pull q)]
  simp

/-- The natural isomorphism defining the strong comparison of the extension. -/
def extensionComparison :
    (B.map q.op.toLoc).toFunctor ⋙ extensionFunctor hFF θ hη ≅
      extensionFunctor hFF θ hη ⋙ (T.map q.op.toLoc).toFunctor :=
  NatIso.ofComponents (extensionComparisonObj hFF θ hη q)
    (fun h => extensionComparison_naturality hFF θ hη q h)

/-- Fiber recovery intertwines the extended parameter comparison with the original one. -/
theorem extensionComparison_recovery (a : F.obj (.mk (op X))) :
    (extensionFunctor hFF θ hη).map ((comparison η q).hom.app a) ≫
      (extensionComparisonObj hFF θ hη q ((component η X).obj a)).hom ≫
        (T.map q.op.toLoc).toFunctor.map ((extensionFunctorRecovery hFF θ hη).hom.app a) =
    (extensionFunctorRecovery hFF θ hη).hom.app ((F.map q.op.toLoc).toFunctor.obj a) ≫
      (comparison θ q).hom.app a := by
  let P := presentation hη ((component η X).obj a)
  let Q := presentation hη ((component η Y).obj ((F.map q.op.toLoc).toFunctor.obj a))
  let R := presentation hη ((B.map q.op.toLoc).toFunctor.obj ((component η X).obj a))
  change Q.mapTo hFF R θ ((comparison η q).hom.app a) ≫
      (R.mapTo hFF (P.pull q) θ (𝟙 _) ≫ (P.pullValueIso q hFF θ).hom) ≫
        (T.map q.op.toLoc).toFunctor.map (P.valueRecovery hFF θ).hom =
    (Q.valueRecovery hFF θ).hom ≫ (comparison θ q).hom.app a
  simp only [Category.assoc]
  rw [reassoc_of% Q.mapTo_comp hFF R θ (P.pull q)]
  simp only [Category.comp_id]
  exact P.pullValueIso_recovery hFF q θ Q

end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation ParameterComposition
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable {X Y Z : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable (q : Y ⟶ X) (q' : Z ⟶ Y)

def pullCompMap : ((P.pull q).pull q').domain ⟶ (P.pull (q' ≫ q)).domain :=
  pullback.lift ((P.pull q).pull q').cover
    (pullback.snd q' (P.pull q).cover ≫ pullback.snd q P.cover) (by
      change pullback.fst q' (pullback.fst q P.cover) ≫ (q' ≫ q) = (pullback.snd q' (pullback.fst q P.cover) ≫ pullback.snd q P.cover) ≫ P.cover
      simp only [Category.assoc, ← pullback.condition_assoc, ← pullback.condition])

theorem pullCompMap_cover : P.pullCompMap q q' ≫ (P.pull (q' ≫ q)).cover =
    ((P.pull q).pull q').cover := pullback.lift_fst _ _ _

theorem pullCompMap_snd : P.pullCompMap q q' ≫ pullback.snd (q' ≫ q) P.cover =
    pullback.snd q' (P.pull q).cover ≫ pullback.snd q P.cover := pullback.lift_snd _ _ _

variable (hFF : ∀ X : C, (component η X).FullyFaithful)

abbrev pullCompTotal : F.DescentData (fun _ : Unit => P.cover) ⥤
    F.DescentData (fun _ : Unit => ((P.pull q).pull q').cover) :=
  Pseudofunctor.DescentData.pullFunctor F
    (p := q' ≫ q) (α := fun _ : Unit => ())
    (p' := fun _ => pullback.snd q' (P.pull q).cover ≫ pullback.snd q P.cover)
    (fun _ => by
      change (pullback.snd q' (pullback.fst q P.cover) ≫ pullback.snd q P.cover) ≫ P.cover = pullback.fst q' (pullback.fst q P.cover) ≫ (q' ≫ q)
      simp only [Category.assoc, ← pullback.condition_assoc, ← pullback.condition])

def pullCompLeftIso :
    P.parameterPull q ⋙ (P.pull q).parameterPull q' ≅ P.pullCompTotal q q' :=
  Pseudofunctor.DescentData.pullFunctorCompIso F
    (p := q) (q := q') (f := fun _ : Unit => P.cover)
    (f' := fun _ : Unit => (P.pull q).cover) (f'' := fun _ : Unit => ((P.pull q).pull q').cover)
    (p' := fun _ => pullback.snd q P.cover) (q' := fun _ => pullback.snd q' (P.pull q).cover)
    (r' := fun _ => pullback.snd q' (P.pull q).cover ≫ pullback.snd q P.cover)
    (α := fun _ : Unit => ()) (β := fun _ : Unit => ())
    (fun _ => pullback.condition.symm) (fun _ => pullback.condition.symm)
    (q' ≫ q) rfl (fun _ => rfl)

def pullCompRightIso :
    P.parameterPull (q' ≫ q) ⋙
      (P.pull (q' ≫ q)).refinement (P.pullCompMap q q') ((P.pull q).pull q').cover
        (P.pullCompMap_cover q q') ≅ P.pullCompTotal q q' :=
  Pseudofunctor.DescentData.pullFunctorCompIso F
    (p := q' ≫ q) (q := 𝟙 Z) (f := fun _ : Unit => P.cover)
    (f' := fun _ : Unit => (P.pull (q' ≫ q)).cover)
    (f'' := fun _ : Unit => ((P.pull q).pull q').cover)
    (p' := fun _ => pullback.snd (q' ≫ q) P.cover) (q' := fun _ => P.pullCompMap q q')
    (r' := fun _ => pullback.snd q' (P.pull q).cover ≫ pullback.snd q P.cover)
    (α := fun _ : Unit => ()) (β := fun _ : Unit => ())
    (fun _ => pullback.condition.symm)
    (fun _ => (P.pullCompMap_cover q q').trans (Category.comp_id _).symm)
    (q' ≫ q) (Category.id_comp _) (fun _ => P.pullCompMap_snd q q')

def pullCompSourceLeft : ((P.pull q).pull q').sourceData hFF ≅
    (P.pullCompTotal q q').obj (P.sourceData hFF) :=
  (P.pull q).pullSourceDataIso q' hFF ≪≫
    ((P.pull q).parameterPull q').mapIso (P.pullSourceDataIso q hFF) ≪≫
      (P.pullCompLeftIso q q').app (P.sourceData hFF)

def pullCompSourceRight :
    ((P.pull (q' ≫ q)).refinement (P.pullCompMap q q') ((P.pull q).pull q').cover
      (P.pullCompMap_cover q q')).obj ((P.pull (q' ≫ q)).sourceData hFF) ≅
    (P.pullCompTotal q q').obj (P.sourceData hFF) :=
  ((P.pull (q' ≫ q)).refinement (P.pullCompMap q q') ((P.pull q).pull q').cover
    (P.pullCompMap_cover q q')).mapIso (P.pullSourceDataIso (q' ≫ q) hFF) ≪≫
      (P.pullCompRightIso q q').app (P.sourceData hFF)

def pullCompSourceIso : ((P.pull q).pull q').sourceData hFF ≅
    ((P.pull (q' ≫ q)).refinement (P.pullCompMap q q') ((P.pull q).pull q').cover
      (P.pullCompMap_cover q q')).obj ((P.pull (q' ≫ q)).sourceData hFF) :=
  P.pullCompSourceLeft q q' hFF ≪≫ (P.pullCompSourceRight q q' hFF).symm

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation ParameterComposition
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable {X Y Z : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable (q : Y ⟶ X) (q' : Z ⟶ Y)
variable (hFF : ∀ X : C, (component η X).FullyFaithful)

def pullCompSourceImage : (map η (fun _ : Unit => ((P.pull q).pull q').cover)).obj
    ((P.pullCompTotal q q').obj (P.sourceData hFF)) ≅
    (B.toDescentData (fun _ : Unit => ((P.pull q).pull q').cover)).obj
      ((B.map (q' ≫ q).op.toLoc).toFunctor.obj b) :=
  pullSourceIso (q := q' ≫ q) (p := fun _ : Unit => P.cover)
    (p' := fun _ : Unit => ((P.pull q).pull q').cover)
    (r := fun _ => pullback.snd q' (P.pull q).cover ≫ pullback.snd q P.cover)
    (α := fun _ => ()) (fun _ => by
      change (pullback.snd q' (pullback.fst q P.cover) ≫ pullback.snd q P.cover) ≫ P.cover =
        pullback.fst q' (pullback.fst q P.cover) ≫ (q' ≫ q)
      simp only [Category.assoc, ← pullback.condition_assoc, ← pullback.condition])
    (P.sourceData hFF) (P.sourceDataIso hFF)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem pullCompSourceLeft_hom :
    (map η (fun _ : Unit => ((P.pull q).pull q').cover)).map
      (P.pullCompSourceLeft q q' hFF).hom ≫ (P.pullCompSourceImage q q' hFF).hom =
    (((P.pull q).pull q').sourceDataIso hFF).hom ≫
      (B.toDescentData (fun _ : Unit => ((P.pull q).pull q').cover)).map
        ((B.mapComp q.op.toLoc q'.op.toLoc).inv.toNatTrans.app b) := by
  have hc := pullSourceIso_comp' η P.cover (P.pull q).cover ((P.pull q).pull q').cover
    q q' (pullback.snd q P.cover) (pullback.snd q' (P.pull q).cover)
    pullback.condition.symm pullback.condition.symm (P.sourceData hFF) (P.sourceDataIso hFF)
    (q' ≫ q) rfl (pullback.snd q' (P.pull q).cover ≫ pullback.snd q P.cover) rfl
  simp only [op_comp, Quiver.Hom.comp_toLoc, Pseudofunctor.mapComp'_eq_mapComp] at hc
  simp only [pullCompSourceLeft, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  dsimp only [pullCompLeftIso, pullCompSourceImage]
  rw [← hc]
  have hn := pullSourceIso_naturality
    (p := fun _ : Unit => (P.pull q).cover) (p' := fun _ : Unit => ((P.pull q).pull q').cover)
    (q := q') (r := fun _ => pullback.snd q' (P.pull q).cover) (α := fun _ => ())
    (fun _ => pullback.condition.symm)
    ((P.pull q).sourceDataIso hFF)
    (pullSourceIso (p := fun _ : Unit => P.cover) (p' := fun _ : Unit => (P.pull q).cover)
      (q := q) (r := fun _ => pullback.snd q P.cover) (α := fun _ => ())
      (fun _ => pullback.condition.symm) (P.sourceData hFF) (P.sourceDataIso hFF))
    (P.pullSourceDataIso q hFF).hom (by simp [pullSourceDataIso])
  rw [reassoc_of% hn, ← Category.assoc]
  congr 1
  simp [pullSourceDataIso]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem pullCompSourceRight_hom :
    (map η (fun _ : Unit => ((P.pull q).pull q').cover)).map
      (P.pullCompSourceRight q q' hFF).hom ≫ (P.pullCompSourceImage q q' hFF).hom =
    ((P.pull (q' ≫ q)).refinedSourceIso hFF (P.pullCompMap q q') ((P.pull q).pull q').cover
      (P.pullCompMap_cover q q')).hom := by
  have hc := pullSourceIso_comp' η P.cover (P.pull (q' ≫ q)).cover ((P.pull q).pull q').cover
    (q' ≫ q) (𝟙 Z) (pullback.snd (q' ≫ q) P.cover) (P.pullCompMap q q')
    pullback.condition.symm ((P.pullCompMap_cover q q').trans (Category.comp_id _).symm)
    (P.sourceData hFF) (P.sourceDataIso hFF) (q' ≫ q) (Category.id_comp _)
    (pullback.snd q' (P.pull q).cover ≫ pullback.snd q P.cover) (P.pullCompMap_snd q q')
  simp only [op_id, Quiver.Hom.id_toLoc, Pseudofunctor.mapComp'_comp_id_inv_app] at hc
  simp only [pullCompSourceRight, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  dsimp only [pullCompRightIso, pullCompSourceImage]
  rw [← hc]
  have hn := pullSourceIso_naturality
    (p := fun _ : Unit => (P.pull (q' ≫ q)).cover)
    (p' := fun _ : Unit => ((P.pull q).pull q').cover)
    (q := 𝟙 Z) (r := fun _ => P.pullCompMap q q') (α := fun _ => ())
    (fun _ => (P.pullCompMap_cover q q').trans (Category.comp_id _).symm)
    ((P.pull (q' ≫ q)).sourceDataIso hFF)
    (pullSourceIso (p := fun _ : Unit => P.cover) (p' := fun _ : Unit => (P.pull (q' ≫ q)).cover)
      (q := q' ≫ q) (r := fun _ => pullback.snd (q' ≫ q) P.cover) (α := fun _ => ())
      (fun _ => pullback.condition.symm) (P.sourceData hFF) (P.sourceDataIso hFF))
    (P.pullSourceDataIso (q' ≫ q) hFF).hom (by simp [pullSourceDataIso])
  rw [← Category.assoc, hn]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem pullCompSourceIso_hom :
    (map η (fun _ : Unit => ((P.pull q).pull q').cover)).map
      (P.pullCompSourceIso q q' hFF).hom ≫
    ((P.pull (q' ≫ q)).refinedSourceIso hFF (P.pullCompMap q q') ((P.pull q).pull q').cover
      (P.pullCompMap_cover q q')).hom =
    (((P.pull q).pull q').sourceDataIso hFF).hom ≫
      (B.toDescentData (fun _ : Unit => ((P.pull q).pull q').cover)).map
        ((B.mapComp q.op.toLoc q'.op.toLoc).inv.toNatTrans.app b) := by
  rw [← P.pullCompSourceRight_hom q q' hFF]
  simp only [pullCompSourceIso, Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc _ (P.pullCompSourceRight q q' hFF).inv
    (P.pullCompSourceRight q q' hFF).hom]
  simp only [Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact P.pullCompSourceLeft_hom q q' hFF

end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation ParameterComposition
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable {X Y Z : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable (q : Y ⟶ X) (q' : Z ⟶ Y) (θ : F ⟶ T) [T.IsStack J]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def pullCompTotalRealization :=
  realizationPullIso (p := fun _ : Unit => P.cover) (q := q' ≫ q)
    (p' := fun _ : Unit => ((P.pull q).pull q').cover)
    (r := fun _ => pullback.snd q' (P.pull q).cover ≫ pullback.snd q P.cover)
    (α := fun _ : Unit => ()) (fun _ => by
      change (pullback.snd q' (pullback.fst q P.cover) ≫ pullback.snd q P.cover) ≫ P.cover = pullback.fst q' (pullback.fst q P.cover) ≫ (q' ≫ q)
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, ← pullback.condition, Category.assoc])
    θ P.covering ((P.pull q).pull q').covering

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem pullCompLeft_value (D : F.DescentData (fun _ : Unit => P.cover)) :
    (realizationPullIso (p := fun _ : Unit => (P.pull q).cover) (q := q')
      (p' := fun _ : Unit => ((P.pull q).pull q').cover)
      (r := fun _ => pullback.snd q' (P.pull q).cover) (α := fun _ => ())
      (fun _ => pullback.condition.symm) θ (P.pull q).covering ((P.pull q).pull q').covering).hom.app
        ((P.parameterPull q).obj D) ≫
      (T.map q'.op.toLoc).toFunctor.map ((realizationPullIso
        (p := fun _ : Unit => P.cover) (q := q) (p' := fun _ : Unit => (P.pull q).cover)
        (r := fun _ => pullback.snd q P.cover) (α := fun _ => ())
        (fun _ => pullback.condition.symm) θ P.covering (P.pull q).covering).hom.app D) ≫
      (T.mapComp' q.op.toLoc q'.op.toLoc (q' ≫ q).op.toLoc rfl).inv.toNatTrans.app
        ((realization θ P.covering).obj D) =
    (realization θ ((P.pull q).pull q').covering).map ((P.pullCompLeftIso q q').hom.app D) ≫
      (P.pullCompTotalRealization q q' θ).hom.app D := by
  exact realizationPullComp' P.cover (P.pull q).cover ((P.pull q).pull q').cover
    q q' (pullback.snd q P.cover) (pullback.snd q' (P.pull q).cover)
    pullback.condition.symm pullback.condition.symm θ P.covering (P.pull q).covering
    ((P.pull q).pull q').covering (q' ≫ q) rfl
    (pullback.snd q' (P.pull q).cover ≫ pullback.snd q P.cover) rfl D

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem pullCompRight_value (D : F.DescentData (fun _ : Unit => P.cover)) :
    (realizationRefinementIso θ (P.pull (q' ≫ q)).cover (P.pullCompMap q q')
      ((P.pull q).pull q').cover (P.pullCompMap_cover q q') (P.pull (q' ≫ q)).covering
      ((P.pull q).pull q').covering).hom.app ((P.parameterPull (q' ≫ q)).obj D) ≫
      (realizationPullIso (p := fun _ : Unit => P.cover) (q := q' ≫ q)
        (p' := fun _ : Unit => (P.pull (q' ≫ q)).cover)
        (r := fun _ => pullback.snd (q' ≫ q) P.cover) (α := fun _ => ())
        (fun _ => pullback.condition.symm) θ P.covering (P.pull (q' ≫ q)).covering).hom.app D =
    (realization θ ((P.pull q).pull q').covering).map ((P.pullCompRightIso q q').hom.app D) ≫
      (P.pullCompTotalRealization q q' θ).hom.app D := by
  have hc := realizationPullComp' P.cover (P.pull (q' ≫ q)).cover ((P.pull q).pull q').cover
    (q' ≫ q) (𝟙 Z) (pullback.snd (q' ≫ q) P.cover) (P.pullCompMap q q')
    pullback.condition.symm ((P.pullCompMap_cover q q').trans (Category.comp_id _).symm)
    θ P.covering (P.pull (q' ≫ q)).covering ((P.pull q).pull q').covering
    (q' ≫ q) (Category.id_comp _) (pullback.snd q' (P.pull q).cover ≫ pullback.snd q P.cover)
    (P.pullCompMap_snd q q') D
  dsimp [firstRealization, secondRealization, realizationRefinementIso,
    pullCompTotalRealization, pullCompRightIso] at hc ⊢
  simp only [Pseudofunctor.mapComp'_comp_id_inv_app] at hc
  have hn := (Cat.Hom.toNatIso (T.mapId (.mk (op Z)))).hom.naturality
    ((realizationPullIso (p := fun _ : Unit => P.cover) (q := q' ≫ q)
      (p' := fun _ : Unit => (P.pull (q' ≫ q)).cover)
      (r := fun _ => pullback.snd (q' ≫ q) P.cover) (α := fun _ => ())
      (fun _ => pullback.condition.symm) θ P.covering (P.pull (q' ≫ q)).covering).hom.app D)
  dsimp at hn
  simp only [Category.comp_id, Category.assoc]
  rw [← hn]
  exact hc


variable (hFF : ∀ X : C, (component η X).FullyFaithful)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem pullCompSourceLeft_value :
    (realization θ ((P.pull q).pull q').covering).map (P.pullCompSourceLeft q q' hFF).hom ≫
      (P.pullCompTotalRealization q q' θ).hom.app (P.sourceData hFF) =
    ((P.pull q).pullValueIso q' hFF θ).hom ≫
      (T.map q'.op.toLoc).toFunctor.map (P.pullValueIso q hFF θ).hom ≫
      (T.mapComp' q.op.toLoc q'.op.toLoc (q' ≫ q).op.toLoc rfl).inv.toNatTrans.app
        (P.value hFF θ) := by
  have hc := P.pullCompLeft_value q q' θ (P.sourceData hFF)
  have hn := (realizationPullIso (p := fun _ : Unit => (P.pull q).cover) (q := q')
    (p' := fun _ : Unit => ((P.pull q).pull q').cover)
    (r := fun _ => pullback.snd q' (P.pull q).cover) (α := fun _ => ())
    (fun _ => pullback.condition.symm) θ (P.pull q).covering ((P.pull q).pull q').covering).hom.naturality
      (P.pullSourceDataIso q hFF).hom
  dsimp only [pullCompSourceLeft, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    pullValueIso]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hc]
  change (realization θ ((P.pull q).pull q').covering).map
    (((P.pull q).parameterPull q').map (P.pullSourceDataIso q hFF).hom) ≫ _ = _ at hn
  rw [← Category.assoc _ _ ((T.map q'.op.toLoc).toFunctor.map
    ((realizationPullIso (p := fun _ : Unit => P.cover) (q := q)
      (p' := fun _ : Unit => (P.pull q).cover) (r := fun _ => pullback.snd q P.cover)
      (α := fun _ => ()) (fun _ => pullback.condition.symm) θ P.covering (P.pull q).covering).hom.app
      (P.sourceData hFF)) ≫ _), hn]
  simp only [Functor.comp_map, value, realization, Functor.comp_obj, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem pullCompSourceRight_value :
    (realization θ ((P.pull q).pull q').covering).map (P.pullCompSourceRight q q' hFF).hom ≫
      (P.pullCompTotalRealization q q' θ).hom.app (P.sourceData hFF) =
    ((P.pull (q' ≫ q)).refinedValueIso hFF (P.pullCompMap q q') ((P.pull q).pull q').cover
      (P.pullCompMap_cover q q') θ ((P.pull q).pull q').covering).hom ≫
      (P.pullValueIso (q' ≫ q) hFF θ).hom := by
  have hc := P.pullCompRight_value q q' θ (P.sourceData hFF)
  have hn := (realizationRefinementIso θ (P.pull (q' ≫ q)).cover (P.pullCompMap q q')
    ((P.pull q).pull q').cover (P.pullCompMap_cover q q') (P.pull (q' ≫ q)).covering
    ((P.pull q).pull q').covering).hom.naturality (P.pullSourceDataIso (q' ≫ q) hFF).hom
  dsimp only [pullCompSourceRight, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [Functor.map_comp, Category.assoc, ← hc]
  change (realization θ ((P.pull q).pull q').covering).map
    (((P.pull (q' ≫ q)).refinement (P.pullCompMap q q') ((P.pull q).pull q').cover
      (P.pullCompMap_cover q q')).map (P.pullSourceDataIso (q' ≫ q) hFF).hom) ≫ _ = _ at hn
  rw [← Category.assoc, hn]
  dsimp [refinedValueIso, pullValueIso, realizationRefinementIso, value, realization]
  simp only [Category.comp_id, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem pullCompSourceIso_value :
    (realization θ ((P.pull q).pull q').covering).map (P.pullCompSourceIso q q' hFF).hom ≫
      ((P.pull (q' ≫ q)).refinedValueIso hFF (P.pullCompMap q q') ((P.pull q).pull q').cover
        (P.pullCompMap_cover q q') θ ((P.pull q).pull q').covering).hom ≫
      (P.pullValueIso (q' ≫ q) hFF θ).hom =
    ((P.pull q).pullValueIso q' hFF θ).hom ≫
      (T.map q'.op.toLoc).toFunctor.map (P.pullValueIso q hFF θ).hom ≫
      (T.mapComp' q.op.toLoc q'.op.toLoc (q' ≫ q).op.toLoc rfl).inv.toNatTrans.app
        (P.value hFF θ) := by
  rw [← P.pullCompSourceRight_value q q' θ hFF]
  dsimp only [pullCompSourceIso, Iso.trans_hom, Iso.symm_hom]
  rw [Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    Category.comp_id]
  exact P.pullCompSourceLeft_value q q' θ hFF

end SquareKit.StackificationUniversal.LocalPresentation
namespace SquareKit.StackificationUniversal.LocalPresentation
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable {X Y Z : C} {b : B.obj (.mk (op X))} (P : LocalPresentation J η b)
variable (q : Y ⟶ X) (q' : Z ⟶ Y)
variable (hFF : ∀ X : C, (component η X).FullyFaithful)
variable (θ : F ⟶ T) [T.IsStack J]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem pullValueIso_comp :
    ((P.pull q).pull q').mapTo hFF (P.pull (q' ≫ q)) θ
      ((B.mapComp' q.op.toLoc q'.op.toLoc (q' ≫ q).op.toLoc rfl).inv.toNatTrans.app b) ≫
      (P.pullValueIso (q' ≫ q) hFF θ).hom =
    ((P.pull q).pullValueIso q' hFF θ).hom ≫
      (T.map q'.op.toLoc).toFunctor.map (P.pullValueIso q hFF θ).hom ≫
      (T.mapComp' q.op.toLoc q'.op.toLoc (q' ≫ q).op.toLoc rfl).inv.toNatTrans.app
        (P.value hFF θ) := by
  simp only [op_comp, Quiver.Hom.comp_toLoc, Pseudofunctor.mapComp'_eq_mapComp]
  rw [((P.pull q).pull q').mapTo_from_sourceMap hFF (P.pull (q' ≫ q)) θ
    (P.pullCompMap q q') (P.pullCompMap_cover q q') _
    (P.pullCompSourceIso q q' hFF).hom (P.pullCompSourceIso_hom q q' hFF)]
  simpa only [Category.assoc, op_comp, Quiver.Hom.comp_toLoc, Pseudofunctor.mapComp'_eq_mapComp] using P.pullCompSourceIso_value q q' θ hFF
end SquareKit.StackificationUniversal.LocalPresentation

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable (hFF : ∀ X : C, (component η X).FullyFaithful)
variable (θ : F ⟶ T) [T.IsStack J] (hη : LocallyGenerating J η)
variable {X Y : C} (q : Y ⟶ X)

variable {Z : C} (q' : Z ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The extension comparison respects composition of parameter substitutions. -/
theorem extensionComparison_comp (b : B.obj (.mk (op X)))
 :
    (extensionComparisonObj hFF θ hη (q' ≫ q) b).hom ≫
        (T.mapComp' q.op.toLoc q'.op.toLoc (q' ≫ q).op.toLoc (by grind)).hom.toNatTrans.app
          ((extensionFunctor hFF θ hη).obj b) =
      (extensionFunctor hFF θ hη).map
          ((B.mapComp' q.op.toLoc q'.op.toLoc (q' ≫ q).op.toLoc (by grind)).hom.toNatTrans.app b) ≫
        (extensionComparisonObj hFF θ hη q' ((B.map q.op.toLoc).toFunctor.obj b)).hom ≫
        (T.map q'.op.toLoc).toFunctor.map (extensionComparisonObj hFF θ hη q b).hom := by
  let P := presentation hη b
  let Q := presentation hη ((B.map q.op.toLoc).toFunctor.obj b)
  let R := presentation hη ((B.map q'.op.toLoc).toFunctor.obj ((B.map q.op.toLoc).toFunctor.obj b))
  let S := presentation hη ((B.map (q' ≫ q).op.toLoc).toFunctor.obj b)
  let iB := Cat.Hom.toNatIso (B.mapComp' q.op.toLoc q'.op.toLoc (q' ≫ q).op.toLoc (by grind))
  let iT := Cat.Hom.toNatIso (T.mapComp' q.op.toLoc q'.op.toLoc (q' ≫ q).op.toLoc (by grind))
  change (S.mapTo hFF (P.pull (q' ≫ q)) θ (𝟙 _) ≫ (P.pullValueIso (q' ≫ q) hFF θ).hom) ≫
      iT.hom.app (P.value hFF θ) =
    S.mapTo hFF R θ (iB.hom.app b) ≫
      (R.mapTo hFF (Q.pull q') θ (𝟙 _) ≫ (Q.pullValueIso q' hFF θ).hom) ≫
      (T.map q'.op.toLoc).toFunctor.map
        (Q.mapTo hFF (P.pull q) θ (𝟙 _) ≫ (P.pullValueIso q hFF θ).hom)
  apply (cancel_mono (iT.inv.app (P.value hFF θ))).mp
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hn := Q.mapTo_pull hFF (P.pull q) q' θ (𝟙 ((B.map q.op.toLoc).toFunctor.obj b))
  rw [(B.map q'.op.toLoc).toFunctor.map_id] at hn
  rw [← reassoc_of% hn]
  simp only [iT, Cat.Hom.toNatIso_inv]
  rw [← P.pullValueIso_comp q q' hFF θ]
  rw [reassoc_of% R.mapTo_comp hFF (Q.pull q') θ ((P.pull q).pull q'),
    reassoc_of% S.mapTo_comp hFF R θ ((P.pull q).pull q'),
    reassoc_of% S.mapTo_comp hFF ((P.pull q).pull q') θ (P.pull (q' ≫ q))]
  simp only [Category.comp_id]
  change _ = S.mapTo hFF (P.pull (q' ≫ q)) θ (iB.hom.app b ≫ iB.inv.app b) ≫ _
  rw [Iso.hom_inv_id_app]

end SquareKit.StackificationUniversal
namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {F B T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {J : GrothendieckTopology C} {η : F ⟶ B}
variable (hFF : ∀ X : C, (component η X).FullyFaithful)
variable (θ : F ⟶ T) [T.IsStack J] (hη : LocallyGenerating J η)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem extensionComparison_unit {X : C} (b : B.obj (.mk (op X))) :
    (extensionComparisonObj hFF θ hη (𝟙 X) b).hom ≫
      (T.mapId (.mk (op X))).hom.toNatTrans.app ((extensionFunctor hFF θ hη).obj b) =
    (extensionFunctor hFF θ hη).map ((B.mapId (.mk (op X))).hom.toNatTrans.app b) := by
  apply unit_of_composition (B.map (𝟙 (.mk (op X)))).toFunctor
    (T.map (𝟙 (.mk (op X)))).toFunctor (extensionFunctor hFF θ hη)
    (Cat.Hom.toNatIso (B.mapId _)) (Cat.Hom.toNatIso (T.mapId _))
    (extensionComparison hFF θ hη (𝟙 X))
  intro a
  have hc (s : X ⟶ X) (hs : 𝟙 X ≫ 𝟙 X = s) :
      (extensionComparisonObj hFF θ hη s a).hom ≫
        (T.mapComp' (𝟙 X).op.toLoc (𝟙 X).op.toLoc s.op.toLoc (by subst s; rfl)).hom.toNatTrans.app
          ((extensionFunctor hFF θ hη).obj a) =
      (extensionFunctor hFF θ hη).map
        ((B.mapComp' (𝟙 X).op.toLoc (𝟙 X).op.toLoc s.op.toLoc (by subst s; rfl)).hom.toNatTrans.app a) ≫
      (extensionComparisonObj hFF θ hη (𝟙 X) ((B.map (𝟙 X).op.toLoc).toFunctor.obj a)).hom ≫
      (T.map (𝟙 X).op.toLoc).toFunctor.map (extensionComparisonObj hFF θ hη (𝟙 X) a).hom := by
    subst s
    exact extensionComparison_comp hFF θ hη (𝟙 X) (𝟙 X) a
  have h := hc (𝟙 X) (Category.id_comp _)
  dsimp only [extensionComparison, NatIso.ofComponents_hom_app, Cat.Hom.toNatIso_inv]
  simpa only [op_id, Quiver.Hom.id_toLoc, Pseudofunctor.mapComp'_id_comp_hom_app, Cat.Hom.toNatIso_inv,
    Cat.Hom.comp_toFunctor, Functor.comp_obj] using h


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def extension : B ⟶ T where
  app X := (extensionFunctor (X := X.as.unop) hFF θ hη).toCatHom
  naturality f := Cat.Hom.isoMk (extensionComparison hFF θ hη f.as.unop)
  naturality_naturality {X Y} {f g} h := by
    obtain rfl := LocallyDiscrete.eq_of_hom h
    have hh : h = 𝟙 f := Subsingleton.elim _ _
    subst h
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    ext b
    simp
  naturality_id X := by
    obtain ⟨⟨X⟩⟩ := X
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext b
    dsimp
    simpa [extensionComparison, Cat.Hom.isoMk, Quiver.Hom.toLoc] using extensionComparison_unit hFF θ hη b
  naturality_comp {X Y Z} f g := by
    cases X
    cases Y
    cases Z
    cases f
    cases g
    rename_i f g
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext b
    dsimp
    simpa [extensionComparison, Cat.Hom.isoMk,
      op_comp, Quiver.Hom.comp_toLoc, Quiver.Hom.toLoc, Pseudofunctor.mapComp'_eq_mapComp] using
      extensionComparison_comp hFF θ hη f.unop g.unop b

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def extensionRecovery : η ≫ extension hFF θ hη ≅ θ :=
  Pseudofunctor.StrongTrans.isoMk
    (fun X => Cat.Hom.isoMk (extensionFunctorRecovery (X := X.as.unop) hFF θ hη)) (by
      intro X Y f
      obtain ⟨⟨X⟩⟩ := X
      obtain ⟨⟨Y⟩⟩ := Y
      cases f
      rename_i f
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext a
      dsimp
      simpa [extension, extensionComparison, Cat.Hom.isoMk, comparison, component,
        Quiver.Hom.toLoc, Category.assoc] using
        (extensionComparison_recovery hFF θ hη f.unop a).symm)

end SquareKit.StackificationUniversal

namespace SquareKit.StackificationUniversal
open CategoryTheory Opposite Limits
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open StackDescentTransformation StackLocalGeneration
universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C] {J : GrothendieckTopology C}
variable {F B : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {η : F ⟶ B} (hFF : ∀ X : C, (component η X).FullyFaithful)
variable (hη : LocallyGenerating J η)
variable (T : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) [T.IsStack J]

/-- Precomposition with a fully faithful, locally generating transformation is an
equivalence into every target stack, including modifications. -/
def universalEquivalence : (B ⟶ T) ≌ (F ⟶ T) := by
  let ff := fullyFaithfulRestriction η hFF J hη (T := T)
  letI := ff.full
  letI := ff.faithful
  letI : (restriction η T).EssSurj := ⟨fun θ => ⟨extension hFF θ hη, ⟨extensionRecovery hFF θ hη⟩⟩⟩
  letI : (restriction η T).IsEquivalence := {}
  exact (restriction η T).asEquivalence

@[simp] theorem universalEquivalence_functor :
    (universalEquivalence hFF hη T).functor = restriction η T := rfl

end SquareKit.StackificationUniversal
