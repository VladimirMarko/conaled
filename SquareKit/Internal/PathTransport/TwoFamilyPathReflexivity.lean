import SquareKit.Internal.PathTransport.TwoFamilyPathContext
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
private theorem discrete_casts_heq {C : Type*} [Category* C] {a b a' b' : C}
    (h : a = b) (k : LocallyDiscrete.mk a' = LocallyDiscrete.mk b') (ha : a = a') :
    HEq (Discrete.mk (eqToHom h)) (eqToHom k) := by
  cases h
  cases ha
  have hb : a = b' := congrArg LocallyDiscrete.as k
  cases hb
  rfl

/-- Reflexivity preserves the total identity arrow, including its dependent fiber. -/
theorem pathReflexivityMap_id (x : Total F) :
 pathReflexivityMap F (𝟙 x) = 𝟙 (pathReflexivityObj F x) := by
 apply Pseudofunctor.CoGrothendieck.ext
 · exact (diagonalTotal F).map_id x
 · dsimp only [pathReflexivityMap, identity, TwoGroupoidHom.arrow]
   have h := congrArg (fun (p : (diagonalTotal F).obj x ⟶ (diagonalTotal F).obj x) =>
     (openIdMap F p).obj (𝟙 x.fiber)) ((diagonalTotal F).map_id x)
   exact discrete_casts_heq _ (congrArg
     (fun H : (openIdHigher F).obj (pathReflexivityObj F x).base ⟶
       (openIdHigher F).obj (pathReflexivityObj F x).base => H.obj (pathReflexivityObj F x).fiber)
     ((openIdHigher F).map_id (pathReflexivityObj F x).base)) h
omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] [Bicategory.Strict Γ] in
private theorem canonical_comp {x y z : Total F} (p : x.base ⟶ y.base) (q : y.base ⟶ z.base)
 (hp : (F.map p).obj x.fiber = y.fiber) (hq : (F.map q).obj y.fiber = z.fiber)
 (hr : (F.map (p ≫ q)).obj x.fiber = z.fiber) :
 compose F (⟨p, eqToHom hp⟩ : Hom F x y) (⟨q, eqToHom hq⟩ : Hom F y z) =
 (⟨p ≫ q, eqToHom hr⟩ : Hom F x z) := by
 apply Pseudofunctor.CoGrothendieck.ext
 · rfl
 · apply heq_of_eq
   change eqToHom _ ≫ (F.map q).map (eqToHom hp) ≫ eqToHom hq = eqToHom hr
   rw [StrongMap.map_eqToHom]
   simp only [eqToHom_trans]

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] [Bicategory.Strict Γ] in
private theorem canonical_eq {x y : Total F} {p q : x.base ⟶ y.base}
 (e : p = q) (h : (F.map p).obj x.fiber = y.fiber)
 (k : (F.map q).obj x.fiber = y.fiber) :
 (⟨p, eqToHom h⟩ : Hom F x y) = ⟨q, eqToHom k⟩ := by cases e; rfl
private theorem discrete_mk_eqToHom {C : Type*} [Category* C] {a b : C} (h : a = b) :
 Discrete.mk (eqToHom h) = eqToHom (congrArg LocallyDiscrete.mk h) := by cases h; rfl

private theorem reflexivity_canonical {x y : Total F} (p : x ⟶ y) :
 pathReflexivityMap F p =
 (⟨(diagonalTotal F).map p, eqToHom (congrArg LocallyDiscrete.mk (diagonal_identity F p))⟩ :
 Hom (openIdHigher F) (pathReflexivityObj F x) (pathReflexivityObj F y)) := by
 unfold pathReflexivityMap
 congr 1
 exact discrete_mk_eqToHom _
set_option maxHeartbeats 1000000 in
/-- Reflexivity preserves composition of arbitrary dependent arrows. -/
theorem pathReflexivityMap_comp {x y z : Total F} (p : x ⟶ y) (q : y ⟶ z) :
 pathReflexivityMap F (p ≫ q) = pathReflexivityMap F p ≫ pathReflexivityMap F q := by
 rw [reflexivity_canonical, reflexivity_canonical, reflexivity_canonical]
 let h := congrArg (fun r => (openIdMap F r).obj (𝟙 x.fiber)) ((diagonalTotal F).map_comp p q).symm
 let k := congrArg LocallyDiscrete.mk (h.trans (diagonal_identity F (p ≫ q)))
 change _ = compose (openIdHigher F) _ _
 rw [canonical_comp (openIdHigher F)
   (x := pathReflexivityObj F x) (y := pathReflexivityObj F y) (z := pathReflexivityObj F z)
   ((diagonalTotal F).map p) ((diagonalTotal F).map q)
   (congrArg LocallyDiscrete.mk (diagonal_identity F p))
   (congrArg LocallyDiscrete.mk (diagonal_identity F q)) k]
 exact canonical_eq (openIdHigher F)
   (x := pathReflexivityObj F x) (y := pathReflexivityObj F z)
   ((diagonalTotal F).map_comp p q) _ _
end SquareKit.Internal.PathTransport.TwoFamily
