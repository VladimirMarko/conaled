import Mathlib.CategoryTheory.Whiskering
import SquareKit.ElementSite
import SquareKit.ElementFamilies
import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-! Experimental gluing on the site of elements. -/
namespace SquareKit.ElementSheaf
open CategoryTheory Opposite ElementSite ElementFamilies
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (F : Cᵒᵖ ⥤ Type w)

abbrev presheaf (Q : F.Elements ⥤ Type w) : (Site F)ᵒᵖ ⥤ Type w :=
  (opOpEquivalence F.Elements).functor ⋙ Q

abbrev family (Q : (Site F)ᵒᵖ ⥤ Type w) : F.Elements ⥤ Type w :=
  (opOpEquivalence F.Elements).inverse ⋙ Q

/-- Project a matching family to the base, using canonical restriction lifts. -/
def baseFamily {P : Cᵒᵖ ⥤ Type w} {Q : (Site F)ᵒᵖ ⥤ Type w}
    (q : Q ⟶ (projection F).op ⋙ P) {X : Site F}
    {R : Sieve ((projection F).obj X)}
    (x : Presieve.FamilyOfElements Q (up F R).arrows) :
    Presieve.FamilyOfElements P R.arrows := fun _V f hf =>
  q.app _ (x (arrow F f X.unop.val) hf)

/-- The canonical lift and an arbitrary lift give the same projected value. -/
theorem baseFamily_at {P : Cᵒᵖ ⥤ Type w} {Q : (Site F)ᵒᵖ ⥤ Type w}
    (q : Q ⟶ (projection F).op ⋙ P) {X : Site F}
    {R : Sieve ((projection F).obj X)}
    (x : Presieve.FamilyOfElements Q (up F R).arrows) (hx : x.Compatible)
    {Y : Site F} (f : Y ⟶ X) (hf : up F R f) :
    baseFamily F q x ((projection F).map f) hf = q.app (op Y) (x f hf) := by
  let g : Y ⟶ point F ((projection F).obj Y) (F.map f.unop.hom X.unop.val) :=
    (vertical F f.unop.map_val).op
  have hg : g ≫ arrow F ((projection F).map f) X.unop.val = f := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    simp [g, vertical]
  have hc : up F R (g ≫ arrow F ((projection F).map f) X.unop.val) := by
    rw [hg]
    exact hf
  have h := hx.to_sieveCompatible (arrow F ((projection F).map f) X.unop.val) g hf
  have he := congrArg (fun k : {k : Y ⟶ X // up F R k} => x k.val k.property)
    (show (⟨g ≫ arrow F ((projection F).map f) X.unop.val, hc⟩ : {k : Y ⟶ X // up F R k}) = ⟨f, hf⟩
      from Subtype.ext hg)
  have h' : x f hf = Q.map g.op (x (arrow F ((projection F).map f) X.unop.val) hf) :=
    he.symm.trans h
  dsimp only [baseFamily]
  rw [h']
  erw [NatTrans.naturality_apply]
  change _ = P.map (𝟙 _) _
  rw [P.map_id]
  rfl

theorem baseFamily_compatible {P : Cᵒᵖ ⥤ Type w} {Q : (Site F)ᵒᵖ ⥤ Type w}
    (q : Q ⟶ (projection F).op ⋙ P) {X : Site F}
    {R : Sieve ((projection F).obj X)}
    (x : Presieve.FamilyOfElements Q (up F R).arrows) (hx : x.Compatible) :
    (baseFamily F q x).Compatible := by
  apply (Presieve.compatible_iff_sieveCompatible _).2
  intro V W f g hf
  let f' := arrow F f X.unop.val
  let g' := arrow F g (F.map f.op X.unop.val)
  have h := baseFamily_at F q x hx (g' ≫ f') (R.downward_closed hf g)
  change baseFamily F q x (g ≫ f) _ = _ at h
  rw [h, hx.to_sieveCompatible f' g' hf, NatTrans.naturality_apply]
  rfl

/-- Forget the fiber equation, retaining the ordinary section. -/
def forgetFiber (p : Over F) : presheaf F (fibers F p) ⟶ (projection F).op ⋙ p.left where
  app X := ↾Subtype.val

/-- Gluing a display's fibers stays over the specified base section. -/
theorem fibers_isSheaf (hF : Presieve.IsSheaf J F) (p : Over F)
    (hA : Presieve.IsSheaf J p.left) :
    Presieve.IsSheaf (topology F J) (presheaf F (fibers F p)) := by
  intro X S hS
  have hs : up F (down F S) = S := up_down F S
  rw [← hs]
  intro x hx
  let a := baseFamily F (forgetFiber F p) x
  obtain ⟨t, ht, hut⟩ := hA (down F S) hS a (baseFamily_compatible F _ x hx)
  have hp : p.hom.app X.unop.obj t = X.unop.val := by
    apply (hF (down F S) hS).isSeparatedFor.ext
    intro V f hf
    have hn := NatTrans.naturality_apply p.hom f.op t
    change p.hom.app (op V) (p.left.map f.op t) = _ at hn
    erw [← hn, ht f hf]
    exact (x (arrow F f X.unop.val) hf).property
  refine ⟨⟨t, hp⟩, ?_, ?_⟩
  · intro Y f hf
    apply Subtype.ext
    exact (ht ((projection F).map f) hf).trans (baseFamily_at F _ x hx f hf)
  · intro b hb
    apply Subtype.ext
    apply hut b.val
    intro V f hf
    exact congrArg Subtype.val (hb (arrow F f X.unop.val) hf)

/-- Dependent total spaces glue by first gluing their base sections and then
using the sheaf on the element over that glued section. -/
theorem total_isSheaf (hF : Presieve.IsSheaf J F) (Q : (Site F)ᵒᵖ ⥤ Type w)
    (hQ : Presieve.IsSheaf (topology F J) Q) :
    Presieve.IsSheaf J (total F (family F Q)) := by
  let T := total F (family F Q)
  let p : Over F := Over.mk (display F (family F Q))
  have hfib : Presieve.IsSheaf (topology F J) (presheaf F (fibers F p)) :=
    Presieve.isSheaf_iso (topology F J)
      (Functor.isoWhiskerLeft (opOpEquivalence F.Elements).functor (fiberTotalIso F (family F Q)).symm) hQ
  intro U R hR x hx
  let b := x.map (display F (family F Q))
  obtain ⟨t, ht, hut⟩ := hF R hR b (hx.map _)
  let X := point F U t
  let y : Presieve.FamilyOfElements (presheaf F (fibers F p)) (up F (X := X) R).arrows :=
    fun Y f hf => ⟨x ((projection F).map f) hf,
      (ht ((projection F).map f) hf).symm.trans f.unop.map_val⟩
  have hy : y.Compatible := by
    apply (Presieve.compatible_iff_sieveCompatible _).2
    intro Y Z f g hf
    apply Subtype.ext
    exact hx.to_sieveCompatible ((projection F).map f) ((projection F).map g) hf
  obtain ⟨a, ha, hua⟩ := hfib (up F (X := X) R) ((up_covering_iff F J (X := X) R).2 hR) y hy
  refine ⟨a.val, ?_, ?_⟩
  · intro V f hf
    exact congrArg Subtype.val (ha (arrow F f t) hf)
  · intro z hz
    have hp : p.hom.app (op U) z = t := hut _ (hz.map _)
    have he : (⟨z, hp⟩ : (presheaf F (fibers F p)).obj (op X)) = a := by
      apply hua
      intro Y f hf
      apply Subtype.ext
      exact hz ((projection F).map f) hf
    exact congrArg Subtype.val he

end SquareKit.ElementSheaf
