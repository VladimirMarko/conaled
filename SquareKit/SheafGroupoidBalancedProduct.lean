import SquareKit.SheafGroupoidBundleComposition
import SquareKit.SplitSheafDescentQuotient
import Mathlib.CategoryTheory.Sites.RegularEpi

/-! The balanced product map and its quotient contract. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle.BalancedProduct
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {H K : Operations J} [H.Laws] [K.Laws]
variable {X : Sheaf J (Type (max u v))} (P : Principal H X)
  (Q : Principal K H.objects)

abbrev total (P : Principal H X) := SplitSheaf.extension P.family

def anchor : total P ⟶ H.objects :=
  SplitSheaf.p P.family ≫ SheafRelation.snd X H.objects

abbrev displaySource := SplitSheaf.extension (Descent.localFamily (localBundle P Q))

abbrev ordinarySource :=
  SplitSheaf.extension (SplitSheaf.tySub (SplitSheaf.ofDisplay Q.toAction.projection) (anchor P))

def toOrdinary : displaySource P Q ⟶ ordinarySource P Q where
  hom := {
    app _ := ↾fun z => ⟨z.1.2.val, ⟨⟨(z.1.2.val.1.2,z.1.1.2),z.2⟩,rfl⟩⟩
    naturality _ _ _ := rfl }

def fromOrdinary : ordinarySource P Q ⟶ displaySource P Q where
  hom := {
    app _ := ↾fun z => by
      rcases z with ⟨⟨⟨x,h⟩,p⟩,⟨⟨⟨h',k⟩,q⟩,e⟩⟩
      change h' = h at e
      subst h'
      exact ⟨⟨(x,k),⟨⟨(x,h),p⟩,rfl⟩⟩,q⟩
    naturality := by
      intro U V f
      ext z
      rcases z with ⟨⟨⟨x,h⟩,p⟩,⟨⟨⟨h',k⟩,q⟩,e⟩⟩
      change h' = h at e
      subst h'
      rfl }

def sourceIso : displaySource P Q ≅ ordinarySource P Q where
  hom := toOrdinary P Q
  inv := fromOrdinary P Q
  hom_inv_id := by
    apply Sheaf.hom_ext
    ext U z
    rcases z with ⟨⟨⟨x,k⟩,⟨⟨⟨y,h⟩,p⟩,e⟩⟩,q⟩
    change y = x at e
    subst y
    rfl
  inv_hom_id := by
    apply Sheaf.hom_ext
    ext U z
    rcases z with ⟨⟨⟨x,h⟩,p⟩,⟨⟨⟨h',k⟩,q⟩,e⟩⟩
    change h' = h at e
    subst h'
    rfl

end SquareKit.SheafGroupoid.Bundle.BalancedProduct
namespace SquareKit.SheafGroupoid.Bundle.BalancedProduct
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {H K : Operations J} [H.Laws] [K.Laws]
variable {X : Sheaf J (Type (max u v))} (P : Principal H X)
  (Q : Principal K H.objects)

def ordinaryFirst : ordinarySource P Q ⟶ total Q :=
  SplitSheaf.lift (SplitSheaf.ofDisplay Q.toAction.projection) (anchor P) ≫
    (SplitSheaf.displayIso Q.toAction.projection).hom

abbrev ordinarySecond : ordinarySource P Q ⟶ total P := SplitSheaf.p _

theorem ordinary_pullback : IsPullback (ordinaryFirst P Q) (ordinarySecond P Q)
    Q.toAction.projection (anchor P) := by
  have hp : IsPullback (SplitSheaf.displayIso Q.toAction.projection).hom
      (SplitSheaf.p (SplitSheaf.ofDisplay Q.toAction.projection))
      Q.toAction.projection (𝟙 H.objects) :=
    IsPullback.of_horiz_isIso ⟨by simp [SplitSheaf.displayIso_projection]⟩
  simpa only [Category.comp_id, ordinaryFirst, ordinarySecond, total, ordinarySource] using
    (SplitSheaf.extension_pullback (SplitSheaf.ofDisplay Q.toAction.projection) (anchor P)).paste_horiz hp

def sourcePullbackIso : displaySource P Q ≅ pullback Q.toAction.projection (anchor P) :=
  sourceIso P Q ≪≫ (ordinary_pullback P Q).isoPullback

def balancedMap (L : LeftAction Q) : ordinarySource P Q ⟶ total (compositionRightBundle P Q L) :=
  (sourceIso P Q).inv ≫ SquareKit.SplitSheafDescent.Quotient.quotientMap (compositionDatum P Q L).toDisplayDatum

instance balancedMap_isLocallySurjective (L : LeftAction Q) :
    Presheaf.IsLocallySurjective J (balancedMap P Q L).hom := by
  have : Presheaf.IsLocallySurjective J (SplitSheaf.p (cover P)).hom := inferInstance
  have : Presheaf.IsLocallySurjective J (SplitSheaf.p (Descent.anchorCover K (cover P))).hom :=
    SheafCover.baseChangeCover_isLocallySurjective (A := cover P) (SheafRelation.fst X K.objects)
  have : Presheaf.IsLocallySurjective J
      (SquareKit.SplitSheafDescent.Quotient.quotientMap (compositionDatum P Q L).toDisplayDatum).hom :=
    SquareKit.SplitSheafDescent.Quotient.quotientMap_isLocallySurjective _
  have : Presheaf.IsLocallySurjective J (sourceIso P Q).inv.hom := inferInstance
  change Presheaf.IsLocallySurjective J
    ((sourceIso P Q).inv.hom ≫
      (SquareKit.SplitSheafDescent.Quotient.quotientMap (compositionDatum P Q L).toDisplayDatum).hom)
  infer_instance

end SquareKit.SheafGroupoid.Bundle.BalancedProduct

namespace SquareKit.SheafGroupoid.Bundle.BalancedProduct
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {H K : Operations J} [H.Laws] [K.Laws]
variable {X : Sheaf J (Type (max u v))} (P : Principal H X)
  (Q : Principal K H.objects) (L : LeftAction Q)

def pairPoint (x : X.obj.Elements) (m : H.Section x.obj)
    (p : Fiber H X P.family x m) (k : K.Section x.obj)
    (q : Fiber K H.objects Q.family (atSection m) k) :
    (ordinarySource P Q).obj.obj x.obj :=
  ⟨⟨(x.val,m.val),p⟩, ⟨⟨(m.val,k.val),q⟩,rfl⟩⟩

theorem balancedMap_kernel (x : X.obj.Elements) (m n : H.Section x.obj)
    (p : Fiber H X P.family x m) (p' : Fiber H X P.family x n)
    (k : K.Section x.obj) (q : Fiber K H.objects Q.family (atSection m) k)
    (q' : Fiber K H.objects Q.family (atSection n) k) :
    (balancedMap P Q L).hom.app x.obj (pairPoint P Q x m p k q) =
      (balancedMap P Q L).hom.app x.obj (pairPoint P Q x n p' k q') ↔
      L.act (connector P x p' p) k q = q' := by
  exact SquareKit.SplitSheafDescent.Quotient.quotientMap_kernel (compositionDatum P Q L).toDisplayDatum
    (point K X x k) ⟨⟨(x.val,m.val),p⟩,rfl⟩ ⟨⟨(x.val,n.val),p'⟩,rfl⟩ q q'

theorem balancedMap_balancing (x : X.obj.Elements) {m n : H.Section x.obj}
    (h : n ⟶ m) (p : Fiber H X P.family x m)
    (k : K.Section x.obj) (q : Fiber K H.objects Q.family (atSection n) k) :
    (balancedMap P Q L).hom.app x.obj (pairPoint P Q x n (P.act x h p) k q) =
      (balancedMap P Q L).hom.app x.obj (pairPoint P Q x m p k (L.act h k q)) := by
  apply (balancedMap_kernel P Q L x n m (P.act x h p) p k q (L.act h k q)).mpr
  rw [← connector_unique P x p (P.act x h p) h rfl]

theorem balancedMap_pullback_effectiveEpi
    {T' : Sheaf J (Type (max u v))} (f : T' ⟶ total (compositionRightBundle P Q L)) :
    EffectiveEpi (pullback.snd (balancedMap P Q L) f) :=
  SquareKit.SplitSheafDescent.QuotientStability.pullback_effectiveEpi (IsPullback.of_hasPullback _ _)

variable {G : Operations J} [G.Laws]

theorem connector_leftAction (R : Principal H G.objects) (M : LeftAction R)
    {U : Cᵒᵖ} {x y : G.Section U} (g : x ⟶ y) {m n : H.Section U}
    (p : Fiber H G.objects R.family (atSection x) m)
    (q : Fiber H G.objects R.family (atSection x) n) :
    connector R (atSection y) (M.act g m p) (M.act g n q) =
      connector R (atSection x) p q := by
  symm
  apply connector_unique R (atSection y) (M.act g m p) (M.act g n q)
  rw [← M.commute, connector_spec]

end SquareKit.SheafGroupoid.Bundle.BalancedProduct
namespace SquareKit.SheafGroupoid.Bundle.BalancedProduct
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {H K : Operations J} [H.Laws] [K.Laws]
variable {X : Sheaf J (Type (max u v))} (P : Principal H X)
  (Q : Principal K H.objects) (L : LeftAction Q)

theorem balancedMap_projection : balancedMap P Q L ≫
    (compositionRightBundle P Q L).toAction.projection =
      ordinarySecond P Q ≫ P.toAction.projection := by
  apply Sheaf.hom_ext
  ext U z
  rcases z with ⟨⟨⟨x,h⟩,p⟩,⟨⟨⟨h',k⟩,q⟩,e⟩⟩
  change h' = h at e
  subst h'
  rfl

theorem balancedMap_anchor : balancedMap P Q L ≫ anchor (compositionRightBundle P Q L) =
    ordinaryFirst P Q ≫ anchor Q := by
  apply Sheaf.hom_ext
  ext U z
  rcases z with ⟨⟨⟨x,h⟩,p⟩,⟨⟨⟨h',k⟩,q⟩,e⟩⟩
  change h' = h at e
  subst h'
  rfl

end SquareKit.SheafGroupoid.Bundle.BalancedProduct
