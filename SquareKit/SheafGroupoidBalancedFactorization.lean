import SquareKit.SheafGroupoidBalancedProduct
import Mathlib.CategoryTheory.Sites.RegularEpi

/-! Balanced factorization, functoriality and base change. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle.BalancedFactorization
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {H K : Operations J} [H.Laws] [K.Laws]
variable {X : Sheaf J (Type (max u v))} (P : Principal H X)
  (Q : Principal K H.objects) (L : LeftAction Q)

def IsBalanced {Y : Sheaf J (Type (max u v))} (e : ordinarySource P Q ⟶ Y) : Prop :=
  ∀ (x : X.obj.Elements) (m n : H.Section x.obj) (h : n ⟶ m)
    (p : Fiber H X P.family x m) (k : K.Section x.obj)
    (q : Fiber K H.objects Q.family (atSection n) k),
    e.hom.app x.obj (pairPoint P Q x n (P.act x h p) k q) =
      e.hom.app x.obj (pairPoint P Q x m p k (L.act h k q))

theorem balanced_to_transport {Y : Sheaf J (Type (max u v))}
    (e : ordinarySource P Q ⟶ Y) (he : IsBalanced P Q L e) :
    SquareKit.SplitSheafDescent.Quotient.Balanced (compositionDatum P Q L).toDisplayDatum
      ((sourceIso P Q).hom ≫ e) := by
  intro x a b q
  rcases x with @⟨U,⟨x,k⟩⟩
  rcases a with ⟨⟨⟨y,m⟩,p⟩,ha⟩
  change y = x at ha
  subst y
  rcases b with ⟨⟨⟨y,n⟩,p'⟩,hb⟩
  change y = x at hb
  subst y
  have h := he (X.obj.elementsMk U x) ⟨n⟩ ⟨m⟩
    (connector P (X.obj.elementsMk U x) p' p) p' ⟨k⟩ q
  rw [connector_spec] at h
  exact h.symm

theorem quotient_isBalanced {Y : Sheaf J (Type (max u v))}
    (f : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (compositionRightBundle P Q L) ⟶ Y) :
    IsBalanced P Q L (balancedMap P Q L ≫ f) := by
  intro x m n h p k q
  exact congrArg (f.hom.app x.obj) (balancedMap_balancing P Q L x h p k q)

def balancedDesc {Y : Sheaf J (Type (max u v))}
    (e : ordinarySource P Q ⟶ Y) (he : IsBalanced P Q L e) :
    SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (compositionRightBundle P Q L) ⟶ Y := by
  letI : Presheaf.IsLocallySurjective J (SplitSheaf.p (Descent.anchorCover K (cover P))).hom :=
    SheafCover.baseChangeCover_isLocallySurjective (A := cover P) (SheafRelation.fst X K.objects)
  exact SquareKit.SplitSheafDescent.Quotient.balancedDesc (compositionDatum P Q L).toDisplayDatum
    ((sourceIso P Q).hom ≫ e) (balanced_to_transport P Q L e he)

theorem balancedDesc_fac {Y : Sheaf J (Type (max u v))}
    (e : ordinarySource P Q ⟶ Y) (he : IsBalanced P Q L e) :
    balancedMap P Q L ≫ balancedDesc P Q L e he = e := by
  unfold balancedDesc balancedMap
  rw [Category.assoc, SquareKit.SplitSheafDescent.Quotient.balancedDesc_fac, Iso.inv_hom_id_assoc]

theorem balancedDesc_unique {Y : Sheaf J (Type (max u v))}
    (e : ordinarySource P Q ⟶ Y) (he : IsBalanced P Q L e)
    (f : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (compositionRightBundle P Q L) ⟶ Y)
    (hf : balancedMap P Q L ≫ f = e) : f = balancedDesc P Q L e he := by
  apply (cancel_epi (balancedMap P Q L)).mp
  rw [hf, balancedDesc_fac]

def balancedHomEquiv (Y : Sheaf J (Type (max u v))) :
    (SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (compositionRightBundle P Q L) ⟶ Y) ≃
      { e : ordinarySource P Q ⟶ Y // IsBalanced P Q L e } where
  toFun f := ⟨balancedMap P Q L ≫ f, quotient_isBalanced P Q L f⟩
  invFun e := balancedDesc P Q L e.val e.property
  left_inv f := (balancedDesc_unique P Q L _ (quotient_isBalanced P Q L f) f rfl).symm
  right_inv e := Subtype.ext (balancedDesc_fac P Q L e.val e.property)

end SquareKit.SheafGroupoid.Bundle.BalancedFactorization
namespace SquareKit.SheafGroupoid.Bundle.BalancedFactorization
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {H K : Operations J} [H.Laws] [K.Laws]
variable {X : Sheaf J (Type (max u v))} (P : Principal H X)
  (Q : Principal K H.objects) (L : LeftAction Q)

def tensorPoint (x : X.obj.Elements) (m : H.Section x.obj)
    (p : Fiber H X P.family x m) (k : K.Section x.obj)
    (q : Fiber K H.objects Q.family (atSection m) k) :
    Fiber K X (compositionRightBundle P Q L).family x k :=
  (Descent.evaluationEquiv (compositionDatum P Q L) x ⟨⟨(x.val,m.val),p⟩,rfl⟩ k).symm q

theorem balancedMap_pair (x : X.obj.Elements) (m : H.Section x.obj)
    (p : Fiber H X P.family x m) (k : K.Section x.obj)
    (q : Fiber K H.objects Q.family (atSection m) k) :
    (balancedMap P Q L).hom.app x.obj (pairPoint P Q x m p k q) =
      ⟨(x.val,k.val), tensorPoint P Q L x m p k q⟩ := rfl

theorem tensorPoint_equivariant (x : X.obj.Elements) (m : H.Section x.obj)
    (p : Fiber H X P.family x m) {k l : K.Section x.obj} (g : k ⟶ l)
    (q : Fiber K H.objects Q.family (atSection m) l) :
    tensorPoint P Q L x m p k (Q.act (atSection m) g q) =
      (compositionRightBundle P Q L).act x g (tensorPoint P Q L x m p l q) := by
  apply (Descent.evaluationEquiv (compositionDatum P Q L) x ⟨⟨(x.val,m.val),p⟩,rfl⟩ k).injective
  have h := Descent.evaluation_equivariant (compositionDatum P Q L) x
    ⟨⟨(x.val,m.val),p⟩,rfl⟩ g (tensorPoint P Q L x m p l q)
  simp only [tensorPoint, Equiv.apply_symm_apply] at h ⊢
  exact h.symm

theorem balancedMap_equivariant (x : X.obj.Elements) (m : H.Section x.obj)
    (p : Fiber H X P.family x m) {k l : K.Section x.obj} (g : k ⟶ l)
    (q : Fiber K H.objects Q.family (atSection m) l) :
    (balancedMap P Q L).hom.app x.obj (pairPoint P Q x m p k (Q.act (atSection m) g q)) =
      ⟨(x.val,k.val),
        (compositionRightBundle P Q L).act x g (tensorPoint P Q L x m p l q)⟩ := by
  rw [balancedMap_pair, tensorPoint_equivariant]

end SquareKit.SheafGroupoid.Bundle.BalancedFactorization
namespace SquareKit.SheafGroupoid.Bundle.BalancedFactorization
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {H K : Operations J} [H.Laws] [K.Laws]
variable {X Y : Sheaf J (Type (max u v))} (P : Principal H X)
  (Q : Principal K H.objects) (L : LeftAction Q) (r : Y ⟶ X)

abbrev reindexLift := SplitSheaf.lift P.family (baseMap r)

theorem rawForget_square : ordinaryFirst (Bundle.reindex P r) Q ≫ Q.toAction.projection =
    (ordinarySecond (Bundle.reindex P r) Q ≫ reindexLift P r) ≫ SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor P := by
  apply Sheaf.hom_ext
  ext U z
  rcases z with ⟨⟨⟨y,h⟩,p⟩,⟨⟨⟨h',k⟩,q⟩,e⟩⟩
  change h' = h at e
  subst h'
  rfl

def rawForget : ordinarySource (Bundle.reindex P r) Q ⟶ ordinarySource P Q :=
  (ordinary_pullback P Q).lift (ordinaryFirst (Bundle.reindex P r) Q)
    (ordinarySecond (Bundle.reindex P r) Q ≫ reindexLift P r) (rawForget_square P Q r)

theorem rawForget_pair (y : Y.obj.Elements) (m : H.Section y.obj)
    (p : Fiber H Y (Bundle.reindex P r).family y m) (k : K.Section y.obj)
    (q : Fiber K H.objects Q.family (atSection m) k) :
    (rawForget P Q r).hom.app y.obj (pairPoint (Bundle.reindex P r) Q y m p k q) =
      pairPoint P Q (r.hom.mapElements.obj y) m p k q := by
  apply Types.ext_of_isPullback (SheafImage.sections_isPullback (ordinary_pullback P Q) y.obj)
  · exact congrArg (fun f : ordinarySource (Bundle.reindex P r) Q ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total Q =>
      f.hom.app y.obj (pairPoint (Bundle.reindex P r) Q y m p k q))
      ((ordinary_pullback P Q).lift_fst _ _ _)
  · exact congrArg (fun f : ordinarySource (Bundle.reindex P r) Q ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total P =>
      f.hom.app y.obj (pairPoint (Bundle.reindex P r) Q y m p k q))
      ((ordinary_pullback P Q).lift_snd _ _ _)

def rawBase : ordinarySource (Bundle.reindex P r) Q ⟶ base K Y :=
  SheafRelation.lift
    (ordinarySecond (Bundle.reindex P r) Q ≫ (Bundle.reindex P r).toAction.projection)
    (ordinaryFirst (Bundle.reindex P r) Q ≫ SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor Q)

theorem rawBase_square : (rawForget P Q r ≫ balancedMap P Q L) ≫
    SplitSheaf.p (compositionRightBundle P Q L).family = rawBase P Q r ≫ baseMap r := by
  apply Sheaf.hom_ext
  ext U z
  rcases z with ⟨⟨⟨y,h⟩,p⟩,⟨⟨⟨h',k⟩,q⟩,e⟩⟩
  change h' = h at e
  subst h'
  change ((balancedMap P Q L).hom.app U ((rawForget P Q r).hom.app U
    (pairPoint (Bundle.reindex P r) Q (Y.obj.elementsMk U y) ⟨h⟩ p ⟨k⟩ q))).1 = _
  exact congrArg Sigma.fst ((congrArg ((balancedMap P Q L).hom.app U)
    (rawForget_pair P Q r (Y.obj.elementsMk U y) ⟨h⟩ p ⟨k⟩ q)).trans
      (balancedMap_pair P Q L (r.hom.mapElements.obj (Y.obj.elementsMk U y)) ⟨h⟩ p ⟨k⟩ q))

def rawBaseChange : ordinarySource (Bundle.reindex P r) Q ⟶
    SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (Bundle.reindex (compositionRightBundle P Q L) r) :=
  (SplitSheaf.extension_pullback (compositionRightBundle P Q L).family (baseMap r)).lift
    (rawForget P Q r ≫ balancedMap P Q L) (rawBase P Q r) (rawBase_square P Q L r)

theorem rawBaseChange_pair (y : Y.obj.Elements) (m : H.Section y.obj)
    (p : Fiber H Y (Bundle.reindex P r).family y m) (k : K.Section y.obj)
    (q : Fiber K H.objects Q.family (atSection m) k) :
    (rawBaseChange P Q L r).hom.app y.obj (pairPoint (Bundle.reindex P r) Q y m p k q) =
      ⟨(y.val,k.val), tensorPoint P Q L (r.hom.mapElements.obj y) m p k q⟩ := by
  apply Types.ext_of_isPullback (SheafImage.sections_isPullback
    (SplitSheaf.extension_pullback (compositionRightBundle P Q L).family (baseMap r)) y.obj)
  · have h := congrArg (fun f : ordinarySource (Bundle.reindex P r) Q ⟶
        SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (compositionRightBundle P Q L) =>
      f.hom.app y.obj (pairPoint (Bundle.reindex P r) Q y m p k q))
      ((SplitSheaf.extension_pullback (compositionRightBundle P Q L).family (baseMap r)).lift_fst
        (rawForget P Q r ≫ balancedMap P Q L) (rawBase P Q r) (rawBase_square P Q L r))
    change _ = (balancedMap P Q L).hom.app y.obj ((rawForget P Q r).hom.app y.obj _) at h
    exact h.trans ((congrArg ((balancedMap P Q L).hom.app y.obj)
      (rawForget_pair P Q r y m p k q)).trans
        (balancedMap_pair P Q L (r.hom.mapElements.obj y) m p k q))
  · exact congrArg (fun f : ordinarySource (Bundle.reindex P r) Q ⟶ base K Y =>
      f.hom.app y.obj (pairPoint (Bundle.reindex P r) Q y m p k q))
      ((SplitSheaf.extension_pullback (compositionRightBundle P Q L).family (baseMap r)).lift_snd
        (rawForget P Q r ≫ balancedMap P Q L) (rawBase P Q r) (rawBase_square P Q L r))

theorem tensorPoint_balancing (x : X.obj.Elements) {m n : H.Section x.obj} (h : n ⟶ m)
    (p : Fiber H X P.family x m) (k : K.Section x.obj)
    (q : Fiber K H.objects Q.family (atSection n) k) :
    tensorPoint P Q L x n (P.act x h p) k q = tensorPoint P Q L x m p k (L.act h k q) := by
  have he := balancedMap_balancing P Q L x h p k q
  rw [balancedMap_pair, balancedMap_pair] at he
  exact eq_of_heq (Sigma.mk.inj_iff.mp he).2

theorem rawBaseChange_balanced : IsBalanced (Bundle.reindex P r) Q L (rawBaseChange P Q L r) := by
  intro y m n h p k q
  rw [rawBaseChange_pair, rawBaseChange_pair]
  apply congrArg (Sigma.mk (y.val,k.val))
  exact tensorPoint_balancing P Q L (r.hom.mapElements.obj y) h p k q

def baseChangeTotal : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (compositionRightBundle (Bundle.reindex P r) Q L) ⟶
    SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (Bundle.reindex (compositionRightBundle P Q L) r) :=
  balancedDesc (Bundle.reindex P r) Q L (rawBaseChange P Q L r) (rawBaseChange_balanced P Q L r)

theorem baseChangeTotal_fac : balancedMap (Bundle.reindex P r) Q L ≫ baseChangeTotal P Q L r =
    rawBaseChange P Q L r := balancedDesc_fac _ _ _ _ _

end SquareKit.SheafGroupoid.Bundle.BalancedFactorization
namespace SquareKit.SheafGroupoid.Bundle.BalancedFactorization
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {H K : Operations J} [H.Laws] [K.Laws]
variable {X Y : Sheaf J (Type (max u v))} (P : Principal H X)
  (Q : Principal K H.objects) (L : LeftAction Q) (r : Y ⟶ X)

theorem baseChangeTotal_projection : baseChangeTotal P Q L r ≫
    SplitSheaf.p (Bundle.reindex (compositionRightBundle P Q L) r).family =
      SplitSheaf.p (compositionRightBundle (Bundle.reindex P r) Q L).family := by
  apply (cancel_epi (balancedMap (Bundle.reindex P r) Q L)).mp
  rw [← Category.assoc, baseChangeTotal_fac]
  have h := (SplitSheaf.extension_pullback (compositionRightBundle P Q L).family (baseMap r)).lift_snd
    (rawForget P Q r ≫ balancedMap P Q L) (rawBase P Q r) (rawBase_square P Q L r)
  apply h.trans
  apply Sheaf.hom_ext
  ext U z
  rcases z with ⟨⟨⟨y,h⟩,p⟩,⟨⟨⟨h',k⟩,q⟩,e⟩⟩
  change h' = h at e
  subst h'
  rfl

def baseChangeFamily : (compositionRightBundle (Bundle.reindex P r) Q L).family.family ⟶
    (Bundle.reindex (compositionRightBundle P Q L) r).family.family :=
  SplitSheaf.mapOfTotal (baseChangeTotal P Q L r) (baseChangeTotal_projection P Q L r)

theorem baseChangeFamily_fac : balancedMap (Bundle.reindex P r) Q L ≫
    SplitSheaf.totalMap (baseChangeFamily P Q L r) = rawBaseChange P Q L r := by
  unfold baseChangeFamily
  rw [SplitSheaf.totalMap_mapOfTotal, baseChangeTotal_fac]

theorem baseChangeFamily_tensorPoint (y : Y.obj.Elements) (m : H.Section y.obj)
    (p : Fiber H Y (Bundle.reindex P r).family y m) (k : K.Section y.obj)
    (q : Fiber K H.objects Q.family (atSection m) k) :
    (baseChangeFamily P Q L r).app (point K Y y k)
      (tensorPoint (Bundle.reindex P r) Q L y m p k q) =
        tensorPoint P Q L (r.hom.mapElements.obj y) m p k q := by
  have he := (congrArg (fun f : ordinarySource (Bundle.reindex P r) Q ⟶
      SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (Bundle.reindex (compositionRightBundle P Q L) r) =>
    f.hom.app y.obj (pairPoint (Bundle.reindex P r) Q y m p k q))
    (baseChangeFamily_fac P Q L r)).trans (rawBaseChange_pair P Q L r y m p k q)
  exact eq_of_heq (Sigma.mk.inj_iff.mp he).2

end SquareKit.SheafGroupoid.Bundle.BalancedFactorization
namespace SquareKit.SheafGroupoid.Bundle.BalancedFactorization
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {K : Operations J} [K.Laws] {Y : Sheaf J (Type (max u v))}

theorem equivariant_of_local_points (A : SplitSheaf.Ty Y)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
    (S T : Action K Y) (f : S.family.family ⟶ T.family.family)
    (hf : ∀ (y : Y.obj.Elements), A.family.obj y →
      ∀ (k l : K.Section y.obj) (g : k ⟶ l) (t : Fiber K Y S.family y l),
        f.app (point K Y y k) (S.act y g t) = T.act y g (f.app (point K Y y l) t))
    (y : Y.obj.Elements) {k l : K.Section y.obj} (g : k ⟶ l)
    (t : Fiber K Y S.family y l) :
    f.app (point K Y y k) (S.act y g t) = T.act y g (f.app (point K Y y l) t) := by
  apply SplitSheafDescent.fiber_ext T.family (point K Y y k)
    (Presheaf.imageSieve (SplitSheaf.p A).hom y.val)
    (Presheaf.imageSieve_mem J (SplitSheaf.p A).hom y.val)
  rintro V j ⟨⟨z,a⟩,ha⟩
  change z = Y.obj.map j.op y.val at ha
  subst z
  let y' := Y.obj.elementsMk (op V) (Y.obj.map j.op y.val)
  let e : y ⟶ y' := ElementFamilies.along Y.obj j.op y.val
  let g' := (K.sectionRestriction j.op).map g
  let t' := S.family.family.map (pointArrow K Y e l) t
  have hn₁ := NatTrans.naturality_apply f (pointArrow K Y e k) (S.act y g t)
  have hn₂ := NatTrans.naturality_apply f (pointArrow K Y e l) t
  calc
    _ = f.app (point K Y y' (k.restrict K j.op))
        (S.family.family.map (pointArrow K Y e k) (S.act y g t)) := hn₁.symm
    _ = f.app (point K Y y' (k.restrict K j.op)) (S.act y' g' t') :=
      congrArg (f.app (point K Y y' (k.restrict K j.op))) (S.natural e g t)
    _ = T.act y' g' (f.app (point K Y y' (l.restrict K j.op)) t') :=
      hf y' a (k.restrict K j.op) (l.restrict K j.op) g' t'
    _ = T.act y' g' (T.family.family.map (pointArrow K Y e l)
        (f.app (point K Y y l) t)) := congrArg (T.act y' g') hn₂
    _ = _ := (T.natural e g (f.app (point K Y y l) t)).symm

variable {H : Operations J} [H.Laws] {X : Sheaf J (Type (max u v))}
variable (P : Principal H X) (Q : Principal K H.objects) (L : LeftAction Q) (r : Y ⟶ X)

theorem baseChangeFamily_equivariant (y : Y.obj.Elements) {k l : K.Section y.obj}
    (g : k ⟶ l) (t : Fiber K Y (compositionRightBundle (Bundle.reindex P r) Q L).family y l) :
    (baseChangeFamily P Q L r).app (point K Y y k)
      ((compositionRightBundle (Bundle.reindex P r) Q L).act y g t) =
    (Bundle.reindex (compositionRightBundle P Q L) r).act y g
      ((baseChangeFamily P Q L r).app (point K Y y l) t) := by
  apply equivariant_of_local_points (cover (Bundle.reindex P r))
    (compositionRightBundle (Bundle.reindex P r) Q L).toAction
    (Bundle.reindex (compositionRightBundle P Q L) r).toAction (baseChangeFamily P Q L r) ?_ y g t
  intro z a k l g t
  let m := coverAnchor (Bundle.reindex P r) z a
  let p := coverPoint (Bundle.reindex P r) z a
  let a' : (cover (Bundle.reindex P r)).family.obj z := ⟨⟨(z.val,m.val),p⟩,rfl⟩
  let q := Descent.evaluationEquiv (compositionDatum (Bundle.reindex P r) Q L) z a' l t
  have ht : tensorPoint (Bundle.reindex P r) Q L z m p l q = t :=
    Equiv.symm_apply_apply _ t
  calc
    _ = (baseChangeFamily P Q L r).app (point K Y z k)
        ((compositionRightBundle (Bundle.reindex P r) Q L).act z g
          (tensorPoint (Bundle.reindex P r) Q L z m p l q)) :=
      congrArg (fun s => (baseChangeFamily P Q L r).app (point K Y z k)
        ((compositionRightBundle (Bundle.reindex P r) Q L).act z g s)) ht.symm
    _ = (baseChangeFamily P Q L r).app (point K Y z k)
        (tensorPoint (Bundle.reindex P r) Q L z m p k (Q.act (atSection m) g q)) :=
      congrArg ((baseChangeFamily P Q L r).app (point K Y z k))
        (tensorPoint_equivariant (Bundle.reindex P r) Q L z m p g q).symm
    _ = tensorPoint P Q L (r.hom.mapElements.obj z) m p k (Q.act (atSection m) g q) :=
      baseChangeFamily_tensorPoint P Q L r z m p k _
    _ = (Bundle.reindex (compositionRightBundle P Q L) r).act z g
        (tensorPoint P Q L (r.hom.mapElements.obj z) m p l q) :=
      tensorPoint_equivariant P Q L (r.hom.mapElements.obj z) m p g q
    _ = (Bundle.reindex (compositionRightBundle P Q L) r).act z g
        ((baseChangeFamily P Q L r).app (point K Y z l)
          (tensorPoint (Bundle.reindex P r) Q L z m p l q)) :=
      congrArg ((Bundle.reindex (compositionRightBundle P Q L) r).act z g)
        (baseChangeFamily_tensorPoint P Q L r z m p l q).symm
    _ = _ := congrArg (fun s => (Bundle.reindex (compositionRightBundle P Q L) r).act z g
      ((baseChangeFamily P Q L r).app (point K Y z l) s)) ht

def baseChangeMap : Bundle.Map (compositionRightBundle (Bundle.reindex P r) Q L)
    (Bundle.reindex (compositionRightBundle P Q L) r) where
  hom := baseChangeFamily P Q L r
  equivariant y _ _ g t := baseChangeFamily_equivariant P Q L r y g t

theorem baseChangeMap_fac : balancedMap (Bundle.reindex P r) Q L ≫
    (baseChangeMap P Q L r).totalMap = rawBaseChange P Q L r :=
  baseChangeFamily_fac P Q L r

end SquareKit.SheafGroupoid.Bundle.BalancedFactorization
namespace SquareKit.SheafGroupoid.Bundle.BalancedFactorization
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {H K : Operations J} [H.Laws] [K.Laws]
variable {X Y : Sheaf J (Type (max u v))} (P : Principal H X)
  (Q : Principal K H.objects) (L : LeftAction Q) (r : Y ⟶ X)

def baseChangeIso : compositionRightBundle (Bundle.reindex P r) Q L ≅
    Bundle.reindex (compositionRightBundle P Q L) r :=
  asIso (show compositionRightBundle (Bundle.reindex P r) Q L ⟶
    Bundle.reindex (compositionRightBundle P Q L) r from baseChangeMap P Q L r)

theorem baseChangeIso_fac : balancedMap (Bundle.reindex P r) Q L ≫
    (baseChangeIso P Q L r).hom.totalMap = rawBaseChange P Q L r :=
  baseChangeMap_fac P Q L r

end SquareKit.SheafGroupoid.Bundle.BalancedFactorization
