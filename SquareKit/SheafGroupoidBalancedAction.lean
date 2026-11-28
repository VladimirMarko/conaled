import SquareKit.SheafGroupoidBalancedFactorization
import Mathlib.CategoryTheory.Sites.RegularEpi

/-! The residual commuting action on a balanced product. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bundle.BalancedAction
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {H K : Operations J} [H.Laws] [K.Laws]
variable {X : Sheaf J (Type (max u v))} {P R : Principal H X}
  (Q : Principal K H.objects) (L : LeftAction Q) (f : Bundle.Map P R)

theorem rawMap_square : ordinaryFirst P Q ≫ Q.toAction.projection =
    (ordinarySecond P Q ≫ f.totalMap) ≫ SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor R := by
  apply Sheaf.hom_ext
  ext U z
  rcases z with ⟨⟨⟨x,h⟩,p⟩,⟨⟨⟨h',k⟩,q⟩,e⟩⟩
  change h' = h at e
  subst h'
  rfl

def rawMap : ordinarySource P Q ⟶ ordinarySource R Q :=
  (ordinary_pullback R Q).lift (ordinaryFirst P Q)
    (ordinarySecond P Q ≫ f.totalMap) (rawMap_square Q f)

theorem rawMap_pair (x : X.obj.Elements) (m : H.Section x.obj)
    (p : Fiber H X P.family x m) (k : K.Section x.obj)
    (q : Fiber K H.objects Q.family (atSection m) k) :
    (rawMap Q f).hom.app x.obj (pairPoint P Q x m p k q) =
      pairPoint R Q x m (f.hom.app (point H X x m) p) k q := by
  apply Types.ext_of_isPullback (SheafImage.sections_isPullback (ordinary_pullback R Q) x.obj)
  · exact congrArg (fun a : ordinarySource P Q ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total Q =>
      a.hom.app x.obj (pairPoint P Q x m p k q)) ((ordinary_pullback R Q).lift_fst _ _ _)
  · exact congrArg (fun a : ordinarySource P Q ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total R =>
      a.hom.app x.obj (pairPoint P Q x m p k q)) ((ordinary_pullback R Q).lift_snd _ _ _)

theorem rawTensor_balanced : IsBalanced P Q L (rawMap Q f ≫ balancedMap R Q L) := by
  intro x m n h p k q
  change (balancedMap R Q L).hom.app x.obj ((rawMap Q f).hom.app x.obj _) =
    (balancedMap R Q L).hom.app x.obj ((rawMap Q f).hom.app x.obj _)
  rw [rawMap_pair, rawMap_pair, f.equivariant]
  exact balancedMap_balancing R Q L x h (f.hom.app (point H X x m) p) k q

def tensorMapTotal : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (compositionRightBundle P Q L) ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (compositionRightBundle R Q L) :=
  balancedDesc P Q L (rawMap Q f ≫ balancedMap R Q L) (rawTensor_balanced Q L f)

theorem tensorMapTotal_fac : balancedMap P Q L ≫ tensorMapTotal Q L f =
    rawMap Q f ≫ balancedMap R Q L := balancedDesc_fac _ _ _ _ _

theorem tensorMapTotal_projection : tensorMapTotal Q L f ≫
    SplitSheaf.p (compositionRightBundle R Q L).family =
      SplitSheaf.p (compositionRightBundle P Q L).family := by
  apply (cancel_epi (balancedMap P Q L)).mp
  rw [← Category.assoc, tensorMapTotal_fac]
  apply Sheaf.hom_ext
  ext U z
  rcases z with ⟨⟨⟨x,h⟩,p⟩,⟨⟨⟨h',k⟩,q⟩,e⟩⟩
  change h' = h at e
  subst h'
  exact congrArg Sigma.fst ((congrArg ((balancedMap R Q L).hom.app U)
    (rawMap_pair Q f (X.obj.elementsMk U x) ⟨h⟩ p ⟨k⟩ q)).trans
      (balancedMap_pair R Q L (X.obj.elementsMk U x) ⟨h⟩ _ ⟨k⟩ q))

def tensorMapFamily : (compositionRightBundle P Q L).family.family ⟶
    (compositionRightBundle R Q L).family.family :=
  SplitSheaf.mapOfTotal (tensorMapTotal Q L f) (tensorMapTotal_projection Q L f)

theorem tensorMapFamily_fac : balancedMap P Q L ≫ SplitSheaf.totalMap (tensorMapFamily Q L f) =
    rawMap Q f ≫ balancedMap R Q L := by
  unfold tensorMapFamily
  rw [SplitSheaf.totalMap_mapOfTotal, tensorMapTotal_fac]

theorem tensorMapFamily_tensorPoint (x : X.obj.Elements) (m : H.Section x.obj)
    (p : Fiber H X P.family x m) (k : K.Section x.obj)
    (q : Fiber K H.objects Q.family (atSection m) k) :
    (tensorMapFamily Q L f).app (point K X x k) (tensorPoint P Q L x m p k q) =
      tensorPoint R Q L x m (f.hom.app (point H X x m) p) k q := by
  have he := congrArg (fun a : ordinarySource P Q ⟶ SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (compositionRightBundle R Q L) =>
    a.hom.app x.obj (pairPoint P Q x m p k q)) (tensorMapFamily_fac Q L f)
  have hp := (congrArg ((balancedMap R Q L).hom.app x.obj) (rawMap_pair Q f x m p k q)).trans
    (balancedMap_pair R Q L x m (f.hom.app (point H X x m) p) k q)
  exact eq_of_heq (Sigma.mk.inj_iff.mp (he.trans hp)).2

theorem tensorMapFamily_equivariant (x : X.obj.Elements) {k l : K.Section x.obj}
    (g : k ⟶ l) (t : Fiber K X (compositionRightBundle P Q L).family x l) :
    (tensorMapFamily Q L f).app (point K X x k) ((compositionRightBundle P Q L).act x g t) =
      (compositionRightBundle R Q L).act x g ((tensorMapFamily Q L f).app (point K X x l) t) := by
  apply equivariant_of_local_points (cover P) (compositionRightBundle P Q L).toAction
    (compositionRightBundle R Q L).toAction (tensorMapFamily Q L f) ?_ x g t
  intro z a k l g t
  let m := coverAnchor P z a
  let p := coverPoint P z a
  let a' : (cover P).family.obj z := ⟨⟨(z.val,m.val),p⟩,rfl⟩
  let q := Descent.evaluationEquiv (compositionDatum P Q L) z a' l t
  have ht : tensorPoint P Q L z m p l q = t := Equiv.symm_apply_apply _ t
  rw [← ht, ← tensorPoint_equivariant, tensorMapFamily_tensorPoint, tensorMapFamily_tensorPoint]
  exact tensorPoint_equivariant R Q L z m (f.hom.app (point H X z m) p) g q

def tensorMap : Bundle.Map (compositionRightBundle P Q L) (compositionRightBundle R Q L) where
  hom := tensorMapFamily Q L f
  equivariant x _ _ g t := tensorMapFamily_equivariant Q L f x g t

end SquareKit.SheafGroupoid.Bundle.BalancedAction
namespace SquareKit.SheafGroupoid.Bundle.BalancedAction
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (G : Operations J) [G.Laws]

abbrev arrowContext := SplitSheaf.extension (homFamily G)

def arrowContextIso : arrowContext G ≅ G.arrows :=
  SplitSheaf.displayIso (SheafRelation.lift G.source G.target)

def arrowSource : arrowContext G ⟶ G.objects :=
  SplitSheaf.p (homFamily G) ≫ SheafRelation.fst G.objects G.objects

def arrowTarget : arrowContext G ⟶ G.objects :=
  SplitSheaf.p (homFamily G) ≫ SheafRelation.snd G.objects G.objects

def arrowAt {U : Cᵒᵖ} (z : (arrowContext G).obj.obj U) :
    (⟨z.1.1⟩ : G.Section U) ⟶ ⟨z.1.2⟩ :=
  (G.sectionArrowEquiv _ _).symm ⟨z.2.val,
    congrArg Prod.fst z.2.property, congrArg Prod.snd z.2.property⟩

theorem arrowAt_restrict {U V : Cᵒᵖ} (f : U ⟶ V) (z : (arrowContext G).obj.obj U) :
    (G.sectionRestriction f).map (arrowAt G z) = arrowAt G ((arrowContext G).obj.map f z) := by
  apply Operations.Arrow.ext
  apply sectionEquiv.injective
  change sectionEquiv (sectionEquiv.symm (G.arrows.obj.map f
      (sectionEquiv (sectionEquiv.symm z.2.val)))) =
    sectionEquiv (sectionEquiv.symm (G.arrows.obj.map f z.2.val))
  simp only [Equiv.apply_symm_apply]

variable {G} {H : Operations J} [H.Laws] (P : Principal H G.objects) (M : LeftAction P)

def leftOnP : Bundle.Map (Bundle.reindex P (arrowSource G)) (Bundle.reindex P (arrowTarget G)) where
  hom := {
    app z := ↾M.act (arrowAt G z.val.1) ⟨z.val.2⟩
    naturality := by
      intro z w f
      ext p
      rcases z with @⟨U,⟨z,m⟩⟩
      rcases w with @⟨V,⟨w,n⟩⟩
      rcases f with ⟨f,hf⟩
      change U ⟶ V at f
      have hz : (arrowContext G).obj.map f z = w := congrArg Prod.fst hf
      have hm : H.objects.obj.map f m = n := congrArg Prod.snd hf
      subst w
      subst n
      change M.act (arrowAt G ((arrowContext G).obj.map f z)) ((⟨m⟩ : H.Section U).restrict H f)
        (P.family.family.map (pointArrow H G.objects
          (ElementFamilies.along G.objects.obj f z.1.1) ⟨m⟩) p) =
        P.family.family.map (pointArrow H G.objects
          (ElementFamilies.along G.objects.obj f z.1.2) ⟨m⟩) (M.act (arrowAt G z) ⟨m⟩ p)
      rw [← arrowAt_restrict]
      exact (M.natural f (arrowAt G z) ⟨m⟩ p).symm }
  equivariant x m n h p := M.commute (arrowAt G x.val) h p

end SquareKit.SheafGroupoid.Bundle.BalancedAction
namespace SquareKit.SheafGroupoid.Bundle.BalancedAction
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {H K : Operations J} [H.Laws] [K.Laws]
variable {X Y : Sheaf J (Type (max u v))} (P : Principal H X)
  (Q : Principal K H.objects) (L : LeftAction Q) (r : Y ⟶ X)

theorem baseChangeInv_tensorPoint (y : Y.obj.Elements) (m : H.Section y.obj)
    (p : Fiber H Y (Bundle.reindex P r).family y m) (k : K.Section y.obj)
    (q : Fiber K H.objects Q.family (atSection m) k) :
    (baseChangeIso P Q L r).inv.hom.app (point K Y y k)
      (tensorPoint P Q L (r.hom.mapElements.obj y) m p k q) =
        tensorPoint (Bundle.reindex P r) Q L y m p k q := by
  apply (baseChangeIso P Q L r).hom.injective y k
  have he := congrArg (fun f : Bundle.reindex (compositionRightBundle P Q L) r ⟶
      Bundle.reindex (compositionRightBundle P Q L) r =>
    f.hom.app (point K Y y k) (tensorPoint P Q L (r.hom.mapElements.obj y) m p k q))
    (baseChangeIso P Q L r).inv_hom_id
  exact he.trans (baseChangeFamily_tensorPoint P Q L r y m p k q).symm

variable {G : Operations J} [G.Laws]
variable (R : Principal H G.objects) (M : LeftAction R)

def arrowTensorMap : Bundle.Map
    (Bundle.reindex (compositionRightBundle R Q L) (arrowSource G))
    (Bundle.reindex (compositionRightBundle R Q L) (arrowTarget G)) :=
  (baseChangeIso R Q L (arrowSource G)).inv.comp
    ((tensorMap Q L (leftOnP R M)).comp (baseChangeIso R Q L (arrowTarget G)).hom)

theorem arrowTensorMap_tensorPoint (z : (arrowContext G).obj.Elements)
    (m : H.Section z.obj)
    (p : Fiber H G.objects R.family ((arrowSource G).hom.mapElements.obj z) m)
    (k : K.Section z.obj) (q : Fiber K H.objects Q.family (atSection m) k) :
    (arrowTensorMap Q L R M).hom.app (point K (arrowContext G) z k)
      (tensorPoint R Q L ((arrowSource G).hom.mapElements.obj z) m p k q) =
    tensorPoint R Q L ((arrowTarget G).hom.mapElements.obj z) m
      (M.act (arrowAt G z.val) m p) k q := by
  have h₁ := baseChangeInv_tensorPoint R Q L (arrowSource G) z m p k q
  have h₂ := tensorMapFamily_tensorPoint Q L (leftOnP R M) z m p k q
  have h₃ := baseChangeFamily_tensorPoint R Q L (arrowTarget G) z m
    (M.act (arrowAt G z.val) m p) k q
  exact (congrArg (fun t => (baseChangeIso R Q L (arrowTarget G)).hom.hom.app
      (point K (arrowContext G) z k)
      ((tensorMap Q L (leftOnP R M)).hom.app (point K (arrowContext G) z k) t)) h₁).trans
    ((congrArg ((baseChangeIso R Q L (arrowTarget G)).hom.hom.app
      (point K (arrowContext G) z k)) h₂).trans h₃)

def arrowPoint {U : Cᵒᵖ} {x y : G.Section U} (g : x ⟶ y) : (arrowContext G).obj.obj U :=
  ⟨(x.val,y.val),⟨sectionEquiv g.map,
    Prod.ext (G.sectionArrowEquiv x y g).property.1 (G.sectionArrowEquiv x y g).property.2⟩⟩

theorem arrowAt_arrowPoint {U : Cᵒᵖ} {x y : G.Section U} (g : x ⟶ y) :
    arrowAt G (arrowPoint g) = g := by
  apply Operations.Arrow.ext
  exact sectionEquiv.symm_apply_apply g.map

theorem arrowPoint_restrict {U V : Cᵒᵖ} (f : U ⟶ V) {x y : G.Section U} (g : x ⟶ y) :
    (arrowContext G).obj.map f (arrowPoint g) = arrowPoint ((G.sectionRestriction f).map g) := by
  refine @Sigma.ext _ _ ((arrowContext G).obj.map f (arrowPoint g))
    (arrowPoint ((G.sectionRestriction f).map g)) rfl ?_
  apply heq_of_eq
  apply Subtype.ext
  change G.arrows.obj.map f (sectionEquiv g.map) =
    sectionEquiv ((Operations.SectionArrow.restrict G f g).map)
  rw [Operations.SectionArrow.restrict_map, sectionEquiv_naturality]

def residualAct {U : Cᵒᵖ} {x y : G.Section U} (g : x ⟶ y) (k : K.Section U) :
    Fiber K G.objects (compositionRightBundle R Q L).family (atSection x) k →
      Fiber K G.objects (compositionRightBundle R Q L).family (atSection y) k :=
  (arrowTensorMap Q L R M).hom.app
    (point K (arrowContext G) ((arrowContext G).obj.elementsMk U (arrowPoint g)) k)

theorem residualAct_tensorPoint {U : Cᵒᵖ} {x y : G.Section U} (g : x ⟶ y)
    (m : H.Section U) (p : Fiber H G.objects R.family (atSection x) m)
    (k : K.Section U) (q : Fiber K H.objects Q.family (atSection m) k) :
    residualAct Q L R M g k (tensorPoint R Q L (atSection x) m p k q) =
      tensorPoint R Q L (atSection y) m (M.act g m p) k q := by
  have he := arrowTensorMap_tensorPoint Q L R M
    ((arrowContext G).obj.elementsMk U (arrowPoint g)) m p k q
  rw [arrowAt_arrowPoint] at he
  exact he

theorem residualAct_natural {U V : Cᵒᵖ} (f : U ⟶ V) {x y : G.Section U}
    (g : x ⟶ y) (k : K.Section U)
    (t : Fiber K G.objects (compositionRightBundle R Q L).family (atSection x) k) :
    (compositionRightBundle R Q L).family.family.map (pointArrow K G.objects
      (ElementFamilies.along G.objects.obj f y.val) k) (residualAct Q L R M g k t) =
    residualAct Q L R M ((G.sectionRestriction f).map g) (k.restrict K f)
      ((compositionRightBundle R Q L).family.family.map (pointArrow K G.objects
        (ElementFamilies.along G.objects.obj f x.val) k) t) := by
  let e : ((arrowContext G).obj.elementsMk U (arrowPoint g)) ⟶
      ((arrowContext G).obj.elementsMk V (arrowPoint ((G.sectionRestriction f).map g))) :=
    ⟨f,arrowPoint_restrict f g⟩
  exact (NatTrans.naturality_apply (arrowTensorMap Q L R M).hom
    (pointArrow K (arrowContext G) e k) t).symm

theorem residualAct_commute {U : Cᵒᵖ} {x y : G.Section U} (g : x ⟶ y)
    {k l : K.Section U} (h : k ⟶ l)
    (t : Fiber K G.objects (compositionRightBundle R Q L).family (atSection x) l) :
    residualAct Q L R M g k ((compositionRightBundle R Q L).act (atSection x) h t) =
    (compositionRightBundle R Q L).act (atSection y) h (residualAct Q L R M g l t) :=
  (arrowTensorMap Q L R M).equivariant
    ((arrowContext G).obj.elementsMk U (arrowPoint g)) h t

end SquareKit.SheafGroupoid.Bundle.BalancedAction
namespace SquareKit.SheafGroupoid.Bundle.BalancedAction
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H K : Operations J} [G.Laws] [H.Laws] [K.Laws]
variable (P : Principal H G.objects) (M : LeftAction P)
  (Q : Principal K H.objects) (L : LeftAction Q)

omit [G.Laws] in
theorem tensorFiber_ext {U : Cᵒᵖ} (x y : G.Section U) (k : K.Section U)
    (s t : Fiber K G.objects (compositionRightBundle P Q L).family (atSection y) k)
    (h : ∀ (V : Cᵒᵖ) (f : U ⟶ V) (m : H.Section V)
      (_p : Fiber H G.objects P.family (atSection (x.restrict G f)) m),
      (compositionRightBundle P Q L).family.family.map (pointArrow K G.objects
        (ElementFamilies.along G.objects.obj f y.val) k) s =
      (compositionRightBundle P Q L).family.family.map (pointArrow K G.objects
        (ElementFamilies.along G.objects.obj f y.val) k) t) : s = t := by
  apply SplitSheafDescent.fiber_ext (compositionRightBundle P Q L).family
    (point K G.objects (atSection y) k)
    (Presheaf.imageSieve P.toAction.projection.hom x.val)
    (Presheaf.imageSieve_mem J P.toAction.projection.hom x.val)
  rintro V f ⟨⟨⟨z,m⟩,p⟩,hp⟩
  change z = G.objects.obj.map f.op x.val at hp
  subst z
  exact h (op V) f.op ⟨m⟩ p

theorem residualAct_identity {U : Cᵒᵖ} (x : G.Section U) (k : K.Section U)
    (t : Fiber K G.objects (compositionRightBundle P Q L).family (atSection x) k) :
    residualAct Q L P M (𝟙 x) k t = t := by
  apply tensorFiber_ext P Q L x x k
  intro V f m p
  rw [residualAct_natural, CategoryTheory.Functor.map_id]
  let z := atSection (x.restrict G f)
  let k' := k.restrict K f
  let t' := (compositionRightBundle P Q L).family.family.map (pointArrow K G.objects
    (ElementFamilies.along G.objects.obj f x.val) k) t
  let a : (cover P).family.obj z := ⟨⟨(z.val,m.val),p⟩,rfl⟩
  let q : Fiber K H.objects Q.family (atSection m) k' :=
    Descent.evaluationEquiv (compositionDatum P Q L) z a k' t'
  have ht : tensorPoint P Q L z m p k' q = t' := Equiv.symm_apply_apply _ t'
  change residualAct Q L P M (𝟙 (x.restrict G f)) k' t' = t'
  calc
    _ = residualAct Q L P M (𝟙 (x.restrict G f)) k' (tensorPoint P Q L z m p k' q) :=
      congrArg (residualAct Q L P M (𝟙 (x.restrict G f)) k') ht.symm
    _ = tensorPoint P Q L z m (M.act (𝟙 (x.restrict G f)) m p) k' q :=
      residualAct_tensorPoint Q L P M (𝟙 (x.restrict G f)) m p k' q
    _ = tensorPoint P Q L z m p k' q :=
      congrArg (fun p => tensorPoint P Q L z m p k' q) (M.identity (x.restrict G f) m p)
    _ = t' := ht

theorem residualAct_comp {U : Cᵒᵖ} {x y z : G.Section U} (g : x ⟶ y) (h : y ⟶ z)
    (k : K.Section U)
    (t : Fiber K G.objects (compositionRightBundle P Q L).family (atSection x) k) :
    residualAct Q L P M h k (residualAct Q L P M g k t) =
      residualAct Q L P M (g ≫ h) k t := by
  apply tensorFiber_ext P Q L x z k
  intro V f m p
  rw [residualAct_natural, residualAct_natural, residualAct_natural, CategoryTheory.Functor.map_comp]
  let x' := atSection (x.restrict G f)
  let k' := k.restrict K f
  let t' := (compositionRightBundle P Q L).family.family.map (pointArrow K G.objects
    (ElementFamilies.along G.objects.obj f x.val) k) t
  let a : (cover P).family.obj x' := ⟨⟨(x'.val,m.val),p⟩,rfl⟩
  let q : Fiber K H.objects Q.family (atSection m) k' :=
    Descent.evaluationEquiv (compositionDatum P Q L) x' a k' t'
  have ht : tensorPoint P Q L x' m p k' q = t' := Equiv.symm_apply_apply _ t'
  change residualAct Q L P M ((G.sectionRestriction f).map h) k'
      (residualAct Q L P M ((G.sectionRestriction f).map g) k' t') =
    residualAct Q L P M ((G.sectionRestriction f).map g ≫ (G.sectionRestriction f).map h) k' t'
  let g' := (G.sectionRestriction f).map g
  let h' := (G.sectionRestriction f).map h
  calc
    _ = residualAct Q L P M h' k' (residualAct Q L P M g' k'
        (tensorPoint P Q L x' m p k' q)) :=
      congrArg (fun t => residualAct Q L P M h' k' (residualAct Q L P M g' k' t)) ht.symm
    _ = residualAct Q L P M h' k'
        (tensorPoint P Q L (atSection (y.restrict G f)) m (M.act g' m p) k' q) :=
      congrArg (residualAct Q L P M h' k') (residualAct_tensorPoint Q L P M g' m p k' q)
    _ = tensorPoint P Q L (atSection (z.restrict G f)) m (M.act h' m (M.act g' m p)) k' q :=
      residualAct_tensorPoint Q L P M h' m (M.act g' m p) k' q
    _ = tensorPoint P Q L (atSection (z.restrict G f)) m (M.act (g' ≫ h') m p) k' q :=
      congrArg (fun p => tensorPoint P Q L (atSection (z.restrict G f)) m p k' q) (M.comp g' h' m p)
    _ = residualAct Q L P M (g' ≫ h') k' (tensorPoint P Q L x' m p k' q) :=
      (residualAct_tensorPoint Q L P M (g' ≫ h') m p k' q).symm
    _ = _ := congrArg (residualAct Q L P M (g' ≫ h') k') ht

def compositionLeftAction : LeftAction (compositionRightBundle P Q L) where
  act := residualAct Q L P M
  identity := residualAct_identity P M Q L
  comp := residualAct_comp P M Q L
  natural := residualAct_natural Q L P M
  commute := residualAct_commute Q L P M

end SquareKit.SheafGroupoid.Bundle.BalancedAction
namespace SquareKit.SheafGroupoid.Bundle.BalancedAction
open CategoryTheory Opposite Limits SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bundle.BalancedProduct SquareKit.SheafGroupoid.Bundle.BalancedFactorization
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H K : Operations J} [G.Laws] [H.Laws] [K.Laws]
variable (P : Principal H G.objects) (M : LeftAction P)
  (Q : Principal K H.objects) (L : LeftAction Q)

omit [G.Laws] in
theorem arrowContextIso_source : (arrowContextIso G).hom ≫ G.source = arrowSource G := by
  apply Sheaf.hom_ext
  ext U z
  exact congrArg Prod.fst z.2.property

omit [G.Laws] in
theorem arrowContextIso_target : (arrowContextIso G).hom ≫ G.target = arrowTarget G := by
  apply Sheaf.hom_ext
  ext U z
  exact congrArg Prod.snd z.2.property

theorem arrowTensorMap_fac : rawBaseChange P Q L (arrowSource G) ≫
    (arrowTensorMap Q L P M).totalMap =
      rawMap Q (leftOnP P M) ≫ rawBaseChange P Q L (arrowTarget G) := by
  apply Sheaf.hom_ext
  ext U a
  rcases a with ⟨⟨⟨z,m⟩,p⟩,⟨⟨⟨m',k⟩,q⟩,e⟩⟩
  change m' = m at e
  subst m'
  let x := (arrowContext G).obj.elementsMk U z
  have hl := congrArg ((arrowTensorMap Q L P M).totalMap.hom.app U)
    (rawBaseChange_pair P Q L (arrowSource G) x ⟨m⟩ p ⟨k⟩ q)
  have hl' := congrArg
    (fun t : Fiber K (arrowContext G)
      (Bundle.reindex (compositionRightBundle P Q L) (arrowTarget G)).family x ⟨k⟩ =>
      (⟨(z,k),t⟩ : (SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (Bundle.reindex (compositionRightBundle P Q L)
        (arrowTarget G))).obj.obj U))
    (arrowTensorMap_tensorPoint Q L P M x ⟨m⟩ p ⟨k⟩ q)
  have hr := congrArg ((rawBaseChange P Q L (arrowTarget G)).hom.app U)
    (rawMap_pair Q (leftOnP P M) x ⟨m⟩ p ⟨k⟩ q)
  have hr' := rawBaseChange_pair P Q L (arrowTarget G) x ⟨m⟩
    (M.act (arrowAt G z) ⟨m⟩ p) ⟨k⟩ q
  exact (hl.trans hl').trans (hr.trans hr').symm

omit M [G.Laws] in
theorem arrowRawQuotient_effectiveEpi : EffectiveEpi (rawBaseChange P Q L (arrowSource G)) := by
  have hf := baseChangeMap_fac P Q L (arrowSource G)
  have : Presheaf.IsLocallySurjective J (rawBaseChange P Q L (arrowSource G)).hom := by
    rw [← hf]
    change Presheaf.IsLocallySurjective J
      ((balancedMap (Bundle.reindex P (arrowSource G)) Q L).hom ≫
        (baseChangeMap P Q L (arrowSource G)).totalMap.hom)
    have := (baseChangeMap P Q L (arrowSource G)).totalMap_isLocallySurjective
    infer_instance
  have : Epi (rawBaseChange P Q L (arrowSource G)) := inferInstance
  have := IsRegularEpiCategory.regularEpiOfEpi (rawBaseChange P Q L (arrowSource G))
  infer_instance

def actionTotal : SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (Bundle.reindex (compositionRightBundle P Q L) (arrowSource G)) ⟶
    SquareKit.SheafGroupoid.Bundle.BalancedProduct.total (compositionRightBundle P Q L) :=
  (arrowTensorMap Q L P M).totalMap ≫
    SplitSheaf.lift (compositionRightBundle P Q L).family (baseMap (arrowTarget G))

theorem actionTotal_base : actionTotal P M Q L ≫ (compositionRightBundle P Q L).toAction.projection =
    (Bundle.reindex (compositionRightBundle P Q L) (arrowSource G)).toAction.projection ≫ arrowTarget G := rfl

theorem actionTotal_anchor : actionTotal P M Q L ≫ SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor (compositionRightBundle P Q L) =
    SquareKit.SheafGroupoid.Bundle.BalancedProduct.anchor (Bundle.reindex (compositionRightBundle P Q L) (arrowSource G)) := rfl

theorem actionTotal_fac : rawBaseChange P Q L (arrowSource G) ≫ actionTotal P M Q L =
    rawMap Q (leftOnP P M) ≫ rawBaseChange P Q L (arrowTarget G) ≫
      SplitSheaf.lift (compositionRightBundle P Q L).family (baseMap (arrowTarget G)) := by
  rw [actionTotal, ← Category.assoc, arrowTensorMap_fac, Category.assoc]

theorem balancedMap_left_equivariant {U : Cᵒᵖ} {x y : G.Section U} (g : x ⟶ y)
    (m : H.Section U) (p : Fiber H G.objects P.family (atSection x) m)
    (k : K.Section U) (q : Fiber K H.objects Q.family (atSection m) k) :
    (balancedMap P Q L).hom.app U (pairPoint P Q (atSection y) m (M.act g m p) k q) =
      ⟨(y.val,k.val), (compositionLeftAction P M Q L).act g k
        (tensorPoint P Q L (atSection x) m p k q)⟩ := by
  exact (balancedMap_pair P Q L (atSection y) m (M.act g m p) k q).trans
    (congrArg (Sigma.mk (y.val,k.val)) (residualAct_tensorPoint Q L P M g m p k q).symm)

end SquareKit.SheafGroupoid.Bundle.BalancedAction
