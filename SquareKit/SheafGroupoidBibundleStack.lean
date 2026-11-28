import SquareKit.SheafGroupoidBibundleAssociator
import SquareKit.SheafGroupoidStack

/-! Reconstruction of principal bibundles from stack maps, including every modification. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bibundle
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (P : Bibundle G H) {X Y : Sheaf J (Type (max u v))}

open SquareKit.SheafGroupoid.Bundle.BalancedAction

def arrowLift {m n : G.Object X} (f : m ⟶ n) : X ⟶ arrowContext G := ⟨{
  app U := ↾fun x => ⟨(m.map.hom.app U x,n.map.hom.app U x), ⟨f.map.hom.app U x,
    Prod.ext (congrArg (fun k => k.hom.app U x) f.source)
      (congrArg (fun k => k.hom.app U x) f.target)⟩⟩
  naturality := by
    intro U V e
    ext x
    apply injective_of_mono ((arrowContextIso G).hom.hom.app V)
    exact NatTrans.naturality_apply f.map.hom e x }⟩

def sourceMap {m n : G.Object X} (f : m ⟶ n) :
    Bundle.Map (Bundle.reindex P.right m.map) (Bundle.reindex P.right n.map) :=
  (leftOnP P.right P.left).reindex (arrowLift f)

theorem sourceMap_id (m : G.Object X) : sourceMap P (𝟙 m) = Bundle.Map.ident (Bundle.reindex P.right m.map) := by
  apply Bundle.Map.ext
  apply NatTrans.ext
  funext z
  apply ConcreteCategory.hom_ext
  intro p
  change P.left.act (arrowValue G (𝟙 m) (X.obj.elementsMk z.obj z.val.1)) ⟨z.val.2⟩ p = p
  rw [arrowValue_id]
  exact P.left.identity _ _ p

theorem sourceMap_comp {m n l : G.Object X} (f : m ⟶ n) (g : n ⟶ l) :
    sourceMap P (f ≫ g) = (sourceMap P f).comp (sourceMap P g) := by
  apply Bundle.Map.ext
  apply NatTrans.ext
  funext z
  apply ConcreteCategory.hom_ext
  intro p
  change P.left.act (arrowValue G (f ≫ g) (X.obj.elementsMk z.obj z.val.1)) ⟨z.val.2⟩ p =
    P.left.act (arrowValue G g (X.obj.elementsMk z.obj z.val.1)) ⟨z.val.2⟩
      (P.left.act (arrowValue G f (X.obj.elementsMk z.obj z.val.1)) ⟨z.val.2⟩ p)
  rw [arrowValue_comp]
  exact (P.left.comp _ _ _ p).symm

def sourceFunctor : G.Object X ⥤ Principal H X where
  obj m := Bundle.reindex P.right m.map
  map := sourceMap P
  map_id := sourceMap_id P
  map_comp := sourceMap_comp P

theorem sourceFunctor_reindex (r : Y ⟶ X) :
    G.restriction r ⋙ sourceFunctor P = sourceFunctor P ⋙ Bundle.restriction r := rfl

def sourceTransformation : G.pseudofunctor ⟶ Bundle.pseudofunctor H where
  app X := (sourceFunctor P (X := X.as.unop)).toCatHom
  naturality _ := Iso.refl _
  naturality_naturality := by
    intro X Y f g h
    obtain rfl := LocallyDiscrete.eq_of_hom h
    have hh : h = 𝟙 f := Subsingleton.elim _ _
    subst h
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    ext m
    simp
  naturality_id X := by
    cases X
    apply Cat.Hom₂.ext
    ext m
    exact (sourceMap_id P _).symm
  naturality_comp f g := by
    cases f
    cases g
    apply Cat.Hom₂.ext
    ext m
    exact (sourceMap_id P _).symm

def stackTransformation : Bundle.pseudofunctor G ⟶ Bundle.pseudofunctor H :=
  (Bundle.universalEquivalence G (Bundle.pseudofunctor H)).inverse.obj (sourceTransformation P)

def stackTransformation_recovery : Bundle.unit G ≫ stackTransformation P ≅ sourceTransformation P :=
  (Bundle.universalEquivalence G (Bundle.pseudofunctor H)).counitIso.app (sourceTransformation P)

variable {P} {Q : Bibundle G H}

def sourceModification (f : P ⟶ Q) : sourceTransformation P ⟶ sourceTransformation Q where
  as.app X := Cat.Hom₂.ofNatTrans {
    app m := f.toMap.reindex m.map
    naturality m n g := by
      apply Bundle.Map.ext
      apply NatTrans.ext
      funext z
      apply ConcreteCategory.hom_ext
      intro p
      exact (f.left_equivariant (arrowValue G g
        (X.as.unop.obj.elementsMk z.obj z.val.1)) ⟨z.val.2⟩ p) }
  as.naturality r := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext m
    rfl

def sourceAssignment : Bibundle G H ⥤ (G.pseudofunctor ⟶ Bundle.pseudofunctor H) where
  obj := sourceTransformation
  map := sourceModification
  map_id P := by
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro X
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext m
    rfl
  map_comp f g := by
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro X
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext m
    rfl

def stackAssignment : Bibundle G H ⥤ (Bundle.pseudofunctor G ⟶ Bundle.pseudofunctor H) :=
  sourceAssignment ⋙ (Bundle.universalEquivalence G (Bundle.pseudofunctor H)).inverse



open StackDescentTransformation
variable (θ : G.pseudofunctor ⟶ Bundle.pseudofunctor H)

def recoveredRight : Principal H G.objects :=
  (component θ G.objects).obj (SquareKit.SheafGroupoid.Bibundle.identityObject G)

def recoveredMap {X : Sheaf J (Type (max u v))} {m n : G.Object X} (f : m ⟶ n) :
    Bundle.Map (Bundle.reindex (recoveredRight θ) m.map)
      (Bundle.reindex (recoveredRight θ) n.map) :=
  mapHom θ (M₁ := SquareKit.SheafGroupoid.Bibundle.identityObject G)
    (M₂ := SquareKit.SheafGroupoid.Bibundle.identityObject G) m.map n.map f

theorem recoveredMap_id {X : Sheaf J (Type (max u v))} (m : G.Object X) :
    recoveredMap θ (𝟙 m) = Bundle.Map.ident _ := mapHom_id θ m.map (SquareKit.SheafGroupoid.Bibundle.identityObject G)

theorem recoveredMap_comp {X : Sheaf J (Type (max u v))} {m n l : G.Object X}
    (f : m ⟶ n) (g : n ⟶ l) :
    recoveredMap θ (f ≫ g) = (recoveredMap θ f).comp (recoveredMap θ g) :=
  (mapHom_comp θ (M₁ := SquareKit.SheafGroupoid.Bibundle.identityObject G)
    (M₂ := SquareKit.SheafGroupoid.Bibundle.identityObject G) (M₃ := SquareKit.SheafGroupoid.Bibundle.identityObject G)
    m.map n.map l.map f g).symm

theorem recoveredMap_reindex {X Y : Sheaf J (Type (max u v))} {m n : G.Object X}
    (f : m ⟶ n) (r : Y ⟶ X) :
    (recoveredMap θ f).reindex r = recoveredMap θ ((G.restriction r).map f) := by
  have h := mapHom_pullHom θ (M₁ := SquareKit.SheafGroupoid.Bibundle.identityObject G)
    (M₂ := SquareKit.SheafGroupoid.Bibundle.identityObject G) m.map n.map f r (r ≫ m.map) (r ≫ n.map) rfl rfl
  change recoveredMap θ ((𝟙 _ ≫ 𝟙 _) ≫ (G.restriction r).map f ≫ (𝟙 _ ≫ 𝟙 _)) =
    (Bundle.Map.ident _).comp ((Bundle.Map.ident _).comp
      (((recoveredMap θ f).reindex r).comp ((Bundle.Map.ident _).comp (Bundle.Map.ident _)))) at h
  simp only [Category.id_comp, Category.comp_id] at h
  apply Bundle.Map.ext
  apply NatTrans.ext
  funext z
  apply ConcreteCategory.hom_ext
  intro p
  exact congrArg (fun a : Bundle.Map (Bundle.reindex (recoveredRight θ) (r ≫ m.map))
    (Bundle.reindex (recoveredRight θ) (r ≫ n.map)) => a.hom.app z p) h.symm

def genericArrow : (⟨arrowSource G⟩ : G.Object (arrowContext G)) ⟶ ⟨arrowTarget G⟩ where
  map := (arrowContextIso G).hom
  source := arrowContextIso_source
  target := arrowContextIso_target

def recoveredGeneric : Bundle.Map (Bundle.reindex (recoveredRight θ) (arrowSource G))
    (Bundle.reindex (recoveredRight θ) (arrowTarget G)) := recoveredMap θ genericArrow

def recoveredAct {U : Cᵒᵖ} {x y : G.Section U} (g : x ⟶ y) (k : H.Section U) :
    Fiber H G.objects (recoveredRight θ).family (atSection x) k →
      Fiber H G.objects (recoveredRight θ).family (atSection y) k :=
  (recoveredGeneric θ).hom.app
    (point H (arrowContext G) ((arrowContext G).obj.elementsMk U (arrowPoint g)) k)

theorem recoveredAct_natural {U V : Cᵒᵖ} (f : U ⟶ V) {x y : G.Section U}
    (g : x ⟶ y) (k : H.Section U)
    (t : Fiber H G.objects (recoveredRight θ).family (atSection x) k) :
    (recoveredRight θ).family.family.map (pointArrow H G.objects
      (ElementFamilies.along G.objects.obj f y.val) k) (recoveredAct θ g k t) =
    recoveredAct θ ((G.sectionRestriction f).map g) (k.restrict H f)
      ((recoveredRight θ).family.family.map (pointArrow H G.objects
        (ElementFamilies.along G.objects.obj f x.val) k) t) := by
  let e : ((arrowContext G).obj.elementsMk U (arrowPoint g)) ⟶
      ((arrowContext G).obj.elementsMk V (arrowPoint ((G.sectionRestriction f).map g))) :=
    ⟨f,arrowPoint_restrict f g⟩
  exact (NatTrans.naturality_apply (recoveredGeneric θ).hom
    (pointArrow H (arrowContext G) e k) t).symm

theorem recoveredAct_commute {U : Cᵒᵖ} {x y : G.Section U} (g : x ⟶ y)
    {k l : H.Section U} (h : k ⟶ l)
    (t : Fiber H G.objects (recoveredRight θ).family (atSection x) l) :
    recoveredAct θ g k ((recoveredRight θ).act (atSection x) h t) =
    (recoveredRight θ).act (atSection y) h (recoveredAct θ g l t) :=
  (recoveredGeneric θ).equivariant
    ((arrowContext G).obj.elementsMk U (arrowPoint g)) h t



theorem arrowPoint_arrowValue {X : Sheaf J (Type (max u v))} {m n : G.Object X}
    (f : m ⟶ n) (z : X.obj.Elements) :
    arrowPoint (arrowValue G f z) = (arrowLift f).hom.app z.obj z.val := by
  refine @Sigma.ext _ _ _ _ rfl ?_
  apply heq_of_eq
  apply Subtype.ext
  exact sectionEquiv.apply_symm_apply _

theorem recoveredAct_arrowValue {X : Sheaf J (Type (max u v))} {m n : G.Object X}
    (f : m ⟶ n) (z : X.obj.Elements) (k : H.Section z.obj)
    (p : Fiber H X (Bundle.reindex (recoveredRight θ) m.map).family z k) :
    recoveredAct θ (arrowValue G f z) k p =
      (recoveredMap θ f).hom.app (point H X z k) p := by
  have h := recoveredMap_reindex θ (genericArrow (G := G)) (arrowLift f)
  change (recoveredGeneric θ).reindex (arrowLift f) = recoveredMap θ f at h
  have hv := congrArg (fun a : Bundle.Map
      (Bundle.reindex (recoveredRight θ) m.map) (Bundle.reindex (recoveredRight θ) n.map) =>
    a.hom.app (point H X z k) p) h
  let idx := (SheafRelation.product G.objects G.objects).obj.elementsMk z.obj
    ((value G m z).val,(value G n z).val)
  have ha : (arrowPoint (arrowValue G f z)).2 = ((arrowLift f).hom.app z.obj z.val).2 := by
    apply Subtype.ext
    exact sectionEquiv.apply_symm_apply _
  have he := congrArg (fun a : (homFamily G).family.obj idx =>
    show Fiber H G.objects (recoveredRight θ).family (atSection (value G n z)) k from
      (recoveredGeneric θ).hom.app (point H (arrowContext G)
        ((arrowContext G).obj.elementsMk z.obj ⟨idx.val,a⟩) k) p) ha
  exact he.trans hv

theorem recoveredAct_identity {U : Cᵒᵖ} (x : G.Section U) (k : H.Section U)
    (p : Fiber H G.objects (recoveredRight θ).family (atSection x) k) :
    recoveredAct θ (𝟙 x) k p = p := by
  have h := recoveredAct_arrowValue θ (𝟙 (SquareKit.SheafGroupoid.Bibundle.identityObject G))
    (atSection x) k p
  rw [arrowValue_id, recoveredMap_id] at h
  exact h



def chainIndex : SheafRelation.product (arrowContext G) G.objects ⟶
    SheafRelation.product G.objects G.objects :=
  SheafRelation.lift (SheafRelation.fst _ _ ≫ arrowTarget G) (SheafRelation.snd _ _)

abbrev chainContext := SplitSheaf.extension (SplitSheaf.tySub (homFamily G) (chainIndex (G := G)))

def chainFirst : chainContext (G := G) ⟶ arrowContext G :=
  SplitSheaf.p _ ≫ SheafRelation.fst _ _

def chainSecond : chainContext (G := G) ⟶ arrowContext G :=
  SplitSheaf.lift (homFamily G) chainIndex

def chainArrowFirst : (⟨chainFirst ≫ arrowSource G⟩ : G.Object (chainContext (G := G))) ⟶
    ⟨chainFirst ≫ arrowTarget G⟩ := (G.restriction chainFirst).map genericArrow

def chainArrowSecond : (⟨chainFirst ≫ arrowTarget G⟩ : G.Object (chainContext (G := G))) ⟶
    ⟨chainSecond ≫ arrowTarget G⟩ := (G.restriction chainSecond).map genericArrow

def chainPoint {U : Cᵒᵖ} {x y z : G.Section U} (f : x ⟶ y) (g : y ⟶ z) :
    (chainContext (G := G)).obj.obj U :=
  ⟨(arrowPoint f,z.val),⟨sectionEquiv g.map,
    Prod.ext (G.sectionArrowEquiv y z g).property.1 (G.sectionArrowEquiv y z g).property.2⟩⟩

theorem chainArrowFirst_value {U : Cᵒᵖ} {x y z : G.Section U} (f : x ⟶ y) (g : y ⟶ z) :
    arrowValue G chainArrowFirst ((chainContext (G := G)).obj.elementsMk U (chainPoint f g)) = f := by
  apply Operations.Arrow.ext
  exact sectionEquiv.symm_apply_apply f.map

theorem chainArrowSecond_value {U : Cᵒᵖ} {x y z : G.Section U} (f : x ⟶ y) (g : y ⟶ z) :
    arrowValue G chainArrowSecond ((chainContext (G := G)).obj.elementsMk U (chainPoint f g)) = g := by
  apply Operations.Arrow.ext
  exact sectionEquiv.symm_apply_apply g.map

theorem recoveredAct_comp {U : Cᵒᵖ} {x y z : G.Section U} (f : x ⟶ y) (g : y ⟶ z)
    (k : H.Section U) (p : Fiber H G.objects (recoveredRight θ).family (atSection x) k) :
    recoveredAct θ g k (recoveredAct θ f k p) = recoveredAct θ (f ≫ g) k p := by
  let c := (chainContext (G := G)).obj.elementsMk U (chainPoint f g)
  have hf := recoveredAct_arrowValue θ chainArrowFirst c k p
  have hg := recoveredAct_arrowValue θ chainArrowSecond c k (recoveredAct θ f k p)
  have hfg := recoveredAct_arrowValue θ (chainArrowFirst ≫ chainArrowSecond) c k p
  rw [chainArrowFirst_value] at hf
  rw [chainArrowSecond_value] at hg
  rw [arrowValue_comp, chainArrowFirst_value, chainArrowSecond_value, recoveredMap_comp] at hfg
  exact hg.trans ((congrArg ((recoveredMap θ chainArrowSecond).hom.app
    (point H (chainContext (G := G)) c k)) hf).trans hfg.symm)

def recoveredLeft : LeftAction (recoveredRight θ) where
  act := recoveredAct θ
  identity := recoveredAct_identity θ
  comp := recoveredAct_comp θ
  natural := recoveredAct_natural θ
  commute := recoveredAct_commute θ

def recoveredBibundle : Bibundle G H where
  right := recoveredRight θ
  left := recoveredLeft θ



theorem sourceMap_recovered {X : Sheaf J (Type (max u v))} {m n : G.Object X} (f : m ⟶ n) :
    sourceMap (recoveredBibundle θ) f = recoveredMap θ f := by
  apply Bundle.Map.ext
  apply NatTrans.ext
  funext z
  apply ConcreteCategory.hom_ext
  intro p
  exact recoveredAct_arrowValue θ f (X.obj.elementsMk z.obj z.val.1) ⟨z.val.2⟩ p

def reconstructionComponent (X : Sheaf J (Type (max u v))) :
    component θ X ≅ sourceFunctor (recoveredBibundle θ) :=
  NatIso.ofComponents (fun m => (comparison θ m.map).app (SquareKit.SheafGroupoid.Bibundle.identityObject G)) (by
    intro m n f
    change (component θ X).map f ≫ (comparison θ n.map).hom.app (SquareKit.SheafGroupoid.Bibundle.identityObject G) =
      (comparison θ m.map).hom.app (SquareKit.SheafGroupoid.Bibundle.identityObject G) ≫ sourceMap (recoveredBibundle θ) f
    rw [sourceMap_recovered]
    simp only [recoveredMap, mapHom, Iso.hom_inv_id_app_assoc])

theorem reconstructionComponent_reindex {X Y : Sheaf J (Type (max u v))}
    (r : Y ⟶ X) (m : G.Object X) :
    (comparison θ (r ≫ m.map)).hom.app (SquareKit.SheafGroupoid.Bibundle.identityObject G) =
      (comparison θ r).hom.app m ≫
        ((comparison θ m.map).hom.app (SquareKit.SheafGroupoid.Bibundle.identityObject G)).reindex r := by
  have h := comparison_comp_hom θ m.map r (r ≫ m.map) rfl
    (SquareKit.SheafGroupoid.Bibundle.identityObject G)
  change (comparison θ (r ≫ m.map)).hom.app (SquareKit.SheafGroupoid.Bibundle.identityObject G) ≫
      (𝟙 _ ≫ 𝟙 _) =
    (component θ Y).map (𝟙 ((G.restriction r).obj m) ≫ 𝟙 ((G.restriction r).obj m)) ≫
      (comparison θ r).hom.app m ≫
        ((comparison θ m.map).hom.app (SquareKit.SheafGroupoid.Bibundle.identityObject G)).reindex r at h
  rw [Category.id_comp, Category.id_comp, (component θ Y).map_id, Category.id_comp,
    Category.comp_id] at h
  exact h

def reconstructionIso : θ ≅ sourceTransformation (recoveredBibundle θ) :=
  Pseudofunctor.StrongTrans.isoMk
    (fun X => Cat.Hom.isoMk (reconstructionComponent θ X.as.unop)) (by
      intro X Y r
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext m
      exact reconstructionComponent_reindex θ r.as.unop m)

variable {θ} {ψ : G.pseudofunctor ⟶ Bundle.pseudofunctor H}

def recoveredModificationRight (Γ : θ ⟶ ψ) : Bundle.Map (recoveredRight θ) (recoveredRight ψ) :=
  (Γ.as.app (.mk (op G.objects))).toNatTrans.app (SquareKit.SheafGroupoid.Bibundle.identityObject G)

theorem modification_mapHom
    {D : Type*} [Category D] {F T : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat}
    {α β : F ⟶ T} (Γ : α ⟶ β)
    {X₁ X₂ Y : D} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (h : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    (T.map f₁.op.toLoc).toFunctor.map ((Γ.as.app (.mk (op X₁))).toNatTrans.app M₁) ≫
      mapHom β f₁ f₂ h = mapHom α f₁ f₂ h ≫
        (T.map f₂.op.toLoc).toFunctor.map ((Γ.as.app (.mk (op X₂))).toNatTrans.app M₂) := by
  dsimp only [mapHom]
  simp only [Category.assoc]
  rw [reassoc_of% modification_naturality_inv Γ.as f₁ M₁]
  rw [← (Γ.as.app (.mk (op Y))).toNatTrans.naturality_assoc]
  rw [modification_naturality Γ.as f₂ M₂]

theorem recoveredModification_map (Γ : θ ⟶ ψ) {X : Sheaf J (Type (max u v))}
    {m n : G.Object X} (f : m ⟶ n) :
    ((recoveredModificationRight Γ).reindex m.map).comp (recoveredMap ψ f) =
      (recoveredMap θ f).comp ((recoveredModificationRight Γ).reindex n.map) :=
  modification_mapHom Γ (M₁ := SquareKit.SheafGroupoid.Bibundle.identityObject G)
    (M₂ := SquareKit.SheafGroupoid.Bibundle.identityObject G) m.map n.map f

def recoveredModification (Γ : θ ⟶ ψ) : recoveredBibundle θ ⟶ recoveredBibundle ψ where
  toMap := recoveredModificationRight Γ
  left_equivariant {U x y} g k p := by
    have h := recoveredModification_map Γ (genericArrow (G := G))
    exact (congrArg (fun a : Bundle.Map
      (Bundle.reindex (recoveredRight θ) (arrowSource G))
      (Bundle.reindex (recoveredRight ψ) (arrowTarget G)) =>
        a.hom.app (point H (arrowContext G)
          ((arrowContext G).obj.elementsMk U (arrowPoint g)) k) p) h).symm

def reconstruction : (G.pseudofunctor ⟶ Bundle.pseudofunctor H) ⥤ Bibundle G H where
  obj := recoveredBibundle
  map := recoveredModification
  map_id θ := by apply SquareKit.SheafGroupoid.Bibundle.Map.ext; rfl
  map_comp Γ Δ := by apply SquareKit.SheafGroupoid.Bibundle.Map.ext; rfl



variable (P)
def sourceUnitMap : P ⟶ recoveredBibundle (sourceTransformation P) where
  toMap := Bundle.Map.ident P.right
  left_equivariant g k p := by
    change P.left.act g k p = P.left.act (arrowAt G (arrowPoint g)) k p
    rw [arrowAt_arrowPoint]

def sourceUnitIso : 𝟭 (Bibundle G H) ≅ sourceAssignment ⋙ reconstruction :=
  NatIso.ofComponents (fun P => asIso (sourceUnitMap P)) (by
    intro P Q f
    apply SquareKit.SheafGroupoid.Bibundle.Map.ext
    rfl)

def sourceCounitIso : reconstruction ⋙ sourceAssignment ≅
    𝟭 (G.pseudofunctor ⟶ Bundle.pseudofunctor H) :=
  NatIso.ofComponents (fun θ => (reconstructionIso θ).symm) (by
    intro θ ψ Γ
    apply Pseudofunctor.StrongTrans.homCategory.ext
    intro X
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext m
    exact modification_naturality_inv Γ.as m.map (SquareKit.SheafGroupoid.Bibundle.identityObject G))

def sourceEquivalence : Bibundle G H ≌ (G.pseudofunctor ⟶ Bundle.pseudofunctor H) :=
  CategoryTheory.Equivalence.mk sourceAssignment reconstruction sourceUnitIso sourceCounitIso

def stackEquivalence : Bibundle G H ≌ (Bundle.pseudofunctor G ⟶ Bundle.pseudofunctor H) :=
  sourceEquivalence.trans (Bundle.universalEquivalence G (Bundle.pseudofunctor H)).symm


end SquareKit.SheafGroupoid.Bibundle
