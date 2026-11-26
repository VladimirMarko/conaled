import SquareKit.SheafAssociatedBundleMaps
import SquareKit.SheafDisplayFamilyDescent
import SquareKit.SheafFamilyDescent
import SquareKit.SheafSiteComparisonQuotient

/-! Associated displays commute with restriction and effective sheaf descent. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SheafAssociatedBundle
open CategoryTheory Opposite ElementFamilies
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Sheaf J GrpCat.{max u v}} {M : Sheaf J (Type (max u v))}
  {X Y Z : Sheaf J (Type (max u v))}
variable (P : SheafTorsor.Torsor G X) (a : SheafActionQuotient.Action G M)

/-- Quotient representatives over a new base map to the original associated display. -/
def reindexPairs (f : Y ⟶ X) :
    InvariantMap (SheafTorsor.reindex P f) a (SplitSheaf.tySub (associated P a) f) where
  value y p m := classOf P a (f.hom.mapElements.obj y) p m
  natural k p m := classOf_natural P a (f.hom.mapElements.map k) p m
  invariant y g p m := classOf_diagonal P a (f.hom.mapElements.obj y) g p m

/-- The comparison is constructed from the quotient universal property. -/
def reindexMap (f : Y ⟶ X) :
    associated (SheafTorsor.reindex P f) a ⟶ SplitSheaf.tySub (associated P a) f :=
  (reindexPairs P a f).descend

@[simp] theorem reindexMap_classOf (f : Y ⟶ X) (y : Y.obj.Elements)
    (p : (SheafTorsor.reindex P f).family.family.obj y) (m : M.obj.obj y.obj) :
    (reindexMap P a f).app y (classOf (SheafTorsor.reindex P f) a y p m) =
      classOf P a (f.hom.mapElements.obj y) p m := (reindexPairs P a f).descend_classOf y p m

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_reindexMap (f : Y ⟶ X) (y : Y.obj.Elements)
    (p : (SheafTorsor.reindex P f).family.family.obj y)
    (s : (associated (SheafTorsor.reindex P f) a).family.obj y) :
    evaluate P a (f.hom.mapElements.obj y) p ((reindexMap P a f).app y s) =
      evaluate (SheafTorsor.reindex P f) a y p s := by
  conv_lhs => rw [← classOf_evaluate (SheafTorsor.reindex P f) a y p s]
  rw [reindexMap_classOf, evaluate_classOf]

set_option backward.isDefEq.respectTransparency false in
instance reindexMap_isIso (f : Y ⟶ X) : IsIso (reindexMap P a f) := by
  have hi : @IsIso (Y.obj.Elements ⥤ Type (max u v)) _ _ _ (reindexMap P a f) := by
    apply SplitSheafDescent.isIso_of_local_bijective (SheafTorsor.reindex P f).family
    intro y p
    constructor
    · intro s t h
      apply (evaluate (SheafTorsor.reindex P f) a y p).injective
      rw [← evaluate_reindexMap P a f y p s, ← evaluate_reindexMap P a f y p t, h]
    · intro t
      refine ⟨classOf (SheafTorsor.reindex P f) a y p
        (evaluate P a (f.hom.mapElements.obj y) p t), ?_⟩
      rw [reindexMap_classOf, classOf_evaluate]
  let e := SplitSheaf.isoMk (asIso (show
    (associated (SheafTorsor.reindex P f) a).family ⟶
      (SplitSheaf.tySub (associated P a) f).family from reindexMap P a f))
  exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

/-- Base change of the constructed display is isomorphic to construction after base change. -/
def reindexIso (f : Y ⟶ X) :
    SplitSheaf.tySub (associated P a) f ≅ associated (SheafTorsor.reindex P f) a :=
  (asIso (reindexMap P a f)).symm

@[simp] theorem reindexIso_inv_classOf (f : Y ⟶ X) (y : Y.obj.Elements)
    (p : (SheafTorsor.reindex P f).family.family.obj y) (m : M.obj.obj y.obj) :
    (reindexIso P a f).inv.app y (classOf (SheafTorsor.reindex P f) a y p m) =
      classOf P a (f.hom.mapElements.obj y) p m := reindexMap_classOf P a f y p m

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem reindexIso_hom_classOf (f : Y ⟶ X) (y : Y.obj.Elements)
    (p : (SheafTorsor.reindex P f).family.family.obj y) (m : M.obj.obj y.obj) :
    (reindexIso P a f).hom.app y (classOf P a (f.hom.mapElements.obj y) p m) =
      classOf (SheafTorsor.reindex P f) a y p m := by
  have h := congrArg (fun k => k.app y (classOf (SheafTorsor.reindex P f) a y p m))
    (reindexIso P a f).inv_hom_id
  change (reindexIso P a f).hom.app y ((reindexIso P a f).inv.app y
    (classOf (SheafTorsor.reindex P f) a y p m)) = _ at h
  rwa [reindexIso_inv_classOf] at h

theorem reindexMap_id : reindexMap P a (𝟙 X) = 𝟙 (associated P a) := by
  apply hom_ext
  intro x p m
  exact reindexMap_classOf P a (𝟙 X) x p m

set_option backward.isDefEq.respectTransparency false in
theorem reindexMap_comp (f : Y ⟶ X) (g : Z ⟶ Y) :
    reindexMap P a (g ≫ f) = reindexMap (SheafTorsor.reindex P f) a g ≫
      (SplitSheaf.restriction g).map (reindexMap P a f) := by
  apply hom_ext
  intro z p m
  change (reindexMap P a (g ≫ f)).app z
    (classOf (SheafTorsor.reindex P (g ≫ f)) a z p m) =
    (reindexMap P a f).app (g.hom.mapElements.obj z)
      ((reindexMap (SheafTorsor.reindex P f) a g).app z
        (classOf (SheafTorsor.reindex P (g ≫ f)) a z p m))
  rw [reindexMap_classOf]
  exact ((congrArg ((reindexMap P a f).app (g.hom.mapElements.obj z))
    (reindexMap_classOf (SheafTorsor.reindex P f) a g z p m)).trans
    (reindexMap_classOf P a f (g.hom.mapElements.obj z) p m)).symm

theorem reindexIso_id : reindexIso P a (𝟙 X) = Iso.refl (associated P a) := by
  apply Iso.ext_inv
  exact reindexMap_id P a

theorem reindexIso_comp (f : Y ⟶ X) (g : Z ⟶ Y) :
    reindexIso P a (g ≫ f) = (SplitSheaf.restriction g).mapIso (reindexIso P a f) ≪≫
      reindexIso (SheafTorsor.reindex P f) a g := by
  apply Iso.ext_inv
  exact reindexMap_comp P a f g

/-- The two-step comparison retains each complete arbitrary-stage section. -/
theorem reindexMap_comp_apply (f : Y ⟶ X) (g : Z ⟶ Y) (z : Z.obj.Elements)
    (s : (associated (SheafTorsor.reindex P (g ≫ f)) a).family.obj z) :
    (reindexMap P a (g ≫ f)).app z s =
      (reindexMap P a f).app (g.hom.mapElements.obj z)
        ((reindexMap (SheafTorsor.reindex P f) a g).app z s) :=
  congrArg (fun k => k.app z s) (reindexMap_comp P a f g)

section Maps
variable {H : Sheaf J GrpCat.{max u v}} {N : Sheaf J (Type (max u v))}
  {φ : G ⟶ H} {Q : SheafTorsor.Torsor H X} {b : SheafActionQuotient.Action H N}

set_option backward.isDefEq.respectTransparency false in
theorem reindexMap_map (f : Y ⟶ X) (h : SheafTorsor.SemilinearMap φ P Q)
    (k : ActionMap φ a b) :
    map (h.reindex f) k ≫ reindexMap Q b f =
      reindexMap P a f ≫ (SplitSheaf.restriction f).map (map h k) := by
  apply hom_ext
  intro y p m
  change (reindexMap Q b f).app y ((map (h.reindex f) k).app y
    (classOf (SheafTorsor.reindex P f) a y p m)) =
    (map h k).app (f.hom.mapElements.obj y) ((reindexMap P a f).app y
      (classOf (SheafTorsor.reindex P f) a y p m))
  rw [map_classOf, reindexMap_classOf, reindexMap_classOf, map_classOf]
  rfl

end Maps

variable {P}
set_option backward.isDefEq.respectTransparency false in
/-- Restriction comparison is natural on every torsor arrow. -/
def functorReindex (f : Y ⟶ X) :
    SheafTorsor.restriction f ⋙ functor a Y ≅ functor a X ⋙ SplitSheaf.restriction f :=
  NatIso.ofComponents (fun P => (reindexIso P a f).symm) (by
    intro P Q h
    exact reindexMap_map P a f (SheafTorsor.SemilinearMap.ofArrow h) (ActionMap.ident a))

section Family
variable {I : Type (max u v)} {B : I → Sheaf J (Type (max u v))}
  (f : ∀ i, B i ⟶ X) (hf : SheafFamilyCover.JointlyLocallySurjective f)

/-- Effective recovery constructs associated family data on all compatible arrows.
The local comparison identifies its components with association of the input components. -/
def descentFunctor : (SheafTorsor.Stack.pseudofunctor G).DescentData f ⥤
    (SplitSheaf.pseudofunctor (J := J)).DescentData f :=
  (SheafFamilyDescent.torsorEquivalence G f hf).inverse ⋙
    functor a X ⋙ (SplitSheaf.pseudofunctor (J := J)).toDescentData f

set_option backward.isDefEq.respectTransparency false in
/-- Gluing the associated display data agrees naturally with associating the glued torsor. -/
def descentRecovery :
    descentFunctor a f hf ⋙ (SheafDisplayFamilyDescent.equivalence f hf).inverse ≅
      (SheafFamilyDescent.torsorEquivalence G f hf).inverse ⋙ functor a X :=
  NatIso.ofComponents (fun d =>
    ((SheafDisplayFamilyDescent.equivalence f hf).unitIso.app
      (associated ((SheafFamilyDescent.torsorEquivalence G f hf).inverse.obj d) a)).symm)
    (by
      intro d e h
      exact (SheafDisplayFamilyDescent.equivalence f hf).unitIso.inv.naturality
        ((functor a X).map ((SheafFamilyDescent.torsorEquivalence G f hf).inverse.map h)))

/-- Every local component is the constructed associated display of the original local torsor. -/
def descentLocalComparison (d : (SheafTorsor.Stack.pseudofunctor G).DescentData f) (i : I) :
    ((descentFunctor a f hf).obj d).obj i ≅ associated (d.obj i) a :=
  reindexIso ((SheafFamilyDescent.torsorEquivalence G f hf).inverse.obj d) a (f i) ≪≫
    (functor a (B i)).mapIso
      (((SheafFamilyDescent.torsorEquivalence G f hf).counitIso.app d).hom.hom i).toIso

set_option backward.isDefEq.respectTransparency false in
theorem descentLocalComparison_natural
    {d e : (SheafTorsor.Stack.pseudofunctor G).DescentData f} (h : d ⟶ e) (i : I) :
    ((descentFunctor a f hf).map h).hom i ≫ (descentLocalComparison a f hf e i).hom =
      (descentLocalComparison a f hf d i).hom ≫ (functor a (B i)).map (h.hom i) := by
  have hc := congrArg (fun k => (functor a (B i)).map k)
    (congrArg (fun k => k.hom i)
      ((SheafFamilyDescent.torsorEquivalence G f hf).counitIso.hom.naturality h))
  change (functor a (B i)).map
    ((((SheafFamilyDescent.torsorEquivalence G f hf).inverse.map h).reindex (f i)) ≫
      ((SheafFamilyDescent.torsorEquivalence G f hf).counitIso.app e).hom.hom i) =
    (functor a (B i)).map
      (((SheafFamilyDescent.torsorEquivalence G f hf).counitIso.app d).hom.hom i ≫ h.hom i) at hc
  rw [Functor.map_comp, Functor.map_comp] at hc
  have hn := (functorReindex a (f i)).inv.naturality
    ((SheafFamilyDescent.torsorEquivalence G f hf).inverse.map h)
  change (SplitSheaf.restriction (f i)).map
    ((functor a X).map ((SheafFamilyDescent.torsorEquivalence G f hf).inverse.map h)) ≫
      (reindexIso ((SheafFamilyDescent.torsorEquivalence G f hf).inverse.obj e) a (f i)).hom =
    (reindexIso ((SheafFamilyDescent.torsorEquivalence G f hf).inverse.obj d) a (f i)).hom ≫
      (functor a (B i)).map
        (((SheafFamilyDescent.torsorEquivalence G f hf).inverse.map h).reindex (f i)) at hn
  change (SplitSheaf.restriction (f i)).map
    ((functor a X).map ((SheafFamilyDescent.torsorEquivalence G f hf).inverse.map h)) ≫
      ((reindexIso ((SheafFamilyDescent.torsorEquivalence G f hf).inverse.obj e) a (f i)).hom ≫
        (functor a (B i)).map (((SheafFamilyDescent.torsorEquivalence G f hf).counitIso.app e).hom.hom i)) =
    ((reindexIso ((SheafFamilyDescent.torsorEquivalence G f hf).inverse.obj d) a (f i)).hom ≫
      (functor a (B i)).map (((SheafFamilyDescent.torsorEquivalence G f hf).counitIso.app d).hom.hom i)) ≫
        (functor a (B i)).map (h.hom i)
  rw [← Category.assoc, hn, Category.assoc, hc, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Associate each input local torsor and its actual overlap arrow. This construction
does not require the family to cover or a global recovered object. -/
def associatedData (d : (SheafTorsor.Stack.pseudofunctor G).DescentData f) :
    (SplitSheaf.pseudofunctor (J := J)).DescentData f where
  obj i := associated (d.obj i) a
  hom W q i j l r hl hr :=
    (reindexIso (d.obj i) a l).hom ≫ (functor a W).map (d.hom q l r hl hr) ≫
      (reindexIso (d.obj j) a r).inv
  pullHom_hom W' W k q q' hq i j l r hl hr kl kr hkl hkr := by
    subst kl; subst kr; subst q'
    change (SplitSheaf.restriction k).map
      ((reindexIso (d.obj i) a l).hom ≫ (functor a W).map (d.hom q l r hl hr) ≫
        (reindexIso (d.obj j) a r).inv) =
      (reindexIso (d.obj i) a (k ≫ l)).hom ≫
        (functor a W').map (d.hom (k ≫ q) (k ≫ l) (k ≫ r) _ _) ≫
          (reindexIso (d.obj j) a (k ≫ r)).inv
    have hd : (d.hom q l r hl hr).reindex k = d.hom (k ≫ q) (k ≫ l) (k ≫ r) _ _ :=
      d.pullHom_hom k q (k ≫ q) rfl l r hl hr (k ≫ l) (k ≫ r) rfl rfl
    rw [← hd, reindexIso_comp, reindexIso_comp]
    simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      Functor.map_comp, Category.assoc]
    have hn : (functor a W').map ((d.hom q l r hl hr).reindex k) ≫
        (reindexIso (SheafTorsor.reindex (d.obj j) r) a k).inv =
      (reindexIso (SheafTorsor.reindex (d.obj i) l) a k).inv ≫
        (SplitSheaf.restriction k).map ((functor a W).map (d.hom q l r hl hr)) :=
      reindexMap_map _ a k (SheafTorsor.SemilinearMap.ofArrow (d.hom q l r hl hr)) (ActionMap.ident a)
    rw [← Category.assoc ((functor a W').map ((d.hom q l r hl hr).reindex k)), hn]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  hom_self W q i l hl := by
    change (reindexIso (d.obj i) a l).hom ≫
      (functor a W).map (d.hom q l l hl hl) ≫ (reindexIso (d.obj i) a l).inv = _
    rw [d.hom_self q l hl]
    change (reindexIso (d.obj i) a l).hom ≫
      (functor a W).map (𝟙 (SheafTorsor.reindex (d.obj i) l)) ≫ (reindexIso (d.obj i) a l).inv = _
    rw [(functor a W).map_id]
    change (reindexIso (d.obj i) a l).hom ≫ 𝟙 _ ≫ (reindexIso (d.obj i) a l).inv = 𝟙 _
    rw [Category.id_comp]
    exact (reindexIso (d.obj i) a l).hom_inv_id
  hom_comp W q i j k l r t hl hr ht := by
    change ((reindexIso (d.obj i) a l).hom ≫ (functor a W).map (d.hom q l r hl hr) ≫
      (reindexIso (d.obj j) a r).inv) ≫
      ((reindexIso (d.obj j) a r).hom ≫ (functor a W).map (d.hom q r t hr ht) ≫
        (reindexIso (d.obj k) a t).inv) = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc ((functor a W).map (d.hom q l r hl hr)), ← Functor.map_comp, d.hom_comp]

set_option backward.isDefEq.respectTransparency false in
/-- All compatible local arrows induce the literal associated local arrows. -/
def associatedDataMap {d e : (SheafTorsor.Stack.pseudofunctor G).DescentData f} (h : d ⟶ e) :
    associatedData a f d ⟶ associatedData a f e where
  hom i := (functor a (B i)).map (h.hom i)
  comm W q i j l r hl hr := by
    have hn := (functorReindex a l).inv.naturality (h.hom i)
    change (SplitSheaf.restriction l).map ((functor a (B i)).map (h.hom i)) ≫
      (reindexIso (e.obj i) a l).hom = (reindexIso (d.obj i) a l).hom ≫
        (functor a W).map ((h.hom i).reindex l) at hn
    have hm : (functor a W).map ((h.hom j).reindex r) ≫ (reindexIso (e.obj j) a r).inv =
      (reindexIso (d.obj j) a r).inv ≫ (SplitSheaf.restriction r).map ((functor a (B j)).map (h.hom j)) :=
      reindexMap_map _ a r (SheafTorsor.SemilinearMap.ofArrow (h.hom j)) (ActionMap.ident a)
    have hc := congrArg ((functor a W).map) (h.comm q l r hl hr)
    change (functor a W).map ((h.hom i).reindex l ≫ e.hom q l r hl hr) =
      (functor a W).map (d.hom q l r hl hr ≫ (h.hom j).reindex r) at hc
    rw [Functor.map_comp, Functor.map_comp] at hc
    change (SplitSheaf.restriction l).map ((functor a (B i)).map (h.hom i)) ≫
      ((reindexIso (e.obj i) a l).hom ≫ (functor a W).map (e.hom q l r hl hr) ≫
        (reindexIso (e.obj j) a r).inv) =
      ((reindexIso (d.obj i) a l).hom ≫ (functor a W).map (d.hom q l r hl hr) ≫
        (reindexIso (d.obj j) a r).inv) ≫
          (SplitSheaf.restriction r).map ((functor a (B j)).map (h.hom j))
    rw [← Category.assoc _ (reindexIso (e.obj i) a l).hom _, hn]
    simp only [Category.assoc]
    rw [← Category.assoc ((functor a W).map ((h.hom i).reindex l)), hc]
    simp only [Category.assoc]
    rw [hm]

def associatedDataFunctor : (SheafTorsor.Stack.pseudofunctor G).DescentData f ⥤
    (SplitSheaf.pseudofunctor (J := J)).DescentData f where
  obj := associatedData a f
  map := associatedDataMap a f
  map_id d := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact (functor a (B i)).map_id (d.obj i)
  map_comp h k := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact (functor a (B i)).map_comp (h.hom i) (k.hom i)

set_option backward.isDefEq.respectTransparency false in
private theorem torsor_canonical_transition (P : SheafTorsor.Torsor G X)
    {W : Sheaf J (Type (max u v))} (q : W ⟶ X) {i j : I} (l : W ⟶ B i) (r : W ⟶ B j)
    (hl : l ≫ f i = q) (hr : r ≫ f j = q) :
    (((SheafTorsor.Stack.pseudofunctor G).toDescentData f).obj P).hom q l r hl hr =
      eqToHom (show SheafTorsor.reindex (SheafTorsor.reindex P (f i)) l =
        SheafTorsor.reindex (SheafTorsor.reindex P (f j)) r from
          congrArg (SheafTorsor.reindex P) (hl.trans hr.symm)) := by
  simp [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj,
    Pseudofunctor.mapComp', SheafTorsor.Stack.pseudofunctor, Functor.toPseudofunctor',
    pseudofunctorOfIsLocallyDiscrete]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
private theorem display_canonical_transition (T : SplitSheaf.Ty X)
    {W : Sheaf J (Type (max u v))} (q : W ⟶ X) {i j : I} (l : W ⟶ B i) (r : W ⟶ B j)
    (hl : l ≫ f i = q) (hr : r ≫ f j = q) :
    (((SplitSheaf.pseudofunctor (J := J)).toDescentData f).obj T).hom q l r hl hr =
      eqToHom (show SplitSheaf.tySub (SplitSheaf.tySub T (f i)) l =
        SplitSheaf.tySub (SplitSheaf.tySub T (f j)) r from
          congrArg (SplitSheaf.tySub T) (hl.trans hr.symm)) := by
  simp [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj,
    Pseudofunctor.mapComp', SplitSheaf.pseudofunctor, Functor.toPseudofunctor',
    pseudofunctorOfIsLocallyDiscrete]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
private theorem reindexIso_congr (P : SheafTorsor.Torsor G X)
    {W : Sheaf J (Type (max u v))} {l r : W ⟶ X} (h : l = r) :
    (reindexIso P a l).hom ≫ (functor a W).map (eqToHom (congrArg (SheafTorsor.reindex P) h)) =
      eqToHom (congrArg (SplitSheaf.tySub (associated P a)) h) ≫ (reindexIso P a r).hom := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]
  rw [(functor a W).map_id]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- The component comparisons respect the actual canonical overlap arrows. -/
def associatedDataOfGlobal (P : SheafTorsor.Torsor G X) :
    ((SplitSheaf.pseudofunctor (J := J)).toDescentData f).obj (associated P a) ≅
      associatedData a f (((SheafTorsor.Stack.pseudofunctor G).toDescentData f).obj P) :=
  Pseudofunctor.DescentData.isoMk (fun i => reindexIso P a (f i)) (by
    intro W q i j l r hl hr
    change (SplitSheaf.restriction l).map (reindexIso P a (f i)).hom ≫
      ((reindexIso (SheafTorsor.reindex P (f i)) a l).hom ≫
        (functor a W).map ((((SheafTorsor.Stack.pseudofunctor G).toDescentData f).obj P).hom q l r hl hr) ≫
          (reindexIso (SheafTorsor.reindex P (f j)) a r).inv) =
      (((SplitSheaf.pseudofunctor (J := J)).toDescentData f).obj (associated P a)).hom q l r hl hr ≫
        (SplitSheaf.restriction r).map (reindexIso P a (f j)).hom
    rw [torsor_canonical_transition f P q l r hl hr, display_canonical_transition f (associated P a) q l r hl hr]
    have hc := congrArg Iso.hom (reindexIso_comp P a (f i) l)
    change (reindexIso P a (l ≫ f i)).hom =
      (SplitSheaf.restriction l).map (reindexIso P a (f i)).hom ≫
        (reindexIso (SheafTorsor.reindex P (f i)) a l).hom at hc
    rw [← Category.assoc _ (reindexIso (SheafTorsor.reindex P (f i)) a l).hom _, ← hc,
      ← Category.assoc, reindexIso_congr a P (hl.trans hr.symm), Category.assoc,
      reindexIso_comp P a (f j) r]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id])

/-- Recovery-defined data and independently constructed local associated data agree
on every object, every overlap, and every compatible arrow. -/
def descentComparison : descentFunctor a f hf ≅ associatedDataFunctor a f :=
  NatIso.ofComponents (fun d =>
    associatedDataOfGlobal a f ((SheafFamilyDescent.torsorEquivalence G f hf).inverse.obj d) ≪≫
      (associatedDataFunctor a f).mapIso ((SheafFamilyDescent.torsorEquivalence G f hf).counitIso.app d))
    (by
      intro d e h
      apply Pseudofunctor.DescentData.hom_ext
      intro i
      exact descentLocalComparison_natural a f hf h i)

/-- Gluing the literal associated local data is naturally association of the glued torsor. -/
def associatedDataRecovery :
    associatedDataFunctor a f ⋙ (SheafDisplayFamilyDescent.equivalence f hf).inverse ≅
      (SheafFamilyDescent.torsorEquivalence G f hf).inverse ⋙ functor a X :=
  Functor.isoWhiskerRight (descentComparison a f hf).symm _ ≪≫ descentRecovery a f hf

end Family

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_reindexIso_hom (f : Y ⟶ X) (y : Y.obj.Elements)
    (p : (SheafTorsor.reindex P f).family.family.obj y)
    (s : (SplitSheaf.tySub (associated P a) f).family.obj y) :
    evaluate (SheafTorsor.reindex P f) a y p ((reindexIso P a f).hom.app y s) =
      evaluate P a (f.hom.mapElements.obj y) p s := by
  have h := evaluate_reindexMap P a f y p ((reindexIso P a f).hom.app y s)
  have e := congrArg (fun k => k.app y s) (reindexIso P a f).hom_inv_id
  change (reindexMap P a f).app y ((reindexIso P a f).hom.app y s) = s at e
  rw [e] at h
  exact h.symm

/-- The target-map section bridge commutes with arbitrary restriction. -/
theorem objectSection_reindex (F : SheafActionQuotient.Object a X) (f : Y ⟶ X) :
    mapSection (reindexIso F.torsor a f).hom (SplitSheaf.tmSub (objectSection F) f) =
      objectSection (SheafActionQuotient.reindex F f) := by
  apply section_ext
  intro y p
  change evaluate (SheafTorsor.reindex F.torsor f) a y p
    ((reindexIso F.torsor a f).hom.app y ((SplitSheaf.tmSub (objectSection F) f).val y)) = _
  rw [evaluate_reindexIso_hom]
  exact (objectSection_value F _ p).trans
    (objectSection_value (SheafActionQuotient.reindex F f) y p).symm



section FamilyRefinement
variable {I L : Type (max u v)} {B : I → Sheaf J (Type (max u v))}
    {D : L → Sheaf J (Type (max u v))}
    {f : ∀ i, B i ⟶ X} {g : ∀ j, D j ⟶ Y}
    (hf : SheafFamilyCover.JointlyLocallySurjective f)
    (hg : SheafFamilyCover.JointlyLocallySurjective g)
    (r : L → I) (p : Y ⟶ X) (b : ∀ j, D j ⟶ B (r j))
    (w : ∀ j, b j ≫ f (r j) = g j ≫ p)

/-- The independently associated local data commute with every covering refinement
and base change after effective gluing, naturally on all compatible arrows. -/
def associatedDataRefinement :
    Pseudofunctor.DescentData.pullFunctor (SheafTorsor.Stack.pseudofunctor G) w ⋙
      associatedDataFunctor a g ⋙ (SheafDisplayFamilyDescent.equivalence g hg).inverse ≅
    associatedDataFunctor a f ⋙ (SheafDisplayFamilyDescent.equivalence f hf).inverse ⋙
      SplitSheaf.restriction p := by
  have := ((SheafTorsor.Stack.pseudofunctor G).isStackFor_ofArrows_iff _).mp
    (SheafFamilyDescent.torsor_isStackFor G f hf)
  have := ((SheafTorsor.Stack.pseudofunctor G).isStackFor_ofArrows_iff _).mp
    (SheafFamilyDescent.torsor_isStackFor G g hg)
  exact Functor.isoWhiskerLeft _ (associatedDataRecovery a g hg) ≪≫
    Functor.isoWhiskerRight
      (SheafFamilyDescent.recoveryNaturality (SheafTorsor.Stack.pseudofunctor G) r p b w) (functor a Y) ≪≫
    Functor.isoWhiskerLeft (SheafFamilyDescent.torsorEquivalence G f hf).inverse (functorReindex a p) ≪≫
    Functor.isoWhiskerRight (associatedDataRecovery a f hf).symm (SplitSheaf.restriction p)

end FamilyRefinement

namespace Site
universe s
variable {C D : Type s} [Category.{s} C] [Category.{s} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
  [F.IsContinuous J K] [F.IsCocontinuous J K]
  {G : Sheaf K GrpCat.{s}} {M X : Sheaf K (Type s)}
  (P : SheafTorsor.Torsor G X) (a : SheafActionQuotient.Action G M)

/-- Site restriction carries every quotient representative to the same represented pair. -/
def pairs : InvariantMap (SheafSiteComparison.torsor J K F P)
    (SheafSiteComparison.action J K F a)
    (SheafSiteComparison.family J K F (associated P a)) where
  value x p m := classOf P a ((SheafSiteComparison.elements K F X).obj x) p m
  natural k p m := classOf_natural P a ((SheafSiteComparison.elements K F X).map k) p m
  invariant x g p m := classOf_diagonal P a ((SheafSiteComparison.elements K F X).obj x) g p m

/-- Association commutes with the chosen continuous, cocontinuous site restriction. -/
def comparison : associated (SheafSiteComparison.torsor J K F P)
    (SheafSiteComparison.action J K F a) ⟶
      SheafSiteComparison.family J K F (associated P a) := (pairs J K F P a).descend

@[simp] theorem comparison_classOf (x : (SheafSiteComparison.sheaf J K F X).obj.Elements)
    (p : (SheafSiteComparison.torsor J K F P).family.family.obj x)
    (m : (SheafSiteComparison.sheaf J K F M).obj.obj x.obj) :
    (comparison J K F P a).app x
      (classOf (SheafSiteComparison.torsor J K F P) (SheafSiteComparison.action J K F a) x p m) =
        classOf P a ((SheafSiteComparison.elements K F X).obj x) p m :=
  (pairs J K F P a).descend_classOf x p m

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_comparison (x : (SheafSiteComparison.sheaf J K F X).obj.Elements)
    (p : (SheafSiteComparison.torsor J K F P).family.family.obj x)
    (t : (associated (SheafSiteComparison.torsor J K F P)
      (SheafSiteComparison.action J K F a)).family.obj x) :
    evaluate P a ((SheafSiteComparison.elements K F X).obj x) p
      ((comparison J K F P a).app x t) =
        evaluate (SheafSiteComparison.torsor J K F P) (SheafSiteComparison.action J K F a) x p t := by
  conv_lhs => rw [← classOf_evaluate (SheafSiteComparison.torsor J K F P)
    (SheafSiteComparison.action J K F a) x p t]
  rw [comparison_classOf, evaluate_classOf]

set_option backward.isDefEq.respectTransparency false in
instance comparison_isIso : IsIso (comparison J K F P a) := by
  have hi : @IsIso ((SheafSiteComparison.sheaf J K F X).obj.Elements ⥤ Type s) _ _ _
      (comparison J K F P a) := by
    apply SplitSheafDescent.isIso_of_local_bijective (SheafSiteComparison.torsor J K F P).family
    intro x p
    constructor
    · intro t z h
      apply (evaluate (SheafSiteComparison.torsor J K F P) (SheafSiteComparison.action J K F a) x p).injective
      rw [← evaluate_comparison J K F P a x p t, ← evaluate_comparison J K F P a x p z, h]
    · intro t
      refine ⟨classOf (SheafSiteComparison.torsor J K F P) (SheafSiteComparison.action J K F a) x p
        (evaluate P a ((SheafSiteComparison.elements K F X).obj x) p t), ?_⟩
      rw [comparison_classOf, classOf_evaluate]
  let e := SplitSheaf.isoMk (asIso (show
    (associated (SheafSiteComparison.torsor J K F P) (SheafSiteComparison.action J K F a)).family ⟶
      (SheafSiteComparison.family J K F (associated P a)).family from comparison J K F P a))
  exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

def comparisonIso : associated (SheafSiteComparison.torsor J K F P)
    (SheafSiteComparison.action J K F a) ≅
      SheafSiteComparison.family J K F (associated P a) := asIso (comparison J K F P a)


variable {H : Sheaf K GrpCat.{s}} {N : Sheaf K (Type s)}
  {φ : G ⟶ H} {Q : SheafTorsor.Torsor H X} {b : SheafActionQuotient.Action H N}

/-- Restrict a semilinear map without replacing the structure homomorphism by an equivalence. -/
def semilinear (h : SheafTorsor.SemilinearMap φ P Q) :
    SheafTorsor.SemilinearMap ((SheafSiteComparison.groupRestriction J K F).map φ)
      (SheafSiteComparison.torsor J K F P) (SheafSiteComparison.torsor J K F Q) where
  hom := Functor.whiskerLeft (SheafSiteComparison.elements K F X) h.hom
  equivariant x := h.equivariant ((SheafSiteComparison.elements K F X).obj x)

def actionMap (h : ActionMap φ a b) :
    ActionMap ((SheafSiteComparison.groupRestriction J K F).map φ)
      (SheafSiteComparison.action J K F a) (SheafSiteComparison.action J K F b) where
  hom := SheafSiteComparison.map J K F h.hom
  equivariant x := h.equivariant (F.op.obj x)

set_option backward.isDefEq.respectTransparency false in
/-- Site comparison preserves every compatible torsor and fiber map. -/
theorem comparison_natural (h : SheafTorsor.SemilinearMap φ P Q) (k : ActionMap φ a b) :
    map (semilinear J K F P h) (actionMap J K F a k) ≫ comparison J K F Q b =
      comparison J K F P a ≫ Functor.whiskerLeft (SheafSiteComparison.elements K F X) (map h k) := by
  apply hom_ext
  intro x p m
  change (comparison J K F Q b).app x
    ((map (semilinear J K F P h) (actionMap J K F a k)).app x
      (classOf (SheafSiteComparison.torsor J K F P) (SheafSiteComparison.action J K F a) x p m)) =
    (map h k).app ((SheafSiteComparison.elements K F X).obj x)
      ((comparison J K F P a).app x
        (classOf (SheafSiteComparison.torsor J K F P) (SheafSiteComparison.action J K F a) x p m))
  rw [map_classOf, comparison_classOf, comparison_classOf, map_classOf]
  rfl

/-- A section restricts at every image stage. -/
def sectionRestriction {T : SplitSheaf.Ty X} (t : SplitSheaf.Tm T) :
    SplitSheaf.Tm (SheafSiteComparison.family J K F T) where
  val x := t.val ((SheafSiteComparison.elements K F X).obj x)
  natural k := t.natural ((SheafSiteComparison.elements K F X).map k)

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_comparison_inv (x : (SheafSiteComparison.sheaf J K F X).obj.Elements)
    (p : (SheafSiteComparison.torsor J K F P).family.family.obj x)
    (t : (SheafSiteComparison.family J K F (associated P a)).family.obj x) :
    evaluate (SheafSiteComparison.torsor J K F P) (SheafSiteComparison.action J K F a) x p
      ((comparisonIso J K F P a).inv.app x t) =
        evaluate P a ((SheafSiteComparison.elements K F X).obj x) p t := by
  have h := evaluate_comparison J K F P a x p ((comparisonIso J K F P a).inv.app x t)
  have e := congrArg (fun k => k.app x t) (comparisonIso J K F P a).inv_hom_id
  change (comparison J K F P a).app x ((comparisonIso J K F P a).inv.app x t) = t at e
  rw [e] at h
  exact h.symm

/-- The equivariant-target/section correspondence agrees with the chosen site comparison. -/
theorem objectSection_comparison (T : SheafActionQuotient.Object a X) :
    mapSection (comparisonIso J K F T.torsor a).inv
      (sectionRestriction J K F (objectSection T)) =
        objectSection (SheafSiteComparison.quotientObject J K F a T) := by
  apply section_ext
  intro x p
  change evaluate (SheafSiteComparison.torsor J K F T.torsor) (SheafSiteComparison.action J K F a) x p
    ((comparisonIso J K F T.torsor a).inv.app x
      ((sectionRestriction J K F (objectSection T)).val x)) = _
  rw [evaluate_comparison_inv]
  exact (objectSection_value T _ p).trans
    (objectSection_value (SheafSiteComparison.quotientObject J K F a T) x p).symm

end Site

end SquareKit.SheafAssociatedBundle
