import SquareKit.SheafStructureGroupExtension
import SquareKit.SheafTorsorCocycleClassification
import SquareKit.SheafTorsorCocycleRefinement

/-! Associated transition maps use inverse right-translation cocycle labels. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SheafAssociatedBundle
open CategoryTheory Opposite ElementFamilies
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Sheaf J GrpCat.{max u v}} {M : Sheaf J (Type (max u v))}
  {X : Sheaf J (Type (max u v))} {A : SplitSheaf.Ty X}
variable (a : SheafActionQuotient.Action G M) (c : SheafTorsor.Cocycle.Datum G A)

set_option backward.isDefEq.respectTransparency false in
/-- Right-translation torsor labels act inversely on associated coordinates. -/
def cocycleDatum : SplitSheafDescent.Datum A (SplitSheaf.constant M (SplitSheaf.extension A)) where
  transport x p q m := a.act x.obj (c.label x p q)⁻¹ m
  identity x p m := by rw [c.identity, inv_one, a.one_act]
  cocycle x p q r m := by rw [← a.mul_act, ← mul_inv_rev, c.cocycle]
  natural f p q m := by
    change M.obj.map f.hom (a.act _ _ m) = _
    rw [a.natural, (G.obj.map f.hom).hom.map_inv, c.natural]
    rfl

variable [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]

def cocycleEvaluation (x : X.obj.Elements) (p : A.family.obj x) :
    c.glue.obj.family.family.obj x ≃ G.obj.obj x.obj :=
  SheafTorsor.Descent.evaluationEquiv c.toDescent x p

/-- The distinguished local point is the inverse image of one in the actual glued torsor. -/
def cocyclePoint (x : X.obj.Elements) (p : A.family.obj x) : c.glue.obj.family.family.obj x :=
  (cocycleEvaluation c x p).symm 1

set_option backward.isDefEq.respectTransparency false in
theorem cocyclePoint_change (x : X.obj.Elements) (p q : A.family.obj x) :
    c.glue.obj.act x (c.label x p q)⁻¹ (cocyclePoint c x p) = cocyclePoint c x q := by
  apply (cocycleEvaluation c x q).injective
  have ht := SheafTorsor.Descent.evaluation_transport c.toDescent x p q (cocyclePoint c x p)
  change cocycleEvaluation c x p (cocyclePoint c x p) * c.label x p q =
    cocycleEvaluation c x q (cocyclePoint c x p) at ht
  have he := SheafTorsor.Descent.evaluation_equivariant c.toDescent
    (SheafTorsor.Descent.point A x q) (c.label x p q)⁻¹ (cocyclePoint c x p)
  change cocycleEvaluation c x q
    (c.glue.obj.act x (c.label x p q)⁻¹ (cocyclePoint c x p)) =
      (c.label x p q)⁻¹ * cocycleEvaluation c x q (cocyclePoint c x p) at he
  rw [he]
  change (c.label x p q)⁻¹ * _ =
    (cocycleEvaluation c x q)
      ((cocycleEvaluation c x q).symm 1)
  rw [Equiv.apply_symm_apply, ← ht]
  change (c.label x p q)⁻¹ *
    ((cocycleEvaluation c x p)
      ((cocycleEvaluation c x p).symm 1) * c.label x p q) = 1
  rw [Equiv.apply_symm_apply, one_mul, inv_mul_cancel]

theorem cocyclePoint_difference (x : X.obj.Elements) (p q : A.family.obj x) :
    SheafTorsor.fiberDifference c.glue.obj x (cocyclePoint c x p) (cocyclePoint c x q) =
      (c.label x p q)⁻¹ :=
  SheafTorsor.fiberDifference_eq _ _ _ _ _ (cocyclePoint_change c x p q)

/-- The constructed associated display has exactly the independently specified local transitions. -/
theorem cocycle_evaluate_change (x : X.obj.Elements) (p q : A.family.obj x)
    (s : (associated c.glue.obj a).family.obj x) :
    evaluate c.glue.obj a x (cocyclePoint c x q) s =
      a.act x.obj (c.label x p q)⁻¹ (evaluate c.glue.obj a x (cocyclePoint c x p) s) := by
  rw [evaluate_change c.glue.obj a x (cocyclePoint c x p), cocyclePoint_difference]

set_option backward.isDefEq.respectTransparency false in
theorem cocyclePoint_natural {x y : X.obj.Elements} (f : x ⟶ y) (p : A.family.obj x) :
    c.glue.obj.family.family.map f (cocyclePoint c x p) =
      cocyclePoint c y (A.family.map f p) := by
  have h := NatTrans.naturality_apply (SheafTorsor.Descent.comparison c.toDescent).iso.inv
    (SplitFunctionDiagram.pairArrow A.family f p) (1 : G.obj.obj x.obj)
  change (SheafTorsor.Descent.comparison c.toDescent).iso.inv.app
    (SheafTorsor.Descent.point A y (A.family.map f p)) (G.obj.map f.hom 1) =
      c.glue.obj.family.family.map f (cocyclePoint c x p) at h
  rw [(G.obj.map f.hom).hom.map_one] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- The local quotient representatives form a compatible map from the independent cocycle datum. -/
def cocycleDatumMap : SplitSheafDescent.Map (cocycleDatum a c)
    (SplitSheafDescent.canonicalDatum A (associated c.glue.obj a)) where
  hom := {
    app z := ↾fun m => classOf c.glue.obj a (X.obj.elementsMk z.obj z.val.1)
      (cocyclePoint c (X.obj.elementsMk z.obj z.val.1) z.val.2) m
    naturality {z w} f := by
      ext m
      rcases z with @⟨U,x,p⟩
      rcases w with @⟨V,y,q⟩
      rcases f with ⟨f,hf⟩
      change U ⟶ V at f
      have hx : X.obj.map f x = y := congrArg Sigma.fst hf
      subst y
      have hp : A.family.map (along X.obj f x) p = q :=
        eq_of_heq (Sigma.mk.inj_iff.mp hf).2
      subst q
      exact ((classOf_natural c.glue.obj a (along X.obj f x) (cocyclePoint c _ p) m).trans
        (congrArg (fun p => classOf c.glue.obj a _ p (M.obj.map f m))
          (cocyclePoint_natural c (along X.obj f x) p))).symm }
  transport x p q m := by
    change classOf c.glue.obj a x (cocyclePoint c x q)
      (a.act x.obj (c.label x p q)⁻¹ m) = classOf c.glue.obj a x (cocyclePoint c x p) m
    rw [← cocyclePoint_change c x p q]
    exact classOf_diagonal c.glue.obj a x _ _ m

/-- Independent inverse-label descent maps into the constructed associated display. -/
def cocycleRecoveryMap : SplitSheafDescent.family (cocycleDatum a c) ⟶ associated c.glue.obj a :=
  (cocycleDatumMap a c).descend ≫
    (SplitSheafDescent.canonicalRecovery A (associated c.glue.obj a)).inv

set_option backward.isDefEq.respectTransparency false in
theorem cocycleRecoveryMap_evaluate (x : X.obj.Elements) (p : A.family.obj x)
    (s : (SplitSheafDescent.family (cocycleDatum a c)).family.obj x) :
    evaluate c.glue.obj a x (cocyclePoint c x p) ((cocycleRecoveryMap a c).app x s) =
      SplitSheafDescent.evaluationEquiv (cocycleDatum a c) x p s := by
  let e := SplitSheafDescent.canonicalRecovery A (associated c.glue.obj a)
  have hh := congrArg (fun k => k.app x ((cocycleDatumMap a c).descend.app x s)) e.inv_hom_id
  have he := congrArg (SplitSheafDescent.evaluationEquiv
    (SplitSheafDescent.canonicalDatum A (associated c.glue.obj a)) x p) hh
  change SplitSheafDescent.evaluationEquiv
      (SplitSheafDescent.canonicalDatum A (associated c.glue.obj a)) x p
      ((SplitSheafDescent.canonicalFamilyMap A (associated c.glue.obj a)).app x
        (e.inv.app x ((cocycleDatumMap a c).descend.app x s))) =
    SplitSheafDescent.evaluationEquiv
      (SplitSheafDescent.canonicalDatum A (associated c.glue.obj a)) x p
      ((cocycleDatumMap a c).descend.app x s) at he
  rw [SplitSheafDescent.canonicalFamilyMap_evaluate, SplitSheafDescent.Map.evaluation] at he
  change (cocycleRecoveryMap a c).app x s =
    classOf c.glue.obj a x (cocyclePoint c x p)
      (SplitSheafDescent.evaluationEquiv (cocycleDatum a c) x p s) at he
  rw [he, evaluate_classOf]

set_option backward.isDefEq.respectTransparency false in
instance cocycleRecoveryMap_isIso : IsIso (cocycleRecoveryMap a c) := by
  have hi : @IsIso (X.obj.Elements ⥤ Type (max u v)) _ _ _ (cocycleRecoveryMap a c) := by
    apply SplitSheafDescent.isIso_of_local_bijective A
    intro x p
    constructor
    · intro s t h
      apply (SplitSheafDescent.evaluationEquiv (cocycleDatum a c) x p).injective
      rw [← cocycleRecoveryMap_evaluate a c x p s, ← cocycleRecoveryMap_evaluate a c x p t, h]
    · intro t
      refine ⟨(SplitSheafDescent.evaluationEquiv (cocycleDatum a c) x p).symm
        (evaluate c.glue.obj a x (cocyclePoint c x p) t), ?_⟩
      apply (evaluate c.glue.obj a x (cocyclePoint c x p)).injective
      rw [cocycleRecoveryMap_evaluate, Equiv.apply_symm_apply]
  let e := SplitSheaf.isoMk (asIso (show
    (SplitSheafDescent.family (cocycleDatum a c)).family ⟶ (associated c.glue.obj a).family
      from cocycleRecoveryMap a c))
  exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

/-- Association of the actual glued torsor equals descent of its independently specified
inverse-label action transitions, up to a constructed display isomorphism. -/
def cocycleComparison : associated c.glue.obj a ≅ SplitSheafDescent.family (cocycleDatum a c) :=
  (asIso (cocycleRecoveryMap a c)).symm

variable {c} {d : SheafTorsor.Cocycle.Datum G A}

set_option backward.isDefEq.respectTransparency false in
/-- Gauges act inversely on associated coordinates, preserving their actual maps. -/
def cocycleGaugeDatumMap (g : SheafTorsor.Cocycle.Gauge c d) :
    SplitSheafDescent.Map (cocycleDatum a c) (cocycleDatum a d) where
  hom := {
    app z := ↾fun m => a.act z.obj
      (SheafTorsor.Cocycle.labelValue g.label (X.obj.elementsMk z.obj z.val.1) z.val.2)⁻¹ m
    naturality {z w} f := by
      ext m
      have hn : G.obj.map f.hom
        (SheafTorsor.Cocycle.labelValue g.label (X.obj.elementsMk z.obj z.val.1) z.val.2) =
          SheafTorsor.Cocycle.labelValue g.label (X.obj.elementsMk w.obj w.val.1) w.val.2 :=
        (NatTrans.naturality_apply g.label.hom f.hom z.val).symm.trans
          (congrArg (g.label.hom.app w.obj) f.map_val)
      change a.act _ _ (M.obj.map f.hom m) = M.obj.map f.hom (a.act _ _ m)
      rw [a.natural, (G.obj.map f.hom).hom.map_inv, hn] }
  transport x p q m := by
    change a.act _ (SheafTorsor.Cocycle.labelValue g.label x q)⁻¹
      (a.act _ (c.label x p q)⁻¹ m) =
      a.act _ (d.label x p q)⁻¹ (a.act _ (SheafTorsor.Cocycle.labelValue g.label x p)⁻¹ m)
    rw [← a.mul_act, ← a.mul_act]
    apply congrArg (fun h => a.act x.obj h m)
    exact (mul_inv_rev _ _).symm.trans
      ((congrArg Inv.inv (g.compatible x p q)).trans (mul_inv_rev _ _))

set_option backward.isDefEq.respectTransparency false in
theorem cocyclePoint_gauge (g : SheafTorsor.Cocycle.Gauge c d)
    (x : X.obj.Elements) (p : A.family.obj x) :
    g.glue.hom.iso.hom.app x (cocyclePoint c x p) =
      d.glue.obj.act x (SheafTorsor.Cocycle.labelValue g.label x p) (cocyclePoint d x p) := by
  apply (cocycleEvaluation d x p).injective
  have hg := g.toDescentMap.evaluation x p (cocyclePoint c x p)
  change cocycleEvaluation d x p (g.glue.hom.iso.hom.app x (cocyclePoint c x p)) =
    cocycleEvaluation c x p (cocyclePoint c x p) * SheafTorsor.Cocycle.labelValue g.label x p at hg
  have he := SheafTorsor.Descent.evaluation_equivariant d.toDescent
    (SheafTorsor.Descent.point A x p) (SheafTorsor.Cocycle.labelValue g.label x p) (cocyclePoint d x p)
  change cocycleEvaluation d x p (d.glue.obj.act x _ (cocyclePoint d x p)) =
    SheafTorsor.Cocycle.labelValue g.label x p * cocycleEvaluation d x p (cocyclePoint d x p) at he
  rw [hg, he]
  change (cocycleEvaluation c x p) ((cocycleEvaluation c x p).symm 1) * _ =
    _ * (cocycleEvaluation d x p) ((cocycleEvaluation d x p).symm 1)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, one_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- The gauge map on the constructed associated object has the expected inverse-label formula. -/
theorem cocycle_gauge_value (g : SheafTorsor.Cocycle.Gauge c d)
    (x : X.obj.Elements) (p : A.family.obj x) (m : M.obj.obj x.obj) :
    evaluate d.glue.obj a x (cocyclePoint d x p)
      (((functor a X).map g.glue.hom).app x (classOf c.glue.obj a x (cocyclePoint c x p) m)) =
      a.act x.obj (SheafTorsor.Cocycle.labelValue g.label x p)⁻¹ m := by
  rw [functor_map_classOf, cocyclePoint_gauge]
  rw [evaluate_change d.glue.obj a x
    (d.glue.obj.act x (SheafTorsor.Cocycle.labelValue g.label x p) (cocyclePoint d x p)),
    evaluate_classOf, SheafTorsor.fiberDifference_act_left, SheafTorsor.fiberDifference_self, one_mul]

set_option backward.isDefEq.respectTransparency false in
theorem cocycleComparison_hom_evaluate (x : X.obj.Elements) (p : A.family.obj x)
    (s : (associated c.glue.obj a).family.obj x) :
    SplitSheafDescent.evaluationEquiv (cocycleDatum a c) x p
      ((cocycleComparison a c).hom.app x s) = evaluate c.glue.obj a x (cocyclePoint c x p) s := by
  rw [← cocycleRecoveryMap_evaluate]
  have h := congrArg (fun k => k.app x s) (cocycleComparison a c).hom_inv_id
  exact congrArg (evaluate c.glue.obj a x (cocyclePoint c x p)) h

omit [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] in
/-- Maps into independent cocycle descent are determined on all restricted local evaluations. -/
theorem cocycle_hom_ext {T : SplitSheaf.Ty X}
    (f g : T ⟶ SplitSheafDescent.family (cocycleDatum a c))
    (h : ∀ x p s, SplitSheafDescent.evaluationEquiv (cocycleDatum a c) x p (f.app x s) =
      SplitSheafDescent.evaluationEquiv (cocycleDatum a c) x p (g.app x s)) : f = g := by
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply SplitSheafDescent.value_ext
  intro y k p
  change SplitSheafDescent.evaluationEquiv (cocycleDatum a c) y p
    ((SplitSheafDescent.family (cocycleDatum a c)).family.map k (f.app x s)) =
    SplitSheafDescent.evaluationEquiv (cocycleDatum a c) y p
      ((SplitSheafDescent.family (cocycleDatum a c)).family.map k (g.app x s))
  exact (congrArg (SplitSheafDescent.evaluationEquiv (cocycleDatum a c) y p)
    (NatTrans.naturality_apply f k s)).symm.trans
    ((h y p (T.family.map k s)).trans
      (congrArg (SplitSheafDescent.evaluationEquiv (cocycleDatum a c) y p)
        (NatTrans.naturality_apply g k s)))

set_option backward.isDefEq.respectTransparency false in
/-- The comparison preserves the independently constructed gauge map, not only its objects. -/
theorem cocycleComparison_natural (g : SheafTorsor.Cocycle.Gauge c d) :
    (functor a X).map g.glue.hom ≫ (cocycleComparison a d).hom =
      (cocycleComparison a c).hom ≫ (cocycleGaugeDatumMap a g).descend := by
  apply cocycle_hom_ext
  intro x p s
  change SplitSheafDescent.evaluationEquiv (cocycleDatum a d) x p
      ((cocycleComparison a d).hom.app x (((functor a X).map g.glue.hom).app x s)) =
    SplitSheafDescent.evaluationEquiv (cocycleDatum a d) x p
      ((cocycleGaugeDatumMap a g).descend.app x ((cocycleComparison a c).hom.app x s))
  rw [cocycleComparison_hom_evaluate, SplitSheafDescent.Map.evaluation]
  change evaluate d.glue.obj a x (cocyclePoint d x p) (((functor a X).map g.glue.hom).app x s) =
    a.act x.obj (SheafTorsor.Cocycle.labelValue g.label x p)⁻¹
      (SplitSheafDescent.evaluationEquiv (cocycleDatum a c) x p ((cocycleComparison a c).hom.app x s))
  rw [cocycleComparison_hom_evaluate]
  conv_lhs => rw [← classOf_evaluate c.glue.obj a x (cocyclePoint c x p) s]
  exact cocycle_gauge_value a g x p _

section Refinement
variable (c)
variable {Y Z : Sheaf J (Type (max u v))} {B : SplitSheaf.Ty Y} {D : SplitSheaf.Ty Z}
  {f : Y ⟶ X} {g : Z ⟶ Y} (r : SheafTorsor.Cocycle.CoverMap f A B)
  [Presheaf.IsLocallySurjective J (SplitSheaf.p B).hom]

/-- Associated gluing commutes with actual refinement and base change. -/
def cocycleRefinementComparison : associated (r.pull c).glue.obj a ≅
    SplitSheaf.tySub (associated c.glue.obj a) f :=
  (functor a Y).mapIso (r.comparison c).toIso ≪≫ (reindexIso c.glue.obj a f).symm

set_option backward.isDefEq.respectTransparency false in
theorem cocyclePoint_refinement (x : Y.obj.Elements) (p : B.family.obj x) :
    (r.comparison c).iso.hom.app x (cocyclePoint (r.pull c) x p) =
      cocyclePoint c (f.hom.mapElements.obj x) (r.app x p) := by
  apply (cocycleEvaluation c (f.hom.mapElements.obj x) (r.app x p)).injective
  rw [show cocycleEvaluation c (f.hom.mapElements.obj x) (r.app x p)
    ((r.comparison c).iso.hom.app x (cocyclePoint (r.pull c) x p)) =
      cocycleEvaluation (r.pull c) x p (cocyclePoint (r.pull c) x p) from
        r.comparison_evaluation c x p _]
  exact (cocycleEvaluation (r.pull c) x p).apply_symm_apply 1 |>.trans
    ((cocycleEvaluation c (f.hom.mapElements.obj x) (r.app x p)).apply_symm_apply 1).symm

set_option backward.isDefEq.respectTransparency false in
theorem cocycleRefinementComparison_evaluate (x : Y.obj.Elements) (p : B.family.obj x)
    (s : (associated (r.pull c).glue.obj a).family.obj x) :
    evaluate c.glue.obj a (f.hom.mapElements.obj x) (cocyclePoint c _ (r.app x p))
      ((cocycleRefinementComparison a c r).hom.app x s) =
      evaluate (r.pull c).glue.obj a x (cocyclePoint (r.pull c) x p) s := by
  change evaluate c.glue.obj a _ _ ((reindexMap c.glue.obj a f).app x
    (((functor a Y).map (r.comparison c)).app x s)) = _
  rw [evaluate_reindexMap]
  rw [← cocyclePoint_refinement c r x p]
  exact evaluate_map (SheafTorsor.SemilinearMap.ofArrow (r.comparison c))
    (ActionMap.ident a) x (cocyclePoint (r.pull c) x p) s

set_option backward.isDefEq.respectTransparency false in
theorem cocycleRefinementComparison_ident :
    cocycleRefinementComparison a c (SheafTorsor.Cocycle.CoverMap.ident A) = Iso.refl _ := by
  apply Iso.ext
  change (functor a X).map ((SheafTorsor.Cocycle.CoverMap.ident A).comparison c) ≫
    reindexMap c.glue.obj a (𝟙 X) = 𝟙 _
  rw [SheafTorsor.Cocycle.CoverMap.comparison_ident, reindexMap_id]
  exact (functor a X).map_id c.glue.obj

variable [Presheaf.IsLocallySurjective J (SplitSheaf.p D).hom]
set_option backward.isDefEq.respectTransparency false in
/-- Two changes of cover give the same comparison as their composite. -/
theorem cocycleRefinementComparison_comp (s : SheafTorsor.Cocycle.CoverMap g B D) :
    (cocycleRefinementComparison a c (r.comp s)).hom =
      (cocycleRefinementComparison a (r.pull c) s).hom ≫
        (SplitSheaf.restriction g).map (cocycleRefinementComparison a c r).hom := by
  change (functor a Z).map ((r.comp s).comparison c) ≫ reindexMap c.glue.obj a (g ≫ f) =
    ((functor a Z).map (s.comparison (r.pull c)) ≫ reindexMap (r.pull c).glue.obj a g) ≫
      (SplitSheaf.restriction g).map ((functor a Y).map (r.comparison c) ≫ reindexMap c.glue.obj a f)
  rw [SheafTorsor.Cocycle.CoverMap.comparison_comp]
  change (functor a Z).map (s.comparison (r.pull c) ≫ (r.comparison c).reindex g) ≫ _ = _
  rw [Functor.map_comp, reindexMap_comp, Functor.map_comp]
  simp only [Category.assoc]
  have hn : (functor a Z).map ((r.comparison c).reindex g) ≫
      reindexMap (SheafTorsor.reindex c.glue.obj f) a g =
      reindexMap (r.pull c).glue.obj a g ≫ (SplitSheaf.restriction g).map
        ((functor a Y).map (r.comparison c)) :=
    reindexMap_map (r.pull c).glue.obj a g
      (SheafTorsor.SemilinearMap.ofArrow (r.comparison c)) (ActionMap.ident a)
  rw [← Category.assoc ((functor a Z).map ((r.comparison c).reindex g)), hn]
  simp only [Category.assoc]

end Refinement

section GroupChange
variable {H : Sheaf J GrpCat.{max u v}} (φ : G ⟶ H) (c)

/-- Apply an arbitrary group homomorphism to the independently supplied labels. -/
def mappedCocycle (φ : G ⟶ H) (c : SheafTorsor.Cocycle.Datum G A) : SheafTorsor.Cocycle.Datum H A where
  label x p q := φ.hom.app x.obj (c.label x p q)
  identity x p := (congrArg (φ.hom.app x.obj) (c.identity x p)).trans (φ.hom.app x.obj).hom.map_one
  cocycle x p q r := ((φ.hom.app x.obj).hom.map_mul _ _).symm.trans
    (congrArg (φ.hom.app x.obj) (c.cocycle x p q r))
  natural f p q := (congrArg (fun t => t (c.label _ p q)) (φ.hom.naturality f.hom)).symm.trans
    (congrArg (φ.hom.app _) (c.natural f p q))

variable {c} in
set_option backward.isDefEq.respectTransparency false in
/-- Gauge labels change by the same homomorphism, retaining every input arrow. -/
def mappedGauge (φ : G ⟶ H) {d : SheafTorsor.Cocycle.Datum G A} (g : SheafTorsor.Cocycle.Gauge c d) :
    SheafTorsor.Cocycle.Gauge (mappedCocycle φ c) (mappedCocycle φ d) where
  label := g.label ≫ (sheafCompose J (forget GrpCat)).map φ
  compatible x p q := by
    change φ.hom.app x.obj (c.label x p q) * φ.hom.app x.obj _ =
      φ.hom.app x.obj _ * φ.hom.app x.obj (d.label x p q)
    rw [← (φ.hom.app x.obj).hom.map_mul, ← (φ.hom.app x.obj).hom.map_mul]
    exact congrArg (φ.hom.app x.obj) (g.compatible x p q)

private theorem datum_transport_ext {A : SplitSheaf.Ty X}
    {T : SplitSheaf.Ty (SplitSheaf.extension A)} {d e : SplitSheafDescent.Datum A T}
    (h : d.transport = e.transport) : d = e := by
  cases d
  cases e
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] in
/-- The extension transition is exactly right translation by the changed cocycle label. -/
theorem cocycleDatum_eq_toDisplayDatum (φ : G ⟶ H) (c : SheafTorsor.Cocycle.Datum G A) :
    cocycleDatum (SheafStructureGroupExtension.rightInverseAction φ) c =
      (mappedCocycle φ c).toDescent.toDisplayDatum := by
  apply datum_transport_ext
  funext x p q h
  change (show H.obj.obj x.obj from h) * (φ.hom.app x.obj (c.label x p q)⁻¹)⁻¹ =
    (show H.obj.obj x.obj from h) * φ.hom.app x.obj (c.label x p q)
  rw [(φ.hom.app x.obj).hom.map_inv, inv_inv]

private theorem evaluate_eqToIso {A : SplitSheaf.Ty X}
    {T : SplitSheaf.Ty (SplitSheaf.extension A)} {d e : SplitSheafDescent.Datum A T}
    (h : d = e) (x : X.obj.Elements) (p : A.family.obj x)
    (s : (SplitSheafDescent.family d).family.obj x) :
    SplitSheafDescent.evaluationEquiv e x p
      ((eqToIso (congrArg SplitSheafDescent.family h)).hom.app x s) =
      SplitSheafDescent.evaluationEquiv d x p s := by cases h; rfl

/-- An actual display isomorphism to gluing the independently changed labels. -/
def cocycleExtensionFamily (φ : G ⟶ H) (c : SheafTorsor.Cocycle.Datum G A) : (SheafStructureGroupExtension.extension φ c.glue.obj).family ≅
    (mappedCocycle φ c).glue.obj.family :=
  cocycleComparison (SheafStructureGroupExtension.rightInverseAction φ) c ≪≫
    eqToIso (congrArg SplitSheafDescent.family (cocycleDatum_eq_toDisplayDatum φ c))

set_option backward.isDefEq.respectTransparency false in
theorem cocycleExtensionFamily_evaluate (φ : G ⟶ H) (c : SheafTorsor.Cocycle.Datum G A) (x : X.obj.Elements) (p : A.family.obj x)
    (s : (SheafStructureGroupExtension.extension φ c.glue.obj).family.family.obj x) :
    cocycleEvaluation (mappedCocycle φ c) x p ((cocycleExtensionFamily φ c).hom.app x s) =
      evaluate c.glue.obj (SheafStructureGroupExtension.rightInverseAction φ) x (cocyclePoint c x p) s := by
  change SplitSheafDescent.evaluationEquiv (mappedCocycle φ c).toDescent.toDisplayDatum x p
    ((eqToIso (congrArg SplitSheafDescent.family (cocycleDatum_eq_toDisplayDatum φ c))).hom.app x
      ((cocycleComparison (SheafStructureGroupExtension.rightInverseAction φ) c).hom.app x s)) = _
  exact (evaluate_eqToIso (cocycleDatum_eq_toDisplayDatum φ c) x p _).trans
    (cocycleComparison_hom_evaluate (SheafStructureGroupExtension.rightInverseAction φ) x p s)

set_option backward.isDefEq.respectTransparency false in
/-- Extension of a glued torsor is the torsor glued from the homomorphism-applied labels. -/
def cocycleExtensionComparison (φ : G ⟶ H) (c : SheafTorsor.Cocycle.Datum G A) : SheafTorsor.Arrow
    (SheafStructureGroupExtension.extension φ c.glue.obj) (mappedCocycle φ c).glue.obj :=
  SheafTorsor.EquivariantMap.toArrow {
    hom := (cocycleExtensionFamily φ c).hom
    equivariant := SheafStructureGroupExtension.equivariant_of_cover (A := A)
      (R := SheafStructureGroupExtension.extension φ c.glue.obj) (S := (mappedCocycle φ c).glue.obj)
      (σ := 𝟙 H) (cocycleExtensionFamily φ c).hom (by
        intro x p h s
        apply (cocycleEvaluation (mappedCocycle φ c) x p).injective
        change cocycleEvaluation (mappedCocycle φ c) x p ((cocycleExtensionFamily φ c).hom.app x
          ((SheafStructureGroupExtension.extension φ c.glue.obj).act x h s)) =
          cocycleEvaluation (mappedCocycle φ c) x p ((mappedCocycle φ c).glue.obj.act x h
            ((cocycleExtensionFamily φ c).hom.app x s))
        rw [cocycleExtensionFamily_evaluate, SheafStructureGroupExtension.evaluate_act]
        exact (congrArg (h * ·) (cocycleExtensionFamily_evaluate φ c x p s)).symm.trans
          (SheafTorsor.Descent.evaluation_equivariant (mappedCocycle φ c).toDescent
            (SheafTorsor.Descent.point A x p) h ((cocycleExtensionFamily φ c).hom.app x s)).symm) }


omit [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] in
theorem mappedCocycle_id (c : SheafTorsor.Cocycle.Datum G A) : mappedCocycle (𝟙 G) c = c := rfl

omit [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] in
theorem mappedCocycle_comp {L : Sheaf J GrpCat.{max u v}} (ψ : H ⟶ L)
    (c : SheafTorsor.Cocycle.Datum G A) :
    mappedCocycle (φ ≫ ψ) c = mappedCocycle ψ (mappedCocycle φ c) := rfl

omit [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] in
theorem mappedCocycle_pull {Y : Sheaf J (Type (max u v))} {B : SplitSheaf.Ty Y}
    {f : Y ⟶ X} (r : SheafTorsor.Cocycle.CoverMap f A B)
    (c : SheafTorsor.Cocycle.Datum G A) :
    mappedCocycle φ (r.pull c) = r.pull (mappedCocycle φ c) := rfl

omit [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] in
theorem mappedGauge_id (c : SheafTorsor.Cocycle.Datum G A) :
    mappedGauge φ (SheafTorsor.Cocycle.Gauge.ident c) =
      SheafTorsor.Cocycle.Gauge.ident (mappedCocycle φ c) := by
  apply SheafTorsor.Cocycle.Gauge.ext
  ext x p
  exact (φ.hom.app x).hom.map_one

omit [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] in
theorem mappedGauge_comp {c d e : SheafTorsor.Cocycle.Datum G A}
    (g : SheafTorsor.Cocycle.Gauge c d) (h : SheafTorsor.Cocycle.Gauge d e) :
    mappedGauge φ (g.comp h) = (mappedGauge φ g).comp (mappedGauge φ h) := by
  apply SheafTorsor.Cocycle.Gauge.ext
  ext x p
  exact (φ.hom.app x).hom.map_mul _ _

set_option backward.isDefEq.respectTransparency false in
/-- Maps into a glued cocycle torsor are determined in every local coordinate. -/
theorem cocycleEvaluation_hom_ext (e : SheafTorsor.Cocycle.Datum H A) {T : SplitSheaf.Ty X}
    (f g : T ⟶ e.glue.obj.family)
    (h : ∀ (x : X.obj.Elements) (p : A.family.obj x) (s : T.family.obj x),
      cocycleEvaluation e x p (f.app x s) = cocycleEvaluation e x p (g.app x s)) : f = g := by
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply SplitSheafDescent.value_ext
  intro y k p
  change cocycleEvaluation e y p (e.glue.obj.family.family.map k (f.app x s)) =
    cocycleEvaluation e y p (e.glue.obj.family.family.map k (g.app x s))
  exact (congrArg (cocycleEvaluation e y p) (NatTrans.naturality_apply f k s)).symm.trans
    ((h y p (T.family.map k s)).trans
      (congrArg (cocycleEvaluation e y p) (NatTrans.naturality_apply g k s)))

set_option backward.isDefEq.respectTransparency false in
/-- The group-change comparison retains every gauge, with its homomorphism-applied label. -/
theorem cocycleExtensionComparison_natural {c d : SheafTorsor.Cocycle.Datum G A}
    (g : SheafTorsor.Cocycle.Gauge c d) :
    SheafStructureGroupExtension.extensionMap φ g.glue.hom ≫ cocycleExtensionComparison φ d =
      cocycleExtensionComparison φ c ≫ (mappedGauge φ g).glue.hom := by
  apply SheafTorsor.Arrow.ext
  apply cocycleEvaluation_hom_ext (mappedCocycle φ d)
  intro y p s
  change cocycleEvaluation (mappedCocycle φ d) y p
      ((cocycleExtensionFamily φ d).hom.app y
        ((SheafStructureGroupExtension.extensionMap φ g.glue.hom).iso.hom.app y s)) =
    cocycleEvaluation (mappedCocycle φ d) y p
      ((mappedGauge φ g).glue.hom.iso.hom.app y ((cocycleExtensionFamily φ c).hom.app y s))
  rw [cocycleExtensionFamily_evaluate, SheafStructureGroupExtension.extensionMap_underlying]
  have hg := (mappedGauge φ g).toDescentMap.evaluation y p ((cocycleExtensionFamily φ c).hom.app y s)
  change cocycleEvaluation (mappedCocycle φ d) y p
    ((mappedGauge φ g).glue.hom.iso.hom.app y ((cocycleExtensionFamily φ c).hom.app y s)) =
    cocycleEvaluation (mappedCocycle φ c) y p ((cocycleExtensionFamily φ c).hom.app y s) *
      φ.hom.app y.obj (SheafTorsor.Cocycle.labelValue g.label y p) at hg
  rw [hg, cocycleExtensionFamily_evaluate]
  conv_lhs => rw [← classOf_evaluate c.glue.obj (SheafStructureGroupExtension.rightInverseAction φ)
    y (cocyclePoint c y p) s]
  exact (cocycle_gauge_value (SheafStructureGroupExtension.rightInverseAction φ) g y p _).trans (by
    change _ * (φ.hom.app y.obj (SheafTorsor.Cocycle.labelValue g.label y p)⁻¹)⁻¹ = _
    rw [(φ.hom.app y.obj).hom.map_inv, inv_inv])

end GroupChange

end SquareKit.SheafAssociatedBundle
