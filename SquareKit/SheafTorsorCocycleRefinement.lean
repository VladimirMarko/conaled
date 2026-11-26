import SquareKit.SheafTorsorCocycleClassification

/-! Refinement and base change act on primitive cocycles and every gauge. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafTorsor.Cocycle
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{w}} {X Y Z : Sheaf J (Type w)}
variable {A : SplitSheaf.Ty X} {B : SplitSheaf.Ty Y} {D : SplitSheaf.Ty Z}

/-- A map of covers over a base map is a natural map on their fibers. -/
abbrev CoverMap (f : Y ⟶ X) (A : SplitSheaf.Ty X) (B : SplitSheaf.Ty Y) :=
  B.family ⟶ (SplitSheaf.tySub A f).family

namespace CoverMap
variable {f : Y ⟶ X}

def total (r : CoverMap f A B) : SplitSheaf.extension B ⟶ SplitSheaf.extension A :=
  SplitSheaf.pair A (SplitSheaf.p B ≫ f) {
    val x := r.app (Y.obj.elementsMk x.obj x.val.1) x.val.2
    natural {x y} k := by
      have h := NatTrans.naturality_apply r ((SplitSheaf.p B).hom.mapElements.map k) x.val.2
      exact h.symm.trans (congrArg (r.app _) ((SplitSheaf.q B).natural k)) }

@[simp] theorem total_projection (r : CoverMap f A B) :
    r.total ≫ SplitSheaf.p A = SplitSheaf.p B ≫ f := rfl

def ident (A : SplitSheaf.Ty X) : CoverMap (𝟙 X) A A := 𝟙 A.family

def comp (r : CoverMap f A B) {g : Z ⟶ Y} (s : CoverMap g B D) : CoverMap (g ≫ f) A D :=
  s ≫ Functor.whiskerLeft g.hom.mapElements r

def pull (r : CoverMap f A B) (c : Datum G A) : Datum G B where
  label x a b := c.label (f.hom.mapElements.obj x) (r.app x a) (r.app x b)
  identity x a := c.identity _ _
  cocycle x a b k := c.cocycle _ _ _ _
  natural k a b := by
    exact (c.natural (f.hom.mapElements.map k) (r.app _ a) (r.app _ b)).trans
      (congrArg₂ (c.label (f.hom.mapElements.obj _))
        (NatTrans.naturality_apply r k a).symm (NatTrans.naturality_apply r k b).symm)

def pullGauge (r : CoverMap f A B) {c d : Datum G A} (g : Gauge c d) : Gauge (r.pull c) (r.pull d) where
  label := r.total ≫ g.label
  compatible _ _ _ := g.compatible _ _ _

def pullFunctor (r : CoverMap f A B) : Datum G A ⥤ Datum G B where
  obj := r.pull
  map := r.pullGauge
  map_id _ := Gauge.ext _ _ rfl
  map_comp _ _ := Gauge.ext _ _ rfl

@[simp] theorem pull_ident (c : Datum G A) : (ident A).pull c = c := rfl
@[simp] theorem pull_comp (r : CoverMap f A B) {g : Z ⟶ Y} (s : CoverMap g B D) (c : Datum G A) :
    (r.comp s).pull c = s.pull (r.pull c) := rfl
@[simp] theorem pullGauge_ident {c d : Datum G A} (g : Gauge c d) : (ident A).pullGauge g = g := rfl
@[simp] theorem pullGauge_comp (r : CoverMap f A B) {g : Z ⟶ Y} (s : CoverMap g B D)
    {c d : Datum G A} (h : Gauge c d) : (r.comp s).pullGauge h = s.pullGauge (r.pullGauge h) := rfl

/-- Substitution is the cartesian map from the pulled-back cover. -/
def baseChange (A : SplitSheaf.Ty X) (f : Y ⟶ X) : CoverMap f A (SplitSheaf.tySub A f) := 𝟙 _

/-- An ordinary commuting square induces the fiber map of its split displays. -/
def ofSquare {U V : Sheaf J (Type w)} (p : U ⟶ X) (q : V ⟶ Y)
    (top : V ⟶ U) (comm : top ≫ p = q ≫ f) :
    CoverMap f (SplitSheaf.ofDisplay p) (SplitSheaf.ofDisplay q) where
  app x := ↾fun b => ⟨top.hom.app x.obj b.val, by
    have h := congrArg (fun k => k.hom.app x.obj b.val) comm
    exact h.trans (congrArg (f.hom.app x.obj) b.property)⟩
  naturality {x y} k := by
    ext b
    apply Subtype.ext
    exact NatTrans.naturality_apply top.hom k.hom b.val

end CoverMap

section Effective
variable {G : Sheaf J GrpCat.{max u v}} {X Y Z : Sheaf J (Type (max u v))}
variable {A : SplitSheaf.Ty X} {B : SplitSheaf.Ty Y} {D : SplitSheaf.Ty Z}
variable {f : Y ⟶ X} (r : CoverMap f A B)
variable [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
variable [Presheaf.IsLocallySurjective J (SplitSheaf.p B).hom]

/-- The comparison over the original cover restricts along any map of covers. -/
def CoverMap.localTrivialization (c : Datum G A) :
    Arrow (SheafTorsor.trivial G (SplitSheaf.extension B))
      (reindex (reindex c.glue.obj f) (SplitSheaf.p B)) :=
  (Descent.comparison c.toDescent).inverse.reindex r.total

omit [Presheaf.IsLocallySurjective J (SplitSheaf.p B).hom] in
theorem CoverMap.chosen_pull (c : Datum G A) :
    chosenCocycle (reindex c.glue.obj f) (r.localTrivialization c) = r.pull c := by
  apply Datum.ext
  intro x a b
  change Descent.evaluationEquiv c.toDescent (f.hom.mapElements.obj x) (r.app x b)
    ((Descent.evaluationEquiv c.toDescent (f.hom.mapElements.obj x) (r.app x a)).symm (1 : G.obj.obj x.obj)) = _
  rw [← Descent.evaluation_transport]
  change (show G.obj.obj x.obj from Descent.evaluationEquiv c.toDescent
    (f.hom.mapElements.obj x) (r.app x a)
    ((Descent.evaluationEquiv c.toDescent (f.hom.mapElements.obj x) (r.app x a)).symm (1 : G.obj.obj x.obj))) *
      (show G.obj.obj x.obj from c.label (f.hom.mapElements.obj x) (r.app x a) (r.app x b)) = _
  rw [Equiv.apply_symm_apply]
  exact one_mul _

/-- Gluing the pulled cocycle recovers the actual reindexed torsor. -/
def CoverMap.comparison (c : Datum G A) : Arrow (r.pull c).glue.obj (reindex c.glue.obj f) :=
  (show Arrow (r.pull c).glue.obj
    (chosenCocycle (reindex c.glue.obj f) (r.localTrivialization c)).glue.obj from
      eqToHom (congrArg (fun d : Datum G B => d.glue.obj) (r.chosen_pull c).symm)).comp
        (chosenRecovery (reindex c.glue.obj f) (r.localTrivialization c))

private theorem cocycle_comparison_eqToHom {c d : Datum G B} (h : c = d) :
    ((show Arrow c.glue.obj d.glue.obj from
      eqToHom (congrArg (fun e : Datum G B => e.glue.obj) h)).reindex (SplitSheaf.p B)).comp
        (Descent.comparison d.toDescent) = Descent.comparison c.toDescent := by
  cases h
  rfl

/-- The gluing comparison recovers its local map exactly. -/
theorem CoverMap.comparison_reindex (c : Datum G A) :
    (r.comparison c).reindex (SplitSheaf.p B) =
      (Descent.comparison (r.pull c).toDescent).comp (r.localTrivialization c) := by
  change ((show Arrow (r.pull c).glue.obj
    (chosenCocycle (reindex c.glue.obj f) (r.localTrivialization c)).glue.obj from
      eqToHom (congrArg (fun d : Datum G B => d.glue.obj) (r.chosen_pull c).symm)).reindex _).comp
        ((chosenRecovery (reindex c.glue.obj f) (r.localTrivialization c)).reindex _) = _
  rw [chosenRecovery_reindex]
  exact congrArg (fun k => k.comp (r.localTrivialization c))
    (cocycle_comparison_eqToHom (r.chosen_pull c).symm)

/-- Evaluating after the comparison agrees with evaluation on the refined cover. -/
theorem CoverMap.comparison_evaluation (c : Datum G A) (x : Y.obj.Elements)
    (b : B.family.obj x) (t : (r.pull c).glue.obj.family.family.obj x) :
    Descent.evaluationEquiv c.toDescent (f.hom.mapElements.obj x) (r.app x b)
      ((r.comparison c).iso.hom.app x t) =
        Descent.evaluationEquiv (r.pull c).toDescent x b t := by
  have h := congrArg (fun k => k.iso.hom.app (Descent.point B x b) t) (r.comparison_reindex c)
  change (r.comparison c).iso.hom.app x t =
    (Descent.evaluationEquiv c.toDescent (f.hom.mapElements.obj x) (r.app x b)).symm
      (Descent.evaluationEquiv (r.pull c).toDescent x b t) at h
  rw [h, Equiv.apply_symm_apply]

/-- Every gauge is respected by the gluing/base-change comparison. -/
theorem CoverMap.comparison_natural {c d : Datum G A} (g : Gauge c d) :
    ((r.pullGauge g).glue.hom).comp (r.comparison d) =
      (r.comparison c).comp (g.glue.hom.reindex f) := by
  apply Descent.reindex_injective (B := B)
  apply Arrow.ext
  ext x t
  let y := Y.obj.elementsMk x.obj x.val.1
  let b : B.family.obj y := x.val.2
  apply (Descent.evaluationEquiv d.toDescent (f.hom.mapElements.obj y) (r.app y b)).injective
  change Descent.evaluationEquiv d.toDescent (f.hom.mapElements.obj y) (r.app y b)
    ((r.comparison d).iso.hom.app y (((r.pullGauge g).glue.hom).iso.hom.app y t)) =
      Descent.evaluationEquiv d.toDescent (f.hom.mapElements.obj y) (r.app y b)
        (g.glue.hom.iso.hom.app (f.hom.mapElements.obj y) ((r.comparison c).iso.hom.app y t))
  rw [r.comparison_evaluation]
  exact ((r.pullGauge g).toDescentMap.evaluation y b t).trans
    ((congrArg (fun z => g.toDescentMap.hom.app
      (Descent.point A (f.hom.mapElements.obj y) (r.app y b)) z)
        (r.comparison_evaluation c y b t).symm).trans
          (g.toDescentMap.evaluation _ _ _).symm)

theorem CoverMap.comparison_ident (c : Datum G A) :
    (CoverMap.ident A).comparison c = Arrow.ident c.glue.obj := by
  apply Descent.reindex_injective (B := A)
  apply Arrow.ext
  ext x t
  apply (Descent.evaluationEquiv c.toDescent
    (X.obj.elementsMk x.obj x.val.1) x.val.2).injective
  exact (CoverMap.ident A).comparison_evaluation c _ _ t

/-- The full admitted subcategory restricts along a map of covers. -/
def CoverMap.admittedRestriction : Admitted (G := G) A ⥤ Admitted (G := G) B where
  obj P := ⟨reindex P.obj f, ⟨P.property.some.reindex r.total⟩⟩
  map h := ⟨h.hom.reindex f⟩

/-- The categorical classification commutes with every map of covers. -/
def CoverMap.comparisonNatIso :
    r.pullFunctor ⋙ glueFunctor ≅ glueFunctor ⋙ r.admittedRestriction (G := G) :=
  NatIso.ofComponents (fun c => (Admits (G := G) B).isoMk (r.comparison c).toIso) (by
    intro c d g
    apply ObjectProperty.hom_ext
    exact r.comparison_natural g)

variable [Presheaf.IsLocallySurjective J (SplitSheaf.p D).hom]

/-- Successive refinements/base changes agree on the comparison itself. -/
theorem CoverMap.comparison_comp {g : Z ⟶ Y} (s : CoverMap g B D) (c : Datum G A) :
    (r.comp s).comparison c =
      (s.comparison (r.pull c)).comp ((r.comparison c).reindex g) := by
  apply Descent.reindex_injective (B := D)
  apply Arrow.ext
  ext x t
  let z := Z.obj.elementsMk x.obj x.val.1
  let a : D.family.obj z := x.val.2
  apply (Descent.evaluationEquiv c.toDescent ((g ≫ f).hom.mapElements.obj z)
    ((r.comp s).app z a)).injective
  exact ((r.comp s).comparison_evaluation c z a t).trans
    ((s.comparison_evaluation (r.pull c) z a t).symm.trans
      (r.comparison_evaluation c (g.hom.mapElements.obj z) (s.app z a)
        ((s.comparison (r.pull c)).iso.hom.app z t)).symm)

end Effective

section Refinement
variable {G : Sheaf J GrpCat.{max u v}} {X : Sheaf J (Type (max u v))}
variable {A B : SplitSheaf.Ty X} (r : CoverMap (𝟙 X) A B)
variable [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
variable [Presheaf.IsLocallySurjective J (SplitSheaf.p B).hom]

/-- A same-base refinement includes full admitted subcategories. -/
def CoverMap.admittedRefinementFullyFaithful :
    (r.admittedRestriction (G := G)).FullyFaithful where
  preimage h := ⟨h.hom⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- Refinement preserves and recovers every gauge between existing cocycles.
Essential surjectivity would require the finer cover to admit no additional torsors. -/
def CoverMap.refinementFullyFaithful : (r.pullFunctor (G := G)).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    ((glueFullyFaithful.comp r.admittedRefinementFullyFaithful).ofIso r.comparisonNatIso.symm)

/-- The image consists exactly of finer-cover cocycles whose torsors already
admit trivialization on the original cover. -/
theorem CoverMap.refinement_image (d : Datum G B) :
    (r.pullFunctor (G := G)).essImage d ↔ Admits (G := G) A d.glue.obj := by
  constructor
  · rintro ⟨c, ⟨e⟩⟩
    let k : Arrow c.glue.obj d.glue.obj :=
      (r.comparison c).inverse.comp ((glueFunctor.map e.hom).hom)
    exact ⟨c.glue.property.some.comp (k.reindex (SplitSheaf.p A))⟩
  · intro h
    let P : Admitted (G := G) A := ⟨d.glue.obj, h⟩
    refine ⟨extract P, ⟨glueFullyFaithful.preimageIso ?_⟩⟩
    exact (Admits (G := G) B).isoMk
      ((r.comparison (extract P)).comp (recovery P).hom.hom).toIso

end Refinement
end SquareKit.SheafTorsor.Cocycle
