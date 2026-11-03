import SquareKit.SmoothTorsorEquivalence

/-! Infinitesimal torsor invariance over arbitrary sheaf parameters. -/
noncomputable section
namespace SquareKit.SmoothOpenSite
open CategoryTheory Opposite SmoothPresentationSite SmoothGeometricKL SheafTorsor SheafRelation
variable {H : Type} [Group H]
local notation "G" => locallyConstantGroup H
local notation "D" => PresentationGeometry.infinitesimal topology

/-- Evaluation at an arbitrary square-zero section, including generalized ones. -/
def nilpotentEvaluation {A : Code} (d : (D).obj.obj (atStage A)) : dual A ⟶ A :=
  dualLift A A (𝟙 A) d

theorem nilpotentEvaluation_inl {A : Code} (d : (D).obj.obj (atStage A)) :
    inl A ≫ nilpotentEvaluation d = 𝟙 A := dualLift_inl _ _ _ _

theorem nilpotentEvaluation_natural {A B : Code} (f : A ⟶ B)
    (d : (D).obj.obj (atStage A)) :
    dualMap f ≫ nilpotentEvaluation ((D).obj.map (stageMap f) d) =
      nilpotentEvaluation d ≫ f := by
  apply dual_ext
  · rw [← Category.assoc, dualMap_inl, Category.assoc,
      nilpotentEvaluation_inl, ← Category.assoc, nilpotentEvaluation_inl, Category.comp_id, Category.id_comp]
  · change smoothMap (nilpotentEvaluation _) (smoothMap (dualMap f) (eps A).val) =
      smoothMap f (smoothMap (nilpotentEvaluation d) (eps A).val)
    rw [dualLift_eps]
    change smoothMap (dualLift B B (𝟙 B) _) (eps B).val =
      smoothMap f (smoothMap (dualLift A A (𝟙 A) d) (eps A).val)
    rw [dualLift_eps, dualLift_eps]
    rfl

/-- Zero and projection for every sheaf parameter, not just represented ones. -/
def parameterZero (X : Sheaf topology Type) : X ⟶ product D X := ⟨{
  app U := ↾fun x => (⟨0, by simp⟩, x)
  naturality U V f := by
    ext x
    apply Prod.ext
    · apply Subtype.ext
      exact (map_zero (smoothMap f.unop.unop).toAlgHom).symm
    · rfl }⟩

@[simp] theorem parameterZero_projection (X : Sheaf topology Type) :
    parameterZero X ≫ snd D X = 𝟙 X := rfl

/-- Replace the nilpotent coordinate by the universal epsilon and pull the
parameter through the dual extension. -/
def productPath (X : Sheaf topology Type) : product D X ⟶ dualSheaf (product D X) := ⟨{
  app U := ↾fun x => (eps U.unop.unop, X.obj.map (stageMap (inl U.unop.unop)) x.2)
  naturality U V f := by
    ext x
    apply Prod.ext
    · apply Subtype.ext
      exact (congrArg Subtype.val (dualMap_eps f.unop.unop)).symm
    · symm
      change X.obj.map (stageMap (dualMap f.unop.unop))
        (X.obj.map (stageMap (inl U.unop.unop)) x.2) =
          X.obj.map (stageMap (inl V.unop.unop)) (X.obj.map f x.2)
      rw [← types_comp_apply, ← X.obj.map_comp, ← types_comp_apply, ← X.obj.map_comp]
      exact congrArg (fun k => X.obj.map (stageMap k) x.2) (dualMap_inl f.unop.unop) }⟩

theorem productPath_zero (X : Sheaf topology Type) :
    productPath X ≫ dualSheafZero (product D X) = snd D X ≫ parameterZero X := by
  ext U x
  apply Prod.ext
  · apply Subtype.ext
    exact dualLift_eps _ _ _ _
  · change X.obj.map (stageMap (dualZero U.unop.unop))
      (X.obj.map (stageMap (inl U.unop.unop)) x.2) = x.2
    rw [← types_comp_apply, ← X.obj.map_comp]
    change X.obj.map (stageMap (inl U.unop.unop ≫ dualZero U.unop.unop)) x.2 = x.2
    rw [inl_dualZero]
    exact congrArg (fun k => k x.2) (X.obj.map_id U)

/-- Evaluate the universal path at its original coordinate. -/
def productEvaluationElement {X : Sheaf topology Type} (x : (product D X).obj.Elements) :
    (dualElements (product D X)).obj ((productPath X).hom.mapElements.obj x) ⟶ x :=
  Functor.Elements.homMk (stageMap (nilpotentEvaluation x.val.1)) (by
    apply Prod.ext
    · apply Subtype.ext
      exact dualLift_eps _ _ _ _
    · change X.obj.map (stageMap (nilpotentEvaluation x.val.1))
        (X.obj.map (stageMap (inl x.obj.unop.unop)) x.val.2) = x.val.2
      rw [← types_comp_apply, ← X.obj.map_comp]
      change X.obj.map (stageMap (inl _ ≫ nilpotentEvaluation x.val.1)) x.val.2 = x.val.2
      rw [nilpotentEvaluation_inl]
      exact congrArg (fun k => k x.val.2) (X.obj.map_id x.obj))

theorem productEvaluationElement_natural {X : Sheaf topology Type}
    {x y : (product D X).obj.Elements} (f : x ⟶ y) :
    (dualElements (product D X)).map ((productPath X).hom.mapElements.map f) ≫
      productEvaluationElement y = productEvaluationElement x ≫ f := by
  apply Functor.Elements.hom_ext
  have hd : (D).obj.map f.hom x.val.1 = y.val.1 := congrArg Prod.fst f.map_val
  change stageMap (dualMap f.hom.unop.unop ≫ nilpotentEvaluation y.val.1) =
    stageMap (nilpotentEvaluation x.val.1 ≫ f.hom.unop.unop)
  rw [← hd]
  exact congrArg stageMap (nilpotentEvaluation_natural f.hom.unop.unop x.val.1)

/-- Path evaluation is equivariant because constant group labels are rigid. -/
def productEvaluationTorsorMap {X : Sheaf topology Type} (P : Torsor G (product D X)) :
    EquivariantMap (reindex (dualTorsor P) (productPath X)) P where
  hom := {
    app x := P.family.family.map (productEvaluationElement x)
    naturality {x y} f := by
      change P.family.family.map ((dualElements _).map ((productPath X).hom.mapElements.map f)) ≫
        P.family.family.map (productEvaluationElement y) =
          P.family.family.map (productEvaluationElement x) ≫ P.family.family.map f
      rw [← P.family.family.map_comp, ← P.family.family.map_comp, productEvaluationElement_natural] }
  equivariant x g p := by
    change P.family.family.obj ((dualElements (product D X)).obj
      ((productPath X).hom.mapElements.obj x)) at p
    change P.family.family.map (productEvaluationElement x)
      (P.act _ ((G).obj.map (stageMap (inl x.obj.unop.unop)) g) p) =
        P.act x g (P.family.family.map (productEvaluationElement x) p)
    rw [P.natural]
    congr 1
    change (G).obj.map (stageMap (nilpotentEvaluation x.val.1))
      ((G).obj.map (stageMap (inl x.obj.unop.unop)) g) = g
    rw [← ConcreteCategory.comp_apply, ← (G).obj.map_comp]
    change (G).obj.map (stageMap (inl _ ≫ nilpotentEvaluation x.val.1)) g = g
    rw [nilpotentEvaluation_inl]
    exact congrArg (fun k => k g) ((G).obj.map_id x.obj)

/-- Two constructed equivariant isomorphisms compare contraction with the
original torsor. Neither comparison assumes that the torsor has a section. -/
def parameterContractionIso (X : Sheaf topology Type) (P : Torsor G (product D X)) :
    reindex P ((productPath X ≫ dualSheafZero (product D X))) ≅ P :=
  (SheafTorsor.Arrow.toIso (show reindex (dualTorsor P) (productPath X) ⟶ reindex P ((productPath X ≫ dualSheafZero (product D X))) from
    (dualTorsorZero P).reindex (productPath X))).symm ≪≫
    SheafTorsor.Arrow.toIso (show reindex (dualTorsor P) (productPath X) ⟶ P from
      (productEvaluationTorsorMap P).toArrow)

theorem productEvaluationTorsor_natural (X : Sheaf topology Type) {P Q : Torsor G (product D X)} (f : P ⟶ Q) :
    (restriction (productPath X)).map ((dualTorsorFunctor _).map f) ≫
      (productEvaluationTorsorMap Q).toArrow = (productEvaluationTorsorMap P).toArrow ≫ f := by
  apply SheafTorsor.Arrow.ext
  ext x p
  exact (NatTrans.naturality_apply f.iso.hom (productEvaluationElement x) p).symm

theorem parameterContraction_natural (X : Sheaf topology Type) {P Q : Torsor G (product D X)} (f : P ⟶ Q) :
    (restriction ((productPath X ≫ dualSheafZero (product D X)))).map f ≫ (parameterContractionIso X Q).hom =
      (parameterContractionIso X P).hom ≫ f := by
  let aP : reindex (dualTorsor P) (productPath X) ⟶ reindex P ((productPath X ≫ dualSheafZero (product D X))) :=
    (dualTorsorZero P).reindex (productPath X)
  let aQ : reindex (dualTorsor Q) (productPath X) ⟶ reindex Q ((productPath X ≫ dualSheafZero (product D X))) :=
    (dualTorsorZero Q).reindex (productPath X)
  let k : reindex (dualTorsor P) (productPath X) ⟶
      reindex (dualTorsor Q) (productPath X) :=
    (restriction (productPath X)).map ((dualTorsorFunctor _).map f)
  have ha : k ≫ aQ = aP ≫ (restriction ((productPath X ≫ dualSheafZero (product D X)))).map f := by
    exact congrArg (fun h => (restriction (productPath X)).map h) (dualTorsorZero_natural f)
  have ha' := congrArg (fun h => h.iso.hom) ha
  have he := congrArg (fun h => h.iso.hom) (productEvaluationTorsor_natural X f)
  apply SheafTorsor.Arrow.ext
  change ((restriction ((productPath X ≫ dualSheafZero (product D X)))).map f).iso.hom ≫
    (aQ.iso.inv ≫ (productEvaluationTorsorMap Q).toArrow.iso.hom) =
      (aP.iso.inv ≫ (productEvaluationTorsorMap P).toArrow.iso.hom) ≫ f.iso.hom
  apply (cancel_epi aP.iso.hom).mp
  change k.iso.hom ≫ aQ.iso.hom = aP.iso.hom ≫ _ at ha'
  dsimp only [restriction] at ha' ⊢
  simp only [← Category.assoc]
  rw [← ha']
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact he

def parameterContractionNatIso (X : Sheaf topology Type) :
    (restriction ((productPath X ≫ dualSheafZero (product D X))) :
      Torsor G (product D X) ⥤ Torsor G (product D X)) ≅ 𝟭 _ :=
  NatIso.ofComponents (parameterContractionIso X) (fun {_ _} f => parameterContraction_natural X f)


/-- Projection is an equivalence over every sheaf parameter. The inverse is
literal zero restriction, and the construction retains torsor arrows. -/
def parameterTorsorEquivalence (X : Sheaf topology Type) :
    Torsor G X ≌ Torsor G (product D X) :=
  CategoryTheory.Equivalence.mk (restriction (snd D X)) (restriction (parameterZero X))
    (eqToIso (by rw [restriction_comp, parameterZero_projection, restriction_id]))
    (eqToIso (by rw [restriction_comp, ← productPath_zero]) ≪≫ parameterContractionNatIso X)

theorem parameterZero_natural {X Y : Sheaf topology Type} (f : X ⟶ Y) :
    f ≫ parameterZero Y = parameterZero X ≫ SheafFunction.parameterMap D f := rfl

theorem parameterTorsor_baseChange {X Y : Sheaf topology Type} (f : X ⟶ Y) :
    restriction f ⋙ (parameterTorsorEquivalence (H := H) X).functor =
      (parameterTorsorEquivalence (H := H) Y).functor ⋙
        restriction (SheafFunction.parameterMap D f) := by
  change restriction _ ⋙ restriction _ = restriction _ ⋙ restriction _
  rw [restriction_comp, restriction_comp]
  rfl

theorem parameterTorsorZero_baseChange {X Y : Sheaf topology Type} (f : X ⟶ Y) :
    restriction (SheafFunction.parameterMap D f) ⋙
        (parameterTorsorEquivalence (H := H) X).inverse =
      (parameterTorsorEquivalence (H := H) Y).inverse ⋙ restriction f := by
  change restriction _ ⋙ restriction _ = restriction _ ⋙ restriction _
  rw [restriction_comp, restriction_comp]
  rfl

end SquareKit.SmoothOpenSite

