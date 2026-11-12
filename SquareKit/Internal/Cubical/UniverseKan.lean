import SquareKit.Internal.Cubical.UniverseComposition

/-! Small chart boxes for constructing filling of the larger universe family. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse
open CategoryTheory
universe u

variable {Γ Θ : Context.{u}} {Δ : Context.{u+1}}

/-- Pull back a large-context face to a small chart without raising its dimension. -/
def chartFace (φ : Cofibration Δ) (σ : raisedContext Γ ⟶ Δ) : Cofibration Γ where
  app I := TypeCat.ofHom (fun x => ⟨(φ.app I (σ.app I ⟨x⟩)).down⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun z => ULift.up z.down) ((σ ≫ φ).naturality_apply f ⟨x⟩)

def chartInterval (σ : raisedContext Γ ⟶ Δ) :
    raisedContext (total (interval Γ)) ⟶ total (interval Δ) where
  app I := TypeCat.ofHom (fun x => ⟨σ.app I ⟨x.down.1⟩,⟨x.down.2.down⟩⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Sigma.ext
    · exact σ.naturality_apply f ⟨x.down.1⟩
    · rfl

def chartTube (φ : Cofibration Δ) (σ : raisedContext Γ ⟶ Δ) :
    raisedContext (restrictContext ((chartFace φ σ).reindex (projection (interval Γ)))) ⟶
      restrictContext (φ.reindex (projection (interval Δ))) where
  app I := TypeCat.ofHom (fun x => ⟨(chartInterval σ).app I ⟨x.down.val⟩,x.down.property⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact (chartInterval σ).naturality_apply f ⟨x.down.val⟩

theorem chartFace_reindex (φ : Cofibration Δ) (σ : raisedContext Γ ⟶ Δ) (τ : Θ ⟶ Γ) :
    chartFace φ (raisedSub τ ≫ σ) = (chartFace φ σ).reindex τ := rfl

theorem chartInterval_reindex (σ : raisedContext Γ ⟶ Δ) (τ : Θ ⟶ Γ) :
    chartInterval (raisedSub τ ≫ σ) = raisedSub (liftSub (interval Γ) τ) ≫ chartInterval σ := rfl

theorem chartTube_reindex (φ : Cofibration Δ) (σ : raisedContext Γ ⟶ Δ) (τ : Θ ⟶ Γ) :
    chartTube φ (raisedSub τ ≫ σ) =
      raisedSub (restrictSubstitution ((chartFace φ σ).reindex (projection (interval Γ)))
        (liftSub (interval Γ) τ)) ≫ chartTube φ σ := rfl

variable {φ : Cofibration Δ}
    (b : OpenBox (family (total (interval Δ))) φ)

/-- Read a native large-universe open box on a small chart. -/
def chartBox (σ : raisedContext Γ ⟶ Δ) : CodeSystem.Box Γ (chartFace φ σ) where
  base := σ ≫ code b.base
  tube := chartTube φ σ ≫ code b.tube.toRestricted
  boundary := by
    ext I x
    exact b.boundary (Δ.elementsMk I (σ.app I ⟨x.down.val⟩)) x.down.property

theorem chartBox_reindex (σ : raisedContext Γ ⟶ Δ) (τ : Θ ⟶ Γ) :
    chartBox b (raisedSub τ ≫ σ) = (chartBox b σ).reindex τ := rfl

noncomputable def chartFill (σ : raisedContext Γ ⟶ Δ) :
    raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u} :=
  (chartBox b σ).fillCode

/-- The constructed chart filler commutes with restriction of the small chart. -/
theorem chartFill_reindex (σ : raisedContext Γ ⟶ Δ) (τ : Θ ⟶ Γ) :
    raisedSub (liftSub (interval Γ) τ) ≫ chartFill b σ =
      chartFill b (raisedSub τ ≫ σ) :=
  CodeSystem.Box.fillCode_reindex _ _

/-- Generic evaluation of the small represented chart recovers the large point. -/
theorem chart_generic (x : Δ.Elements) : (chart x).app x.obj ⟨⟨𝟙 x.obj.unop⟩⟩ = x.val :=
  ConcreteCategory.congr_hom (Δ.map_id x.obj) x.val

def chartPoint (x : (total (interval Δ)).Elements) :
    (raisedContext (total (interval (representable.{u} x.obj.unop)))).obj x.obj :=
  ⟨⟨⟨𝟙 x.obj.unop⟩,⟨x.val.2.down⟩⟩⟩

theorem chartInterval_generic (x : (total (interval Δ)).Elements) :
    (chartInterval (chart (intervalBase x))).app x.obj (chartPoint x) = x.val := by
  apply Sigma.ext
  · exact chart_generic (intervalBase x)
  · rfl

theorem chartPoint_natural {x y : (total (interval Δ)).Elements} (f : x ⟶ y) :
    (raisedContext (total (interval (representable.{u} x.obj.unop)))).map f.hom (chartPoint x) =
      (raisedSub (liftSub (interval (representable.{u} x.obj.unop))
        (representableMap f.hom.unop))).app y.obj (chartPoint y) := by
  apply ULift.ext
  apply Sigma.ext
  · exact congrArg ULift.up ((Category.comp_id f.hom.unop).trans (Category.id_comp f.hom.unop).symm)
  · exact heq_of_eq (congrArg (fun z : (total (interval Δ)).obj y.obj =>
      (ULift.up z.2.down : ULift.{u} (Cube.Hom y.obj.unop ⟨1⟩))) f.map_val)

noncomputable def fillValue (x : (total (interval Δ)).Elements) : SmallFamilyCode.{u} x.obj.unop :=
  (chartFill b (chart (intervalBase x))).app x.obj (chartPoint x)

private theorem code_naturality {X : Context.{u+1}}
    (a : X ⟶ smallFamilyCodes.{u}) {I J : Cubeᵒᵖ} (f : I ⟶ J) (x : X.obj I) :
    smallFamilyCodes.map f (a.app I x) = a.app J (X.map f x) :=
  (a.naturality_apply f x).symm

private theorem fillValue_map {x y : (total (interval Δ)).Elements} (f : x ⟶ y) :
    smallFamilyCodes.map f.hom (fillValue b x) =
      (chartFill b (chart (intervalBase x))).app y.obj
        ((raisedContext (total (interval (representable.{u} x.obj.unop)))).map f.hom (chartPoint x)) :=
  @code_naturality (raisedContext (total (interval (representable.{u} x.obj.unop))))
    (chartFill b (chart (intervalBase x))) x.obj y.obj f.hom (chartPoint x)

private theorem fillValue_chart {x y : (total (interval Δ)).Elements} (f : x ⟶ y) :
    (chartFill b (chart (intervalBase x))).app y.obj
        ((raisedContext (total (interval (representable.{u} x.obj.unop)))).map f.hom (chartPoint x)) =
      (chartFill b (raisedSub (representableMap f.hom.unop) ≫ chart (intervalBase x))).app y.obj
        (chartPoint y) := by
  rw [chartPoint_natural f]
  exact congrArg (fun a : raisedContext (total (interval (representable.{u} y.obj.unop))) ⟶ smallFamilyCodes.{u} =>
    a.app y.obj (chartPoint y)) (chartFill_reindex b (chart (intervalBase x)) (representableMap f.hom.unop))

private theorem fillValue_restrict {x y : (total (interval Δ)).Elements} (f : x ⟶ y) :
    (chartFill b (raisedSub (representableMap f.hom.unop) ≫ chart (intervalBase x))).app y.obj
        (chartPoint y) = fillValue b y :=
  congrArg (fun a : raisedContext (representable.{u} y.obj.unop) ⟶ Δ =>
    (chartFill b a).app y.obj (chartPoint y))
    (chart_restrict ((projection (interval Δ)).mapElements.map f))

theorem fillValue_natural {x y : (total (interval Δ)).Elements} (f : x ⟶ y) :
    smallFamilyCodes.map f.hom (fillValue b x) = fillValue b y :=
  (fillValue_map b f).trans ((fillValue_chart b f).trans (fillValue_restrict b f))

noncomputable def fillTerm : Term (family (total (interval Δ))) where
  val := fillValue b
  property f := fillValue_natural b f

theorem fillTerm_cap : (fillTerm b).reindex (endpointSub Δ false) = b.base := by
  apply Term.ext
  intro x
  have hc := congrArg (fun a => a.app x.obj ⟨⟨𝟙 x.obj.unop⟩⟩)
    (CodeSystem.Box.fillCode_cap (chartBox b (chart x)))
  refine hc.trans ?_
  change b.base.val (Δ.elementsMk x.obj ((chart x).app x.obj ⟨⟨𝟙 x.obj.unop⟩⟩)) = b.base.val x
  rw [chart_generic]

theorem fillTerm_tube (x : (total (interval Δ)).Elements)
    (hx : (φ.reindex (projection (interval Δ))).full x) :
    (fillTerm b).val x = b.tube.val x hx := by
  let σ := chart (intervalBase x)
  let y : (total (interval (representable.{u} x.obj.unop))).obj x.obj := (chartPoint x).down
  have hy : ((chartFace φ σ).reindex (projection (interval _))).full
      ((total (interval (representable.{u} x.obj.unop))).elementsMk x.obj y) := by
    change (φ.reindex (projection (interval Δ))).full
      ((total (interval Δ)).elementsMk x.obj ((chartInterval σ).app x.obj (chartPoint x)))
    rw [chartInterval_generic]
    exact hx
  have hc := congrArg (fun a => a.app x.obj ⟨⟨y,hy⟩⟩)
    (CodeSystem.Box.fillCode_tube (chartBox b σ))
  refine hc.trans ?_
  apply eq_of_heq
  apply PartialSection.val_heq b.tube
  change (total (interval Δ)).elementsMk x.obj ((chartInterval σ).app x.obj (chartPoint x)) = x
  rw [chartInterval_generic]

theorem fillTerm_fills : b.Fills (fillTerm b) := ⟨fillTerm_cap b,fillTerm_tube b⟩

theorem chartBox_input_reindex {Λ : Context.{u+1}} (σ : Λ ⟶ Δ)
    (τ : raisedContext Γ ⟶ Λ) :
    chartBox (b.reindex σ) τ = chartBox b (τ ≫ σ) := rfl

theorem fillTerm_reindex {Λ : Context.{u+1}} (σ : Λ ⟶ Δ) :
    fillTerm (b.reindex σ) = (fillTerm b).reindex (liftSub (interval Δ) σ) := by
  apply Term.ext
  intro x
  change (chartBox (b.reindex σ) (chart (intervalBase x))).fillCode.app x.obj (chartPoint x) = _
  rw [chartBox_input_reindex]
  exact congrArg (fun a : raisedContext (representable.{u} x.obj.unop) ⟶ Δ =>
    (chartBox b a).fillCode.app x.obj (chartPoint x))
    (chart_substitution σ (intervalBase x)).symm

/-- Filling of the actual dimension-dependent universe family, assembled from
small chart fillers with their chosen substitution laws. -/
noncomputable def filling (Ξ : Context.{u+1}) : Filling (family.{u} Ξ) where
  fill _ _ b := fillTerm b

theorem filling_lawful (Ξ : Context.{u+1}) : (filling.{u} Ξ).Lawful where
  fills _ _ b := fillTerm_fills b
  uniform _ _ b σ := fillTerm_reindex b σ

end SquareKit.Cubical.Presheaf.SmallUniverse
