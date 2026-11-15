import SquareKit.Internal.PathTransport.TwoFamilyPathContractionArrows
import SquareKit.Internal.PathTransport.TwoFamilyPathFaithful
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
/-- The contraction component projects to the identity first endpoint. -/
theorem pathFirst_contractionComponent (x : PathContext F) :
    (pathFirst F).map (contractionComponent F x) = 𝟙 ((pathFirst F).obj x) := by
  apply Pseudofunctor.CoGrothendieck.ext
  · rfl
  · exact heq_of_eq (pathFirst_map_fiber F (contractionComponent F x))
private theorem projectionFiber_cast_right {x y : PathContext F} {p q r : x ⟶ y}
    (α : p ⟶ q) (h : q = r) :
    HEq ((pathFirst F).map₂ (α ≫ eqToHom h)).fiber ((pathFirst F).map₂ α).fiber := by
  cases h
  rw [eqToHom_refl, Category.comp_id]
private theorem projectionFiber_cast_left {x y : PathContext F} {p q r : x ⟶ y}
    (h : p = q) (α : q ⟶ r) :
    HEq ((pathFirst F).map₂ (eqToHom h ≫ α)).fiber ((pathFirst F).map₂ α).fiber := by
  cases h
  rw [eqToHom_refl, Category.id_comp]
/-- The endpoint comparison has identity first fiber cell up to its canonical boundary. -/
theorem contractionEndpointSquare_firstFiber {x y : PathContext F} (p : x ⟶ y) :
    HEq (contractionEndpointSquare F p).fiber.1
      (𝟙 (show (F.map p.base.base).obj x.base.fiber.1 ⟶ y.base.fiber.1 from p.base.fiber.1)) := by
  let u : (F.map p.base.base).obj x.base.fiber.1 ⟶ y.base.fiber.1 := p.base.fiber.1
  let e : (contractionRightEndpoint F p).fiber =
      ((endpointFamily F).map₂ (𝟙 p.base.base)).app (x.base.fiber.1,x.base.fiber.1) ≫
        (contractionRightEndpoint F p).fiber := by
    rw [(endpointFamily F).map₂_id]
    exact (Category.id_comp _).symm
  change HEq ((𝟙 u) ≫ (eqToHom e).1) (𝟙 u)
  rw [CategoryTheory.eqToHom_fst]
  exact comp_eqToHom_heq _ _
/-- The actual comparison retains that identity first fiber cell through both boundary casts. -/
theorem contractionNaturalityCell_firstFiber {x y : PathContext F} (p : x ⟶ y) :
    HEq ((pathFirst F).map₂ (contractionNaturalityCell F p)).fiber
      (𝟙 (show (F.map p.base.base).obj x.base.fiber.1 ⟶ y.base.fiber.1 from p.base.fiber.1)) := by
  have h0 : HEq (contractionLiftCell F p).base.fiber.1
      (𝟙 (show (F.map p.base.base).obj x.base.fiber.1 ⟶ y.base.fiber.1 from p.base.fiber.1)) := by
    change HEq (contractionEndpointSquare F p).fiber.1 _
    exact contractionEndpointSquare_firstFiber F p
  have h1 := projectionFiber_cast_left F (contractionLeftArrow_composite F p)
    (contractionLiftCell F p ≫ eqToHom (contractionRightArrow_composite F p).symm)
  have h2 := projectionFiber_cast_right F (contractionLiftCell F p)
    (contractionRightArrow_composite F p).symm
  have h3 := pathFirst_cell_fiber_heq F (contractionLiftCell F p)
  -- Explicitly construct the HEq chain to avoid repeatedly inferring nested
  -- projection/cast types. Lean's kernel checks the resulting proof normally.
  run_tac Lean.Elab.Tactic.withMainContext do
    let h1 ← Lean.Meta.getLocalDeclFromUserName `h1
    let h2 ← Lean.Meta.getLocalDeclFromUserName `h2
    let h3 ← Lean.Meta.getLocalDeclFromUserName `h3
    let h4 ← Lean.Meta.getLocalDeclFromUserName `h0
    let t1 ← Lean.instantiateMVars h1.type
    let t2 ← Lean.instantiateMVars h2.type
    let t3 ← Lean.instantiateMVars h3.type
    let t4 ← Lean.instantiateMVars h4.type
    unless [t1,t2,t3,t4].all (fun t => t.isAppOfArity ``HEq 4) do
      throwError "Expected fully applied HEq types"
    let a := t1.getAppArgs
    let b := t2.getAppArgs
    let c := t3.getAppArgs
    let d := t4.getAppArgs
    let trans := Lean.mkConst ``HEq.trans t1.getAppFn.constLevels!
    let t34 := Lean.mkAppN trans #[c[0]!,c[2]!,d[2]!,c[1]!,c[3]!,d[3]!,h3.toExpr,h4.toExpr]
    let t234 := Lean.mkAppN trans #[b[0]!,b[2]!,d[2]!,b[1]!,b[3]!,d[3]!,h2.toExpr,t34]
    let proof := Lean.mkAppN trans #[a[0]!,a[2]!,d[2]!,a[1]!,a[3]!,d[3]!,h1.toExpr,t234]
    Lean.Elab.Tactic.closeMainGoal `exact proof
private theorem projectionBase_cast_right {x y : PathContext F} {p q r : x ⟶ y}
    (α : p ⟶ q) (h : q = r) :
    HEq ((pathFirst F).map₂ (α ≫ eqToHom h)).base ((pathFirst F).map₂ α).base := by
  cases h
  rw [eqToHom_refl, Category.comp_id]
private theorem projectionBase_cast_left {x y : PathContext F} {p q r : x ⟶ y}
    (h : p = q) (α : q ⟶ r) :
    HEq ((pathFirst F).map₂ (eqToHom h ≫ α)).base ((pathFirst F).map₂ α).base := by
  cases h
  rw [eqToHom_refl, Category.id_comp]
/-- The first projection of the actual comparison has identity base cell up to boundary casts. -/
theorem contractionNaturalityCell_firstBase {x y : PathContext F} (p : x ⟶ y) :
    HEq ((pathFirst F).map₂ (contractionNaturalityCell F p)).base (𝟙 p.base.base) := by
  apply HEq.trans (projectionBase_cast_left F _ _)
  exact projectionBase_cast_right F _ _
/-- Reflexivity followed by first projection retains every dependent arrow. -/
theorem pathFirst_reflexivity_map {x y : Total F} (p : x ⟶ y) :
    (pathFirst F).map ((pathReflexivity F).map p) = p := by
  apply Pseudofunctor.CoGrothendieck.ext
  · rfl
  · apply HEq.trans (heq_of_eq (pathFirst_map_fiber F ((pathReflexivity F).map p)))
    exact heq_of_eq (diagonal_fiber_fst F p)
/-- The left contraction composite projects to the supplied first-endpoint arrow. -/
theorem contractionLeft_projection {x y : PathContext F} (p : x ⟶ y) :
    (pathFirst F).map ((pathReflexivity F).map ((pathFirst F).map p) ≫ contractionComponent F y) =
      (pathFirst F).map p := by
  rw [(pathFirst F).map_comp, pathFirst_reflexivity_map, pathFirst_contractionComponent]
  exact Category.comp_id _
/-- The right contraction composite projects to the supplied first-endpoint arrow. -/
theorem contractionRight_projection {x y : PathContext F} (p : x ⟶ y) :
    (pathFirst F).map (contractionComponent F x ≫ p) = (pathFirst F).map p := by
  rw [(pathFirst F).map_comp, pathFirst_contractionComponent]
  exact Category.id_comp _
omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
private theorem total_cell_heq {x y : Total F} {p q p' q' : x ⟶ y}
 (hp : p = p') (hq : q = q') (α : p ⟶ q) (β : p' ⟶ q')
 (hb : HEq α.base β.base) (hf : HEq α.fiber β.fiber) : HEq α β := by
 cases hp
 cases hq
 apply heq_of_eq
 refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (eq_of_heq hb) ?_
 exact eq_of_heq (HEq.trans hf (comp_eqToHom_heq _ _).symm)
private theorem casts_heq {C : Type*} [Category C] {a b a' b' : C}
    (h : a = b) (k : a' = b') (e : a = a') : HEq (eqToHom h) (eqToHom k) := by
  cases e; cases h; cases k; rfl
/-- The projected actual comparison is heterogeneously the identity cell. -/
theorem contractionNaturalityCell_first_heq {x y : PathContext F} (p : x ⟶ y) :
    HEq ((pathFirst F).map₂ (contractionNaturalityCell F p)) (𝟙 ((pathFirst F).map p)) := by
  apply total_cell_heq F (contractionLeft_projection F p) (contractionRight_projection F p)
  · exact contractionNaturalityCell_firstBase F p
  · apply HEq.trans (contractionNaturalityCell_firstFiber F p)
    symm
    change HEq ((eqToHom (rfl : (pathFirst F).map p = (pathFirst F).map p)).fiber) _
    rw [total_eqToHom_fiber]
    exact casts_heq _ rfl (pathFirst_map_fiber F p)
private theorem canonical_from_heq {C : Type*} [Category C] {a b c : C}
    (h : a = c) (k : b = c) (f : a ⟶ b) (hf : HEq f (𝟙 c)) :
    f = eqToHom (h.trans k.symm) := by
  cases h
  cases k
  exact eq_of_heq hf
/-- The projected actual comparison is the canonical equality cell between its boundaries. -/
theorem contractionNaturalityCell_first {x y : PathContext F} (p : x ⟶ y) :
    (pathFirst F).map₂ (contractionNaturalityCell F p) =
      eqToHom ((contractionLeft_projection F p).trans (contractionRight_projection F p).symm) :=
  canonical_from_heq (contractionLeft_projection F p) (contractionRight_projection F p)
    _ (contractionNaturalityCell_first_heq F p)
end SquareKit.Internal.PathTransport.TwoFamily
