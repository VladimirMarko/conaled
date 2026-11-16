import SquareKit.Internal.Cubical.CartesianSubstitution
import SquareKit.Internal.Cubical.CartesianDependentFilling

/-! Path filling with both endpoint faces retained throughout the box. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

def Term.convert {Γ : Context.{u}} {A B : Family Γ} (h : A = B) (t : Term A) : Term B := h ▸ t

theorem Term.convert_val_heq {Γ : Context.{u}} {A B : Family Γ} (h : A = B)
    (a : Term A) (x : Γ.Elements) : HEq ((Term.convert h a).val x) (a.val x) := by
  cases h
  rfl

abbrev intervalFace (Γ : Context.{u}) (b : Bool) : Subcontext (total (interval Γ)) :=
  Subcontext.intervalEq (generic (interval Γ)) (endpoint (total (interval Γ)) b)

theorem Subcontext.full_join {Γ : Context.{u}} (φ ψ : Subcontext Γ) (x : Γ.Elements) :
    (φ.join ψ).holds x ↔ φ.holds x ∨ ψ.holds x := Iff.rfl

theorem intervalFace_iff {Γ : Context.{u}} (b : Bool) (x : (total (interval Γ)).Elements) :
    (intervalFace Γ b).holds x ↔ x.val.2 = (endpoint Γ b).val ((projection (interval Γ)).mapElements.obj x) := Iff.rfl


def swapIntervals (Γ : Context.{u}) :
    total (interval (total (interval Γ))) ⟶ total (interval (total (interval Γ))) where
  app _ := TypeCat.ofHom (fun z => ⟨⟨z.1.1,z.2⟩,z.1.2⟩)
  naturality _ _ _ := rfl

theorem swapIntervals_twice (Γ : Context.{u}) : swapIntervals Γ ≫ swapIntervals Γ = 𝟙 _ := rfl

theorem swapIntervals_endpoint (Γ : Context.{u}) (b : Bool) :
    endpointSub (total (interval Γ)) b ≫ swapIntervals Γ = liftSub (interval (total (interval Γ))) (endpointSub Γ b) := rfl

theorem swapIntervals_lift_endpoint (Γ : Context.{u}) (b : Bool) :
    liftSub (interval (total (interval Γ))) (endpointSub Γ b) ≫ swapIntervals Γ = endpointSub (total (interval Γ)) b := rfl

theorem swapIntervals_natural {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    swapIntervals Δ ≫ liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ) =
      liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ) ≫ swapIntervals Γ := rfl

theorem intervalFace_inclusion (Γ : Context.{u}) (b : Bool) :
    (restrictInclusion (intervalFace Γ b) ≫ projection (interval Γ)) ≫ endpointSub Γ b =
      restrictInclusion (intervalFace Γ b) := by
  ext I z
  change (⟨z.val.1,(endpoint Γ b).val (Γ.elementsMk I z.val.1)⟩ :
    (total (interval Γ)).obj I) = z.val
  exact congrArg (fun r => (⟨z.val.1,r⟩ : (total (interval Γ)).obj I))
    (((intervalFace_iff b
      ((total (interval Γ)).elementsMk I z.val)).mp z.property).symm)

def endpointSection {Γ : Context.{u}} (B : Family (total (interval Γ))) (b : Bool)
    (a : Term (reindex B (endpointSub Γ b))) : PartialSection B (intervalFace Γ b) :=
  PartialSection.ofRestricted
    ((Term.convert (congrArg (fun σ => reindex B σ) (intervalFace_inclusion Γ b)) ((Term.reindex a (restrictInclusion (intervalFace Γ b) ≫ projection (interval Γ))))))

theorem endpointSection_val {Γ : Context.{u}} (B : Family (total (interval Γ))) (b : Bool)
    (a : Term (reindex B (endpointSub Γ b))) (x : (total (interval Γ)).Elements)
    (h : (intervalFace Γ b).holds x) :
    HEq ((endpointSection B b a).val x h) (a.val ((projection (interval Γ)).mapElements.obj x)) :=
  Term.convert_val_heq _ _ ((restrictContext (intervalFace Γ b)).elementsMk x.obj ⟨x.val,h⟩)

theorem intervalFace_disjoint {Γ : Context.{u}} (x : (total (interval Γ)).Elements)
    (h₀ : (intervalFace Γ false).holds x) (h₁ : (intervalFace Γ true).holds x) : False := by
  have h := ((intervalFace_iff false x).mp h₀).symm.trans
    ((intervalFace_iff true x).mp h₁)
  have hd := congrArg (fun q => q.down 0) h
  cases hd

theorem endpointSection_reindex {Γ Δ : Context.{u}} (B : Family (total (interval Γ))) (b : Bool)
    (a : Term (reindex B (endpointSub Γ b))) (σ : Δ ⟶ Γ) :
    ((endpointSection B b a).reindex (liftSub (interval Γ) σ)) =
      endpointSection (reindex B (liftSub (interval Γ) σ)) b ((Term.reindex a σ)) := by
  apply PartialSection.ext
  intro x h
  apply eq_of_heq
  exact (endpointSection_val B b a ((liftSub (interval Γ) σ).mapElements.obj x) h).trans
    (endpointSection_val (reindex B (liftSub (interval Γ) σ)) b ((Term.reindex a σ)) x h).symm


def PartialSection.pathApp {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (Cartesian.reindex B (endpointSub Γ false))}
    {a₁ : Term (Cartesian.reindex B (endpointSub Γ true))} {φ : Subcontext Γ}
    (s : PartialSection (path B a₀ a₁) φ) :
    PartialSection B (φ.reindex (projection (interval Γ))) :=
  PartialSection.ofRestricted
    (Term.reindex (Cartesian.pathApp (Term.map (pathReindex B a₀ a₁ (restrictInclusion φ)) s.toRestricted))
      (restrictedInterval φ))

theorem PartialSection.pathApp_val {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (Cartesian.reindex B (endpointSub Γ false))}
    {a₁ : Term (Cartesian.reindex B (endpointSub Γ true))} {φ : Subcontext Γ}
    (s : PartialSection (path B a₀ a₁) φ) (x : (total (interval Γ)).Elements)
    (h : (φ.reindex (projection (interval Γ))).holds x) :
    s.pathApp.val x h =
      (s.val ((projection (interval Γ)).mapElements.obj x) h).val.val (𝟙 _) x.val.2 := rfl

theorem PartialSection.pathApp_reindex {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (Cartesian.reindex B (endpointSub Γ false))}
    {a₁ : Term (Cartesian.reindex B (endpointSub Γ true))} {φ : Subcontext Γ}
    (s : PartialSection (path B a₀ a₁) φ) (σ : Δ ⟶ Γ) :
    ((s.reindex σ).map (pathReindex B a₀ a₁ σ)).pathApp =
      s.pathApp.reindex (liftSub (interval Γ) σ) := rfl

theorem PartialSection.pathApp_zero {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (Cartesian.reindex B (endpointSub Γ false))}
    {a₁ : Term (Cartesian.reindex B (endpointSub Γ true))} {φ : Subcontext Γ}
    (s : PartialSection (path B a₀ a₁) φ) (x : (total (interval Γ)).Elements)
    (h : (φ.reindex (projection (interval Γ))).holds x) (h₀ : (intervalFace Γ false).holds x) :
    HEq (s.pathApp.val x h) (a₀.val ((projection (interval Γ)).mapElements.obj x)) := by
  rcases x with @⟨I,⟨γ,r⟩⟩
  have hr := (intervalFace_iff false
    ((total (interval Γ)).elementsMk I ⟨γ,r⟩)).mp h₀
  change r = (endpoint Γ false).val (Γ.elementsMk I γ) at hr
  subst r
  exact heq_of_eq ((s.val (Γ.elementsMk I γ) h).property (𝟙 _)).1

theorem PartialSection.pathApp_one {Γ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (Cartesian.reindex B (endpointSub Γ false))}
    {a₁ : Term (Cartesian.reindex B (endpointSub Γ true))} {φ : Subcontext Γ}
    (s : PartialSection (path B a₀ a₁) φ) (x : (total (interval Γ)).Elements)
    (h : (φ.reindex (projection (interval Γ))).holds x) (h₁ : (intervalFace Γ true).holds x) :
    HEq (s.pathApp.val x h) (a₁.val ((projection (interval Γ)).mapElements.obj x)) := by
  rcases x with @⟨I,⟨γ,r⟩⟩
  have hr := (intervalFace_iff true
    ((total (interval Γ)).elementsMk I ⟨γ,r⟩)).mp h₁
  change r = (endpoint Γ true).val (Γ.elementsMk I γ) at hr
  subst r
  exact heq_of_eq ((s.val (Γ.elementsMk I γ) h).property (𝟙 _)).2



noncomputable def endpointBoundary {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) :
    PartialSection B ((intervalFace Γ false).join (intervalFace Γ true)) :=
  (endpointSection B false a₀).glue (endpointSection B true a₁)
    (fun x h₀ h₁ => (intervalFace_disjoint x h₀ h₁).elim)

theorem endpointBoundary_zero {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (x : (total (interval Γ)).Elements)
    (h : ((intervalFace Γ false).join (intervalFace Γ true)).holds x)
    (h₀ : (intervalFace Γ false).holds x) :
    (endpointBoundary B a₀ a₁).val x h = (endpointSection B false a₀).val x h₀ :=
  glueValue_left _ _ x h h₀

theorem endpointBoundary_one {Γ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (x : (total (interval Γ)).Elements)
    (h : ((intervalFace Γ false).join (intervalFace Γ true)).holds x)
    (h₁ : (intervalFace Γ true).holds x) :
    (endpointBoundary B a₀ a₁).val x h = (endpointSection B true a₁).val x h₁ :=
  glueValue_right _ _ (fun x h₀ h₁ => (intervalFace_disjoint x h₀ h₁).elim) x h h₁

def pathBoundaryFace {Γ : Context.{u}} (φ : Subcontext Γ) : Subcontext (total (interval Γ)) :=
  (φ.reindex (projection (interval Γ))).join ((intervalFace Γ false).join (intervalFace Γ true))

theorem PartialSection.pathApp_boundary_compatible {Γ : Context.{u}}
    {B : Family (total (interval Γ))}
    {a₀ : Term (Cartesian.reindex B (endpointSub Γ false))}
    {a₁ : Term (Cartesian.reindex B (endpointSub Γ true))} {φ : Subcontext Γ}
    (s : PartialSection (path B a₀ a₁) φ) : s.pathApp.Compatible (endpointBoundary B a₀ a₁) := by
  intro x h p
  rcases (Subcontext.full_join _ _ x).mp p with h₀ | h₁
  · rw [endpointBoundary_zero B a₀ a₁ x p h₀]
    exact eq_of_heq ((s.pathApp_zero x h h₀).trans (endpointSection_val B false a₀ x h₀).symm)
  · rw [endpointBoundary_one B a₀ a₁ x p h₁]
    exact eq_of_heq ((s.pathApp_one x h h₁).trans (endpointSection_val B true a₁ x h₁).symm)

noncomputable def PartialSection.pathBoundary {Γ : Context.{u}}
    {B : Family (total (interval Γ))}
    {a₀ : Term (Cartesian.reindex B (endpointSub Γ false))}
    {a₁ : Term (Cartesian.reindex B (endpointSub Γ true))} {φ : Subcontext Γ}
    (s : PartialSection (path B a₀ a₁) φ) : PartialSection B (pathBoundaryFace φ) :=
  s.pathApp.glue (endpointBoundary B a₀ a₁) s.pathApp_boundary_compatible

theorem PartialSection.pathBoundary_old {Γ : Context.{u}}
    {B : Family (total (interval Γ))}
    {a₀ : Term (Cartesian.reindex B (endpointSub Γ false))}
    {a₁ : Term (Cartesian.reindex B (endpointSub Γ true))} {φ : Subcontext Γ}
    (s : PartialSection (path B a₀ a₁) φ) (x : (total (interval Γ)).Elements)
    (p : (pathBoundaryFace φ).holds x) (h : (φ.reindex (projection (interval Γ))).holds x) :
    s.pathBoundary.val x p = s.pathApp.val x h := glueValue_left _ _ x p h

theorem PartialSection.pathBoundary_zero {Γ : Context.{u}}
    {B : Family (total (interval Γ))}
    {a₀ : Term (Cartesian.reindex B (endpointSub Γ false))}
    {a₁ : Term (Cartesian.reindex B (endpointSub Γ true))} {φ : Subcontext Γ}
    (s : PartialSection (path B a₀ a₁) φ) (x : (total (interval Γ)).Elements)
    (p : (pathBoundaryFace φ).holds x) (h₀ : (intervalFace Γ false).holds x) :
    HEq (s.pathBoundary.val x p) (a₀.val ((projection (interval Γ)).mapElements.obj x)) := by
  have h := (Subcontext.full_join (intervalFace Γ false) (intervalFace Γ true) x).mpr (Or.inl h₀)
  exact (heq_of_eq (glueValue_right _ _ s.pathApp_boundary_compatible x p h)).trans
    ((heq_of_eq (endpointBoundary_zero B a₀ a₁ x h h₀)).trans (endpointSection_val B false a₀ x h₀))

theorem PartialSection.pathBoundary_one {Γ : Context.{u}}
    {B : Family (total (interval Γ))}
    {a₀ : Term (Cartesian.reindex B (endpointSub Γ false))}
    {a₁ : Term (Cartesian.reindex B (endpointSub Γ true))} {φ : Subcontext Γ}
    (s : PartialSection (path B a₀ a₁) φ) (x : (total (interval Γ)).Elements)
    (p : (pathBoundaryFace φ).holds x) (h₁ : (intervalFace Γ true).holds x) :
    HEq (s.pathBoundary.val x p) (a₁.val ((projection (interval Γ)).mapElements.obj x)) := by
  have h := (Subcontext.full_join (intervalFace Γ false) (intervalFace Γ true) x).mpr (Or.inr h₁)
  exact (heq_of_eq (glueValue_right _ _ s.pathApp_boundary_compatible x p h)).trans
    ((heq_of_eq (endpointBoundary_one B a₀ a₁ x h h₁)).trans (endpointSection_val B true a₁ x h₁))

theorem endpointBoundary_reindex {Γ Δ : Context.{u}} (B : Family (total (interval Γ)))
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) (σ : Δ ⟶ Γ) :
    (endpointBoundary B a₀ a₁).reindex (liftSub (interval Γ) σ) =
      endpointBoundary (reindex B (liftSub (interval Γ) σ)) (Term.reindex a₀ σ) (Term.reindex a₁ σ) := by
  exact (PartialSection.glue_reindex _ _ _ (liftSub (interval Γ) σ)).trans
    (PartialSection.glue_congr (endpointSection_reindex B false a₀ σ)
      (endpointSection_reindex B true a₁ σ) _ _)

theorem PartialSection.pathBoundary_reindex {Γ Δ : Context.{u}}
    {B : Family (total (interval Γ))}
    {a₀ : Term (Cartesian.reindex B (endpointSub Γ false))}
    {a₁ : Term (Cartesian.reindex B (endpointSub Γ true))} {φ : Subcontext Γ}
    (s : PartialSection (path B a₀ a₁) φ) (σ : Δ ⟶ Γ) :
    s.pathBoundary.reindex (liftSub (interval Γ) σ) =
      ((s.reindex σ).map (pathReindex B a₀ a₁ σ)).pathBoundary := by
  exact (PartialSection.glue_reindex _ _ _ (liftSub (interval Γ) σ)).trans
    (PartialSection.glue_congr (s.pathApp_reindex σ).symm
      (endpointBoundary_reindex B a₀ a₁ σ) _ _)

theorem pathBoundaryFace_endpoint {Γ : Context.{u}} (φ : Subcontext Γ) (b : Bool)
    (x : Γ.Elements) : (pathBoundaryFace φ).holds ((endpointSub Γ b).mapElements.obj x) := by
  apply (Subcontext.full_join _ _ _).mpr
  apply Or.inr
  apply (Subcontext.full_join _ _ _).mpr
  cases b
  · exact Or.inl ((intervalFace_iff false _).mpr rfl)
  · exact Or.inr ((intervalFace_iff true _).mpr rfl)




def pathFillingContext {Γ Δ : Context.{u}} (p : total (interval Δ) ⟶ Γ) :
    total (interval (total (interval Δ))) ⟶ total (interval Γ) :=
  swapIntervals Δ ≫ liftSub (interval Γ) p

noncomputable def pathFillingBox {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))}
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (path B a₀ a₁) p) φ r) :
    OpenBox (reindex B (pathFillingContext p)) (pathBoundaryFace φ) (Term.reindex r (projection (interval Δ))) where
  tube := ((b.tube.map (pathReindex B a₀ a₁ p)).pathBoundary).reindex (swapIntervals Δ)
  base := pathApp (Term.map (pathReindex B a₀ a₁ (graph r ≫ p)) b.base)
  boundary x h := by
    rcases x with @⟨I,⟨δ,j⟩⟩
    let y := Δ.elementsMk I δ
    let s := b.tube.map (pathReindex B a₀ a₁ p)
    let z := (total (interval (total (interval Δ)))).elementsMk I
      ⟨⟨δ,r.val y⟩,j⟩
    have hp : (pathBoundaryFace (φ.reindex (projection (interval Δ)))).holds z := h
    rcases (Subcontext.full_join _ _ ((total (interval Δ)).elementsMk I ⟨δ,j⟩)).mp h with hφ | he
    · have hv := s.pathBoundary_old z hp hφ
      exact hv.trans (congrArg (fun v => v.val.val (𝟙 _) j) (b.boundary y hφ))
    · rcases (Subcontext.full_join _ _ ((total (interval Δ)).elementsMk I ⟨δ,j⟩)).mp he with h₀ | h₁
      · have hr := (intervalFace_iff false
          ((total (interval Δ)).elementsMk I ⟨δ,j⟩)).mp h₀
        change j = (endpoint Δ false).val y at hr
        subst j
        exact eq_of_heq ((s.pathBoundary_zero z hp h₀).trans
          (heq_of_eq ((b.base.val y).property (𝟙 _)).1).symm)
      · have hr := (intervalFace_iff true
          ((total (interval Δ)).elementsMk I ⟨δ,j⟩)).mp h₁
        change j = (endpoint Δ true).val y at hr
        subst j
        exact eq_of_heq ((s.pathBoundary_one z hp h₁).trans
          (heq_of_eq ((b.base.val y).property (𝟙 _)).2).symm)

theorem pathFillingBox_reindex {Γ Δ Θ : Context.{u}} {B : Family (total (interval Γ))}
    {a₀ : Term (reindex B (endpointSub Γ false))}
    {a₁ : Term (reindex B (endpointSub Γ true))}
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (path B a₀ a₁) p) φ r) (σ : Θ ⟶ Δ) :
    pathFillingBox (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ) =
      (pathFillingBox p φ r b).reindex (liftSub (interval Δ) σ) := by
  apply OpenBox.ext
  · let s := b.tube.map (pathReindex B a₀ a₁ p)
    exact (congrArg (fun s => s.reindex (swapIntervals Θ))
      (s.pathBoundary_reindex (liftSub (interval Δ) σ))).symm
  · exact pathApp_reindex
      (Term.map (pathReindex B a₀ a₁ (graph r ≫ p)) b.base) σ




section
variable {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
  {a₀ : Term (reindex B (endpointSub Γ false))}
  {a₁ : Term (reindex B (endpointSub Γ true))}
  (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
  (b : OpenBox (reindex (path B a₀ a₁) p) φ r)
  (t : Term (reindex B (pathFillingContext p)))
  (ht : (pathFillingBox p φ r b).Fills t)

include ht
theorem pathFillingBody_zero :
    (Term.reindex ((Term.reindex t (swapIntervals Δ))) (endpointSub (total (interval Δ)) false)) = (Term.reindex a₀ p) := by
  apply Term.ext
  intro x
  rcases x with @⟨I,⟨δ,i⟩⟩
  let y := Δ.elementsMk I δ
  let z := (total (interval (total (interval Δ)))).elementsMk I
    ⟨⟨δ,(endpoint Δ false).val y⟩,i⟩
  have hp := pathBoundaryFace_endpoint φ false y
  have h := ht.2 z hp
  let s := b.tube.map (pathReindex B a₀ a₁ p)
  have hz : (intervalFace (total (interval Δ)) false).holds ((swapIntervals Δ).mapElements.obj z) :=
    (intervalFace_iff false _).mpr rfl
  exact eq_of_heq ((heq_of_eq h).trans (s.pathBoundary_zero ((swapIntervals Δ).mapElements.obj z) hp hz))

theorem pathFillingBody_one :
    (Term.reindex ((Term.reindex t (swapIntervals Δ))) (endpointSub (total (interval Δ)) true)) = (Term.reindex a₁ p) := by
  apply Term.ext
  intro x
  rcases x with @⟨I,⟨δ,i⟩⟩
  let y := Δ.elementsMk I δ
  let z := (total (interval (total (interval Δ)))).elementsMk I
    ⟨⟨δ,(endpoint Δ true).val y⟩,i⟩
  have hp := pathBoundaryFace_endpoint φ true y
  have h := ht.2 z hp
  let s := b.tube.map (pathReindex B a₀ a₁ p)
  have hz : (intervalFace (total (interval Δ)) true).holds ((swapIntervals Δ).mapElements.obj z) :=
    (intervalFace_iff true _).mpr rfl
  exact eq_of_heq ((heq_of_eq h).trans (s.pathBoundary_one ((swapIntervals Δ).mapElements.obj z) hp hz))

def pathFillingBody_path : Term (path (reindex B (liftSub (interval Γ) p)) ((Term.reindex a₀ p)) ((Term.reindex a₁ p))) :=
  pathLam ((Term.reindex t (swapIntervals Δ))) (pathFillingBody_zero p φ r b t ht) (pathFillingBody_one p φ r b t ht)

end



section
variable {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
  {a₀ : Term (reindex B (endpointSub Γ false))}
  {a₁ : Term (reindex B (endpointSub Γ true))}
  (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
  (b : OpenBox (reindex (path B a₀ a₁) p) φ r)
  (t : Term (reindex B (pathFillingContext p)))
  (ht : (pathFillingBox p φ r b).Fills t)

def pathFillingResult : Term (reindex (path B a₀ a₁) p) :=
  Term.map (pathReindexIso B a₀ a₁ p).inv (pathFillingBody_path p φ r b t ht)

theorem pathFillingResult_normalize :
    Term.map (pathReindex B a₀ a₁ p) (pathFillingResult p φ r b t ht) =
      pathFillingBody_path p φ r b t ht :=
  Term.map_iso_roundtrip (pathReindexIso B a₀ a₁ p).symm _

theorem pathFillingResult_cap :
    (Term.reindex (pathFillingResult p φ r b t ht) (graph r)) = b.base := by
  apply Term.map_injective_of_iso (pathReindexIso B a₀ a₁ (graph r ≫ p))
  apply pathApp_injective
  have hn := congrArg (fun s => pathApp
    (Term.map (pathReindex (reindex B (liftSub (interval Γ) p))
      ((Term.reindex a₀ p)) ((Term.reindex a₁ p)) (graph r))
      ((Term.reindex s (graph r))))) (pathFillingResult_normalize p φ r b t ht)
  exact hn.trans ht.1

theorem pathFillingResult_tube (x : (total (interval Δ)).Elements)
    (hx : (φ.reindex (projection (interval Δ))).holds x) :
    (pathFillingResult p φ r b t ht).val x = b.tube.val x hx := by
  apply ((pathReindexIso B a₀ a₁ p).app x).toEquiv.injective
  let s := b.tube.map (pathReindex B a₀ a₁ p)
  change (Term.map (pathReindex B a₀ a₁ p) (pathFillingResult p φ r b t ht)).val x = s.val x hx
  calc
    _ = (pathFillingBody_path p φ r b t ht).val x :=
      congrArg (fun v => v.val x) (pathFillingResult_normalize p φ r b t ht)
    _ = _ := by
      apply Subtype.ext
      apply PiElement.ext
      intro y f j
      have hy := (φ.reindex (projection (interval Δ))).natural f hx
      let z := extendObj (interval (total (interval Δ))) y j
      have hz : (pathBoundaryFace φ).holds
          ((projection (interval (total (interval Δ)))).mapElements.obj
            ((swapIntervals Δ).mapElements.obj z)) :=
        (Subcontext.full_join _ _ _).mpr (Or.inl hy)
      have hfill := ht.2 ((swapIntervals Δ).mapElements.obj z) hz
      have hold := s.pathBoundary_old z hz hy
      have hprop : (s.val x hx).val.val f j = (s.val y hy).val.val (𝟙 _) j := by
        have h := congrArg (fun v => v.val.val (𝟙 _) j) (s.natural f hx)
        change (s.val x hx).val.val (f ≫ 𝟙 _) j = _ at h
        simpa only [Category.comp_id] using h
      exact hfill.trans (hold.trans hprop.symm)

theorem pathFillingResult_fills : b.Fills (pathFillingResult p φ r b t ht) :=
  ⟨pathFillingResult_cap p φ r b t ht, pathFillingResult_tube p φ r b t ht⟩

theorem pathFillingResult_congr (t' : Term (reindex B (pathFillingContext p)))
    (ht' : (pathFillingBox p φ r b).Fills t') (h : t = t') :
    pathFillingResult p φ r b t ht = pathFillingResult p φ r b t' ht' := by
  cases h
  rfl

theorem pathFillingResult_reindex {Θ : Context.{u}} (σ : Θ ⟶ Δ)
    (ht' : (pathFillingBox (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ)).Fills
      ((Term.reindex t (liftSub (interval (total (interval Δ))) (liftSub (interval Δ) σ))))) :
    pathFillingResult (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ)
      ((Term.reindex t (liftSub (interval (total (interval Δ))) (liftSub (interval Δ) σ)))) ht' =
      (Term.reindex (pathFillingResult p φ r b t ht) (liftSub (interval Δ) σ)) := by
  apply Term.map_injective_of_iso (pathReindexIso B a₀ a₁ (liftSub (interval Δ) σ ≫ p))
  apply pathApp_injective
  have hn := congrArg (fun s => pathApp
    (Term.map (pathReindex (reindex B (liftSub (interval Γ) p))
      ((Term.reindex a₀ p)) ((Term.reindex a₁ p)) (liftSub (interval Δ) σ))
      ((Term.reindex s (liftSub (interval Δ) σ))))) (pathFillingResult_normalize p φ r b t ht)
  have hn' := congrArg pathApp (pathFillingResult_normalize
    (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ)
    ((Term.reindex t (liftSub (interval (total (interval Δ))) (liftSub (interval Δ) σ)))) ht')
  exact hn'.trans hn.symm

end



noncomputable def pathFilling {Γ : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) : Filling (path B a₀ a₁) where
  fill {Δ} p φ r b := pathFillingResult p φ r b
    (F.fill (pathFillingContext p) (pathBoundaryFace φ) (Term.reindex r (projection (interval Δ))) (pathFillingBox p φ r b))
    (hF.fills (pathFillingContext p) (pathBoundaryFace φ) (Term.reindex r (projection (interval Δ))) (pathFillingBox p φ r b))

theorem pathFilling_fills {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true)))
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (path B a₀ a₁) p) φ r) :
    b.Fills ((pathFilling F hF a₀ a₁).fill p φ r b) :=
  pathFillingResult_fills p φ r b _ (hF.fills _ _ _ _)

theorem pathFilling_uniform {Γ Δ Θ : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true)))
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ))
    (b : OpenBox (reindex (path B a₀ a₁) p) φ r) (σ : Θ ⟶ Δ) :
    (pathFilling F hF a₀ a₁).fill (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ) =
      (Term.reindex ((pathFilling F hF a₀ a₁).fill p φ r b) (liftSub (interval Δ) σ)) := by
  let t := F.fill (pathFillingContext p) (pathBoundaryFace φ) (Term.reindex r (projection (interval Δ))) (pathFillingBox p φ r b)
  have ht : (pathFillingBox p φ r b).Fills t := hF.fills _ _ _ _
  have ht' : (pathFillingBox (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ)).Fills
      ((Term.reindex t (liftSub (interval (total (interval Δ))) (liftSub (interval Δ) σ)))) :=
    (pathFillingBox_reindex p φ r b σ).symm ▸ (ht.reindex (liftSub (interval Δ) σ))
  have he : F.fill (pathFillingContext (liftSub (interval Δ) σ ≫ p)) (pathBoundaryFace (φ.reindex σ)) (Term.reindex (Term.reindex r σ) (projection (interval Θ)))
      (pathFillingBox (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ)) =
      (Term.reindex t (liftSub (interval (total (interval Δ))) (liftSub (interval Δ) σ))) :=
    (congrArg (F.fill (pathFillingContext (liftSub (interval Δ) σ ≫ p))
      (pathBoundaryFace (φ.reindex σ)) (Term.reindex (Term.reindex r σ) (projection (interval Θ)))) (pathFillingBox_reindex p φ r b σ)).trans
        (hF.uniform (pathFillingContext p) (pathBoundaryFace φ) (Term.reindex r (projection (interval Δ))) (pathFillingBox p φ r b)
          (liftSub (interval Δ) σ))
  exact (pathFillingResult_congr (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ)
    _ (hF.fills _ _ _ _) _ ht' he).trans (pathFillingResult_reindex p φ r b t ht σ ht')

theorem pathFilling_lawful {Γ : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful)
    (a₀ : Term (reindex B (endpointSub Γ false)))
    (a₁ : Term (reindex B (endpointSub Γ true))) : (pathFilling F hF a₀ a₁).Lawful where
  fills := pathFilling_fills F hF a₀ a₁
  uniform := pathFilling_uniform F hF a₀ a₁


end SquareKit.Cubical.Cartesian
