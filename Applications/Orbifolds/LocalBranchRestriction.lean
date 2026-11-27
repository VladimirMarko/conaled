import Applications.Orbifolds.LocalBranches

/-! Endpoint fibers and restrictions of actual smooth branch diagrams. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Orbifolds.LocalBranches
variable {EA EX EY HA HX HY A X Y : Type*}
  [NormedAddCommGroup EA] [NormedSpace ℝ EA]
  [NormedAddCommGroup EX] [NormedSpace ℝ EX]
  [NormedAddCommGroup EY] [NormedSpace ℝ EY]
  [TopologicalSpace HA] [TopologicalSpace HX] [TopologicalSpace HY]
  [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace HA A] [ChartedSpace HX X] [ChartedSpace HY Y]
  {IA : ModelWithCorners ℝ EA HA} {IX : ModelWithCorners ℝ EX HX}
  {IY : ModelWithCorners ℝ EY HY}
namespace Diagram
variable {s : A → X} {t : A → Y} {U : Opens X} {V : Opens Y} {J : Type*}
  (D : Diagram IA IX s t U V J)

/-- Complete endpoint fibers, including the actual arrow and both equations. -/
def fiberEquiv (x : U) (y : V) :
    {a : A // s a = x.val ∧ t a = y.val} ≃
      Σ i, {u : D.domain i // D.domainInclusion i u = x ∧ D.branch i u = y} where
  toFun a := by
    let r : D.region := ⟨a.val, by simpa only [a.property.1] using x.property, by simpa only [a.property.2] using y.property⟩
    exact ⟨(D.decompose r).1, (D.decompose r).2,
      (D.decompose_source r).trans (Subtype.ext a.property.1),
      (D.decompose_target r).trans (Subtype.ext a.property.2)⟩
  invFun z := ⟨(D.assemble z.1 z.2.val).val,
    congrArg Subtype.val ((D.source_assemble z.1 z.2.val).trans z.2.property.1),
    congrArg Subtype.val z.2.property.2⟩
  left_inv a := by
    apply Subtype.ext
    change (D.assemble _ _).val = a.val
    exact congrArg (fun b : D.region => b.val) (D.assemble_decompose _)
  right_inv z := by
    rcases z with ⟨i,u,hx,hy⟩
    have h := D.decompose_assemble i u
    dsimp only
    have hh : ∀ (z : Σ i, D.domain i) (hz :
        D.domainInclusion z.1 z.2 = x ∧ D.branch z.1 z.2 = y),
        z = ⟨i,u⟩ → (⟨z.1, ⟨z.2,hz⟩⟩ : Σ i,
          {u : D.domain i // D.domainInclusion i u = x ∧ D.branch i u = y}) = ⟨i,⟨u,hx,hy⟩⟩ := by
      intro z hz he
      subst z
      rfl
    apply hh
    exact h

/-- Every open part of a piece has an open source image. -/
def restrictedDomain (i : J) (P : Opens A) (hP : P ≤ D.piece i) : Opens X :=
  ⟨s '' P, by
    have he : s '' (P : Set A) = Subtype.val ''
        ((D.sourceEquiv i) '' ((Subtype.val : D.piece i → A) ⁻¹' P)) := by
      ext x
      constructor
      · rintro ⟨a,ha,rfl⟩
        refine ⟨D.sourceEquiv i ⟨a,hP ha⟩, ⟨⟨a,hP ha⟩,ha,rfl⟩,?_⟩
        exact D.source_eq i _
      · rintro ⟨x,⟨a,ha,rfl⟩,rfl⟩
        exact ⟨a.val,ha,(D.source_eq i a).symm⟩
    rw [he]
    exact (D.domain i).isOpenEmbedding'.isOpenMap _
      ((D.sourceEquiv i).toHomeomorph.isOpenMap _
        (P.isOpen.preimage continuous_subtype_val))⟩

theorem restrictedDomain_le (i : J) (P : Opens A) (hP : P ≤ D.piece i) :
    D.restrictedDomain i P hP ≤ D.domain i := by
  rintro x ⟨a,ha,rfl⟩
  rw [← D.source_eq i ⟨a,hP ha⟩]
  exact (D.sourceEquiv i ⟨a,hP ha⟩).property

/-- Restrict the actual source diffeomorphism to any open part of its piece. -/
def restrictedSourceEquiv (i : J) (P : Opens A) (hP : P ≤ D.piece i) :
    Diffeomorph IA IX P (D.restrictedDomain i P hP) ∞ where
  toFun a := ⟨s a.val, ⟨a.val,a.property,rfl⟩⟩
  invFun x := ⟨((D.sourceEquiv i).symm
    ⟨x.val,D.restrictedDomain_le i P hP x.property⟩).val, by
      obtain ⟨a,ha,he⟩ := x.property
      have hx : (⟨x.val,D.restrictedDomain_le i P hP x.property⟩ : D.domain i) =
          D.sourceEquiv i ⟨a,hP ha⟩ := Subtype.ext (he.symm.trans (D.source_eq i ⟨a,hP ha⟩).symm)
      rw [hx, Diffeomorph.symm_apply_apply]
      exact ha⟩
  left_inv a := by
    apply Subtype.ext
    have hx : (⟨s a.val, D.restrictedDomain_le i P hP ⟨a.val,a.property,rfl⟩⟩ : D.domain i) =
        D.sourceEquiv i ⟨a.val,hP a.property⟩ := Subtype.ext (D.source_eq i ⟨a.val,hP a.property⟩).symm
    change ((D.sourceEquiv i).symm _).val = a.val
    rw [hx, Diffeomorph.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    exact (D.source_eq i _).symm.trans
      (congrArg Subtype.val ((D.sourceEquiv i).apply_symm_apply _))
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    have h := contMDiff_subtype_val.comp
      ((D.sourceEquiv i).contMDiff_toFun.comp (contMDiff_inclusion (I := IA) hP))
    change ContMDiff IA IX ∞ (fun a : P => s a.val)
    exact h.congr (fun a => (D.source_eq i ⟨a.val,hP a.property⟩).symm)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    change ContMDiff IX IA ∞ (fun x : D.restrictedDomain i P hP =>
      ((D.sourceEquiv i).symm ⟨x.val,D.restrictedDomain_le i P hP x.property⟩).val)
    exact (contMDiff_subtype_val (I := IA) (U := D.piece i)).comp
      ((D.sourceEquiv i).contMDiff_invFun.comp
        (contMDiff_inclusion (I := IX) (D.restrictedDomain_le i P hP)))

section Restrict
variable (hs : ContMDiff IA IX ∞ s) (ht : ContMDiff IA IY ∞ t)
    (U' : Opens X) (V' : Opens Y) (hU : U' ≤ U) (hV : V' ≤ V)

def restrictedPiece (i : J) : Opens A :=
  ⟨{a | a ∈ D.piece i ∧ s a ∈ U' ∧ t a ∈ V'},
    (D.piece i).isOpen.inter ((U'.isOpen.preimage hs.continuous).inter
      (V'.isOpen.preimage ht.continuous))⟩

theorem restrictedPiece_le (i : J) : D.restrictedPiece hs ht U' V' i ≤ D.piece i :=
  fun _ ha => ha.1

/-- Restriction preserves actual inverse maps, permitting empty and partial domains. -/
def restrict : Diagram IA IX s t U' V' J where
  piece := D.restrictedPiece hs ht U' V'
  domain i := D.restrictedDomain i _ (D.restrictedPiece_le hs ht U' V' i)
  sourceEquiv i := D.restrictedSourceEquiv i _ (D.restrictedPiece_le hs ht U' V' i)
  source_eq _ _ := rfl
  domain_le i x hx := by
    obtain ⟨a,ha,rfl⟩ := hx
    exact ha.2.1
  target_mem _ a := a.property.2.2
  disjoint i j hij := Opens.coe_disjoint.mp
    ((Opens.coe_disjoint.mpr (D.disjoint hij)).mono
      (D.restrictedPiece_le hs ht U' V' i) (D.restrictedPiece_le hs ht U' V' j))
  covers a := by
    constructor
    · intro ha
      obtain ⟨i,hi⟩ := (D.covers a).mp ⟨hU ha.1,hV ha.2⟩
      exact ⟨i,hi,ha⟩
    · rintro ⟨i,hi⟩
      exact hi.2

theorem restrict_region_le : (D.restrict hs ht U' V' hU hV).region ≤ D.region :=
  fun _ ha => ⟨hU ha.1,hV ha.2⟩

def restrictRegionMap : (D.restrict hs ht U' V' hU hV).region → D.region :=
  Opens.inclusion (D.restrict_region_le hs ht U' V' hU hV)

def restrictDomainMap (i : J) : (D.restrict hs ht U' V' hU hV).domain i → D.domain i :=
  Opens.inclusion (D.restrictedDomain_le i _ (D.restrictedPiece_le hs ht U' V' i))

@[simp] theorem restrict_assemble (i : J)
    (u : (D.restrict hs ht U' V' hU hV).domain i) :
    D.restrictRegionMap hs ht U' V' hU hV ((D.restrict hs ht U' V' hU hV).assemble i u) =
      D.assemble i (D.restrictDomainMap hs ht U' V' hU hV i u) := rfl

@[simp] theorem restrict_source (a : (D.restrict hs ht U' V' hU hV).region) :
    D.source (D.restrictRegionMap hs ht U' V' hU hV a) =
      Opens.inclusion hU ((D.restrict hs ht U' V' hU hV).source a) := rfl

@[simp] theorem restrict_target (a : (D.restrict hs ht U' V' hU hV).region) :
    D.target (D.restrictRegionMap hs ht U' V' hU hV a) =
      Opens.inclusion hV ((D.restrict hs ht U' V' hU hV).target a) := rfl

end Restrict
end Diagram
end Orbifolds.LocalBranches
