import Applications.Orbifolds.LocalBranchSum
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Separation.Hausdorff

/-! Proper anchors with locally invertible sources admit finite smooth branches. -/
noncomputable section
open Set TopologicalSpace Topology
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
  {s : A → X} {t : A → Y}

omit [TopologicalSpace Y] in
/-- Local source injectivity makes every actual endpoint fiber discrete. -/
theorem anchorFiber_discrete (hs : IsLocalDiffeomorph IA IX ∞ s) (x : X) (y : Y) :
    IsDiscrete {a | s a = x ∧ t a = y} := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro a ha
  obtain ⟨q, hqa, heq⟩ := hs a
  refine ⟨q.source, q.open_source, ?_⟩
  ext b
  constructor
  · intro hb
    apply mem_singleton_iff.mpr
    apply q.toPartialEquiv.injOn hb.1 hqa
    rw [← heq hb.1, ← heq hqa, hb.2.1, ha.1]
  · rintro rfl
    exact ⟨hqa, ha⟩

/-- Compactness comes from the supplied proper anchor, not from the manifolds. -/
theorem anchorFiber_finite (hs : IsLocalDiffeomorph IA IX ∞ s)
    (hp : IsProperMap (fun a => (s a, t a))) (x : X) (y : Y) :
    {a | s a = x ∧ t a = y}.Finite := by
  have hc : IsCompact {a | s a = x ∧ t a = y} := by
    simpa only [Set.preimage, mem_singleton_iff, Prod.mk.injEq] using
      hp.isCompact_preimage (isCompact_singleton (x := (x,y)))
  exact hc.finite (anchorFiber_discrete hs x y)

/-- Closedness excludes all arrows outside the chosen open chart neighborhoods. -/
theorem rectangle_of_fiber_subset (hp : IsProperMap (fun a => (s a,t a)))
    (x : X) (y : Y) (W : Opens A)
    (hW : ∀ a, s a = x → t a = y → a ∈ W) :
    ∃ U : Opens X, ∃ V : Opens Y, x ∈ U ∧ y ∈ V ∧
      ∀ a, s a ∈ U → t a ∈ V → a ∈ W := by
  have hc : IsClosed ((fun a => (s a,t a)) '' (W : Set A)ᶜ) :=
    hp.isClosedMap _ W.isOpen.isClosed_compl
  have hn : (x,y) ∈ ((fun a => (s a,t a)) '' (W : Set A)ᶜ)ᶜ := by
    rintro ⟨a,ha,he⟩
    exact ha (hW a (congrArg Prod.fst he) (congrArg Prod.snd he))
  obtain ⟨U,V,hU,hx,hV,hy,hUV⟩ := mem_nhds_prod_iff'.mp (hc.isOpen_compl.mem_nhds hn)
  refine ⟨⟨U,hU⟩, ⟨V,hV⟩, hx,hy,?_⟩
  intro a hsa hta
  by_contra ha
  exact hUV ⟨hsa,hta⟩ ⟨a,ha,rfl⟩

section ChartConstruction
variable {J : Type*} (q : J → PartialDiffeomorph IA IX A X ∞)
  (heq : ∀ i, EqOn s (q i) (q i).source)
  (hd : Pairwise fun i j => Disjoint (q i).source (q j).source)
  (hs : ContMDiff IA IX ∞ s) (ht : ContMDiff IA IY ∞ t)
  (U : Opens X) (V : Opens Y)
  (hc : ∀ a, s a ∈ U → t a ∈ V → ∃ i, a ∈ (q i).source)

/-- The rectangle preimage with its ordinary inherited topology. -/
def arrowRegion : Opens A :=
  ⟨{a | s a ∈ U ∧ t a ∈ V}, (U.isOpen.preimage hs.continuous).inter
    (V.isOpen.preimage ht.continuous)⟩

/-- Restriction of independently supplied disjoint source charts. -/
def diagramOfCharts : Diagram IA IX s t U V J where
  piece i := ⟨(restrictChart (q i) (arrowRegion hs ht U V)).source,
    (restrictChart (q i) (arrowRegion hs ht U V)).open_source⟩
  domain i := ⟨(restrictChart (q i) (arrowRegion hs ht U V)).target,
    (restrictChart (q i) (arrowRegion hs ht U V)).open_target⟩
  sourceEquiv i := chartDiffeomorph (restrictChart (q i) (arrowRegion hs ht U V))
  source_eq i a := (heq i a.property.1).symm
  domain_le i x hx := by
    have ha := (restrictChart (q i) (arrowRegion hs ht U V)).toPartialEquiv.map_target hx
    have he := (restrictChart (q i) (arrowRegion hs ht U V)).toPartialEquiv.right_inv hx
    have hsa : s ((q i).invFun x) ∈ U := ha.2.1
    have hsx : s ((q i).invFun x) = x := (heq i ha.1).trans he
    rwa [hsx] at hsa
  target_mem i a := a.property.2.2
  disjoint i j hij := Opens.coe_disjoint.mp ((hd hij).mono inter_subset_left inter_subset_left)
  covers a := by
    constructor
    · intro ha
      obtain ⟨i,hi⟩ := hc a ha.1 ha.2
      exact ⟨i,hi,ha⟩
    · rintro ⟨i,hi⟩
      exact hi.2

end ChartConstruction
/-- Restrict a partial chart to an open set contained in its source, using
that set itself as the source rather than an intersection presentation. -/
def chartOn (q : PartialDiffeomorph IA IX A X ∞) (P : Opens A)
    (hP : (P : Set A) ⊆ q.source) : PartialDiffeomorph IA IX A X ∞ where
  toFun := q
  invFun := q.invFun
  source := P
  target := q.target ∩ q.invFun ⁻¹' P
  map_source' a ha := ⟨q.toPartialEquiv.map_source (hP ha), by
    change q.invFun (q a) ∈ P
    have he : q.invFun (q a) = a := q.toPartialEquiv.left_inv (hP ha)
    rw [he]
    exact ha⟩
  map_target' _ hx := hx.2
  left_inv' _ ha := q.toPartialEquiv.left_inv (hP ha)
  right_inv' _ hx := q.toPartialEquiv.right_inv hx.1
  open_source := P.isOpen
  open_target := (restrictChart q P).open_target
  contMDiffOn_toFun := q.contMDiffOn_toFun.mono hP
  contMDiffOn_invFun := q.contMDiffOn_invFun.mono inter_subset_left

/-- Additional target inverses on an existing source-branch diagram. -/
structure Bisections {J : Type*} {U : Opens X} {V : Opens Y}
    (D : Diagram IA IX s t U V J) (IY : ModelWithCorners ℝ EY HY) where
  targetDomain : J → Opens Y
  targetEquiv : ∀ i, Diffeomorph IA IY (D.piece i) (targetDomain i) ∞
  target_eq : ∀ i (a : D.piece i), (targetEquiv i a).val = t a.val
  targetDomain_le : ∀ i, targetDomain i ≤ V

namespace Bisections
variable {J : Type*} {U : Opens X} {V : Opens Y} {D : Diagram IA IX s t U V J}
  (B : Bisections D IY)

def branchDiffeomorph (i : J) : Diffeomorph IX IY (D.domain i) (B.targetDomain i) ∞ :=
  (D.sourceEquiv i).symm.trans (B.targetEquiv i)

theorem branchDiffeomorph_eq (i : J) (u : D.domain i) :
    (B.branchDiffeomorph i u).val = (D.branch i u).val :=
  B.target_eq i _

end Bisections

section Proper
variable [T2Space A]

/-- Disjoint source charts can also be chosen inside independently supplied
neighborhoods, which permits the bisection specialization. -/
theorem exists_diagram_subordinate (hs : IsLocalDiffeomorph IA IX ∞ s)
    (ht : ContMDiff IA IY ∞ t) (hp : IsProperMap (fun a => (s a,t a)))
    (x : X) (y : Y)
    (O : {a // s a = x ∧ t a = y} → Opens A)
    (hO : ∀ a, a.val ∈ O a) :
    ∃ U : Opens X, ∃ V : Opens Y, x ∈ U ∧ y ∈ V ∧
      ∃ D : Diagram IA IX s t U V {a // s a = x ∧ t a = y},
        ∀ i, D.piece i ≤ O i := by
  classical
  let F := {a // s a = x ∧ t a = y}
  have hf := anchorFiber_finite hs hp x y
  obtain ⟨W,hW,hdW⟩ := hf.t2_separation
  choose q hqa hqe using (fun a : F => hs a.val)
  let r (a : F) := restrictChart (q a)
    (⟨W a.val ∩ O a, (hW a.val).2.inter (O a).isOpen⟩ : Opens A)
  have hr (a : F) : a.val ∈ (r a).source :=
    ⟨hqa a, (hW a.val).1, hO a⟩
  have he (a : F) : EqOn s (r a) (r a).source :=
    fun _ hb => hqe a hb.1
  have hd : Pairwise fun a b : F => Disjoint (r a).source (r b).source := by
    intro a b hab
    exact (hdW a.property b.property (fun h => hab (Subtype.ext h))).mono
      (fun _ h => h.2.1) (fun _ h => h.2.1)
  let all : Opens A := ⟨⋃ a : F, (r a).source, isOpen_iUnion (fun a => (r a).open_source)⟩
  have hall (a : A) (hsa : s a = x) (hta : t a = y) : a ∈ all :=
    mem_iUnion.mpr ⟨⟨a,hsa,hta⟩, hr ⟨a,hsa,hta⟩⟩
  obtain ⟨U,V,hx,hy,hUV⟩ := rectangle_of_fiber_subset hp x y all hall
  have hc (a : A) (hsa : s a ∈ U) (hta : t a ∈ V) : ∃ i, a ∈ (r i).source :=
    mem_iUnion.mp (hUV a hsa hta)
  refine ⟨U,V,hx,hy,diagramOfCharts r he hd hs.contMDiff ht U V hc,?_⟩
  intro i a ha
  exact ha.1.2.2

/-- The ordinary local decomposition uses no supplied fiber enumeration. -/
theorem exists_diagram (hs : IsLocalDiffeomorph IA IX ∞ s)
    (ht : ContMDiff IA IY ∞ t) (hp : IsProperMap (fun a => (s a,t a)))
    (x : X) (y : Y) :
    ∃ U : Opens X, ∃ V : Opens Y, x ∈ U ∧ y ∈ V ∧
      Nonempty (Diagram IA IX s t U V {a // s a = x ∧ t a = y}) := by
  obtain ⟨U,V,hx,hy,D,_⟩ := exists_diagram_subordinate hs ht hp x y
    (fun _ => ⊤) (fun _ => mem_univ _)
  exact ⟨U,V,hx,hy,⟨D⟩⟩

/-- A finite numbered presentation is derived from the actual central fiber. -/
theorem exists_fin_diagram (hs : IsLocalDiffeomorph IA IX ∞ s)
    (ht : ContMDiff IA IY ∞ t) (hp : IsProperMap (fun a => (s a,t a)))
    (x : X) (y : Y) :
    ∃ U : Opens X, ∃ V : Opens Y, x ∈ U ∧ y ∈ V ∧
      ∃ n : ℕ, Nonempty (Diagram IA IX s t U V (Fin n)) := by
  classical
  let : Fintype {a : A // s a = x ∧ t a = y} := (anchorFiber_finite hs hp x y).fintype
  obtain ⟨U,V,hx,hy,⟨D⟩⟩ := exists_diagram hs ht hp x y
  exact ⟨U,V,hx,hy,_,⟨D.finDiagram⟩⟩

/-- When the central fiber is empty, the constructed whole rectangle is empty. -/
theorem exists_empty_diagram (hs : IsLocalDiffeomorph IA IX ∞ s)
    (ht : ContMDiff IA IY ∞ t) (hp : IsProperMap (fun a => (s a,t a)))
    (x : X) (y : Y) (hempty : ∀ a, ¬(s a = x ∧ t a = y)) :
    ∃ U : Opens X, ∃ V : Opens Y, x ∈ U ∧ y ∈ V ∧
      ∃ D : Diagram IA IX s t U V {a // s a = x ∧ t a = y}, D.region = ⊥ := by
  obtain ⟨U,V,hx,hy,⟨D⟩⟩ := exists_diagram hs ht hp x y
  refine ⟨U,V,hx,hy,D,?_⟩
  apply le_antisymm _ bot_le
  intro a ha
  obtain ⟨i,_⟩ := (D.covers a).mp ha
  exact (hempty i.val i.property).elim

/-- A proper anchor with both endpoints locally invertible has actual smooth
bisections. No common target image is imposed. -/
theorem exists_bisection_diagram (hs : IsLocalDiffeomorph IA IX ∞ s)
    (ht : IsLocalDiffeomorph IA IY ∞ t) (hp : IsProperMap (fun a => (s a,t a)))
    (x : X) (y : Y) :
    ∃ U : Opens X, ∃ V : Opens Y, x ∈ U ∧ y ∈ V ∧
      ∃ D : Diagram IA IX s t U V {a // s a = x ∧ t a = y}, Nonempty (Bisections D IY) := by
  classical
  let F := {a // s a = x ∧ t a = y}
  choose q hqa hqe using (fun a : F => ht a.val)
  obtain ⟨U,V,hx,hy,D,hD⟩ := exists_diagram_subordinate hs ht.contMDiff hp x y
    (fun a => ⟨(q a).source,(q a).open_source⟩) hqa
  let r (i : F) := chartOn (q i) (D.piece i) (hD i)
  refine ⟨U,V,hx,hy,D,⟨?_⟩⟩
  refine { targetDomain := fun i => ⟨(r i).target,(r i).open_target⟩
           targetEquiv := fun i => chartDiffeomorph (r i)
           target_eq := ?_
           targetDomain_le := ?_ }
  · intro i a
    exact (hqe i (hD i a.property)).symm
  · intro i z hz
    have ha := (r i).toPartialEquiv.map_target hz
    have he := (r i).toPartialEquiv.right_inv hz
    have hm := D.target_mem i ⟨(r i).invFun z,ha⟩
    have htz : t ((r i).invFun z) = z := (hqe i (hD i ha)).trans he
    rwa [htz] at hm

end Proper
end Orbifolds.LocalBranches
