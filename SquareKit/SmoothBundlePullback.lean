import SquareKit.SmoothBundleMorphisms
import SquareKit.SmoothLocalHomeomorph

/-! Ordinary pullbacks of smooth principal bundles, with the fiber-product topology. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SmoothPrincipalBundle
open ManifoldRealization Set Topology
open scoped Manifold ContDiff
variable {n m : ℕ} {G B E B' : Type} [Group G] [MulAction G E]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace B']
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [ChartedSpace (Space m) B']

abbrev Pullback (P : Bundle (n := n) (G := G) (B := B) (E := E)) (f : B' → B) :=
  {z : B' × E // f z.1 = P.projection z.2}

namespace Pullback
attribute [local instance] Classical.propDecidable
variable (P : Bundle (n := n) (G := G) (B := B) (E := E)) (f : B' → B)

def fst (z : Pullback P f) : B' := z.val.1
def snd (z : Pullback P f) : E := z.val.2
omit [TopologicalSpace B'] in
theorem equation (z : Pullback P f) : f (fst P f z) = P.projection (snd P f z) := z.property

theorem continuous_fst : Continuous (fst P f) := _root_.continuous_fst.comp continuous_subtype_val
theorem continuous_snd : Continuous (snd P f) := _root_.continuous_snd.comp continuous_subtype_val

instance : MulAction G (Pullback P f) where
  smul g z := ⟨(z.val.1, g • z.val.2), z.property.trans (P.invariant g z.val.2).symm⟩
  one_smul z := Subtype.ext (Prod.ext rfl (one_smul G z.val.2))
  mul_smul g h z := Subtype.ext (Prod.ext rfl (mul_smul g h z.val.2))

def trivialization (z : Pullback P f) : LocalTrivialization (n := n) (G := G) P.projection :=
  (P.triviality (f (fst P f z))).choose

omit [TopologicalSpace B'] in
theorem mem_base (z : Pullback P f) : f (fst P f z) ∈ (trivialization P f z).base :=
  (P.triviality (f (fst P f z))).choose_spec

def sheetLabel (z : Pullback P f) : G :=
  (trivialization P f z).label (snd P f z) ((equation P f z) ▸ mem_base P f z)

omit [TopologicalSpace B'] in
theorem mem_sheet (z : Pullback P f) :
    snd P f z ∈ ((trivialization P f z).sheet (sheetLabel P f z)).source :=
  (trivialization P f z).label_source _ _

variable (hf : Continuous f)

/-- A pulled-back sheet is a homeomorphism to an open subset of the new base. -/
def sheet (z : Pullback P f) (t : LocalTrivialization (n := n) (G := G) P.projection) (g : G) : OpenPartialHomeomorph (Pullback P f) B' where
  toFun := fst P f
  invFun b := if hb : f b ∈ t.base then
    ⟨(b, (t.sheet g).symm (f b)),
      (t.projection_inverse _ _ hb).symm⟩ else z
  source := snd P f ⁻¹' (t.sheet g).source
  target := f ⁻¹' t.base
  map_source' y hy := by
    have h := (t.sheet g).map_source hy
    rw [t.target] at h
    rwa [t.projection _ _ hy, ← equation P f y] at h
  map_target' b hb := by
    change f b ∈ t.base at hb
    rw [dite_eq_left hb]
    exact t.inverse_source _ _ hb
  left_inv' y hy := by
    have hb : f (fst P f y) ∈ t.base := by
      have h := (t.sheet g).map_source hy
      rw [t.target] at h
      rwa [t.projection _ _ hy, ← equation P f y] at h
    simp only [dite_eq_left hb]
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · rfl
    · exact (congrArg ((t.sheet g).symm)
        (equation P f y)).trans (t.inverse_projection _ _ hy)
  right_inv' b hb := by
    change f b ∈ t.base at hb
    rw [dite_eq_left hb]
    rfl
  open_source := (t.sheet g).open_source.preimage
    (continuous_snd P f)
  open_target := t.isOpen_base.preimage hf
  continuousOn_toFun := (continuous_fst P f).continuousOn
  continuousOn_invFun := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h : Continuous (fun b : f ⁻¹' t.base =>
        (t.sheet g).symm (f b.val)) :=
      ((t.sheet g).continuousOn_symm.comp
        hf.continuousOn (fun b hb => t.target _ ▸ hb)).domRestrict
    have hc : Continuous (fun b : f ⁻¹' t.base =>
        (⟨(b.val, (t.sheet g).symm (f b.val)),
          (t.projection_inverse _ _ b.property).symm⟩ : Pullback P f)) :=
      (continuous_subtype_val.prodMk h).subtype_mk _
    apply hc.congr
    intro b
    dsimp only [Set.domRestrict]
    rw [dite_eq_left (show f b.val ∈ t.base from b.property)]

def localSheet (z : Pullback P f) : OpenPartialHomeomorph (Pullback P f) B' :=
  sheet P f hf z (trivialization P f z) (sheetLabel P f z)

theorem mem_localSheet_source (z : Pullback P f) : z ∈ (localSheet P f hf z).source :=
  mem_sheet P f z

/-- The pullback sheets supply the generic projection atlas. -/
def projectionSheets : SmoothLocalHomeomorph.ProjectionSheets (fst P f) where
  sheet := localSheet P f hf
  mem_source := mem_localSheet_source P f hf
  projection _ := rfl

def chart (z : Pullback P f) : OpenPartialHomeomorph (Pullback P f) (Space m) :=
  (projectionSheets P f hf).chart (n := m) z

@[instance_reducible]
def chartedSpace : ChartedSpace (Space m) (Pullback P f) :=
  (projectionSheets P f hf).chartedSpace

theorem fst_chart_symm (z : Pullback P f) {x : Space m}
    (hx : x ∈ (chart (m := m) P f hf z).target) :
    fst P f ((chart (m := m) P f hf z).symm x) = (chartAt (Space m) (fst P f z)).symm x :=
  (projectionSheets P f hf).proj_chart_symm z hx

theorem chart_transition (z w : Pullback P f) {x : Space m}
    (hx : x ∈ ((chart (m := m) P f hf z).symm.trans (chart (m := m) P f hf w)).source) :
    ((chart (m := m) P f hf z).symm.trans (chart (m := m) P f hf w)) x =
      ((chartAt (Space m) (fst P f z)).symm.trans (chartAt (Space m) (fst P f w))) x :=
  (projectionSheets P f hf).chart_transition z w hx

theorem chart_transition_source (z w : Pullback P f) :
    ((chart (m := m) P f hf z).symm.trans (chart (m := m) P f hf w)).source ⊆
      ((chartAt (Space m) (fst P f z)).symm.trans (chartAt (Space m) (fst P f w))).source :=
  (projectionSheets P f hf).chart_transition_source z w

theorem isManifold [IsManifold (Model m) ∞ B'] :
    letI := chartedSpace (m := m) P f hf
    IsManifold (Model m) ∞ (Pullback P f) :=
  (projectionSheets P f hf).isManifold

theorem smooth_of_fst_at [IsManifold (Model m) ∞ B'] {k : ℕ} {N : Type}
    [TopologicalSpace N] [ChartedSpace (Space k) N]
    (h : N → Pullback P f) (x : N) (hc : ContinuousAt h x)
    (hs : ContMDiffAt (Model k) (Model m) ∞ (fst P f ∘ h) x) :
    letI := chartedSpace (m := m) P f hf
    ContMDiffAt (Model k) (Model m) ∞ h x :=
  (projectionSheets P f hf).smooth_of_proj_at h x hc hs

theorem smooth_of_fst [IsManifold (Model m) ∞ B'] {k : ℕ} {N : Type}
    [TopologicalSpace N] [ChartedSpace (Space k) N]
    (h : N → Pullback P f) (hc : Continuous h)
    (hs : ContMDiff (Model k) (Model m) ∞ (fst P f ∘ h)) :
    letI := chartedSpace (m := m) P f hf
    ContMDiff (Model k) (Model m) ∞ h :=
  (projectionSheets P f hf).smooth_of_proj h hc hs

theorem smooth_fst [IsManifold (Model m) ∞ B'] :
    letI := chartedSpace (m := m) P f hf
    ContMDiff (Model m) (Model m) ∞ (fst P f) :=
  (projectionSheets P f hf).smooth_proj

theorem smooth_iff_fst [IsManifold (Model m) ∞ B'] {k : ℕ} {N : Type}
    [TopologicalSpace N] [ChartedSpace (Space k) N] (h : N → Pullback P f) :
    letI := chartedSpace (m := m) P f hf
    ContMDiff (Model k) (Model m) ∞ h ↔
      Continuous h ∧ ContMDiff (Model k) (Model m) ∞ (fst P f ∘ h) :=
  (projectionSheets P f hf).smooth_iff_proj h

theorem smooth_snd [IsManifold (Model m) ∞ B']
    (hs : ContMDiff (Model m) (Model n) ∞ f) :
    letI := chartedSpace (m := m) P f hf
    ContMDiff (Model m) (Model n) ∞ (snd P f) := by
  let := chartedSpace (m := m) P f hf
  intro z
  have hi := ((trivialization P f z).smooth_inverse (sheetLabel P f z)).contMDiffAt
    ((trivialization P f z).isOpen_base.mem_nhds (mem_base P f z))
  have h := hi.comp z ((hs.comp (smooth_fst P f hf)) z)
  apply h.congr_of_eventuallyEq
  filter_upwards [(localSheet P f hf z).open_source.mem_nhds (mem_localSheet_source P f hf z)] with y hy
  change snd P f y = ((trivialization P f z).sheet (sheetLabel P f z)).symm (f (fst P f y))
  rw [equation P f y]
  exact ((trivialization P f z).inverse_projection _ _ hy).symm

theorem smooth_action [IsManifold (Model m) ∞ B'] (g : G) :
    letI := chartedSpace (m := m) P f hf
    ContMDiff (Model m) (Model m) ∞ (fun z : Pullback P f => g • z) := by
  let := chartedSpace (m := m) P f hf
  apply smooth_of_fst P f hf
  · exact ((continuous_fst P f).prodMk
      ((P.smooth_action g).continuous.comp (continuous_snd P f))).subtype_mk _
  · exact smooth_fst P f hf

theorem smooth_sheet_inverse [IsManifold (Model m) ∞ B'] (z : Pullback P f)
    (t : LocalTrivialization (n := n) (G := G) P.projection) (g : G) :
    letI := chartedSpace (m := m) P f hf
    ContMDiffOn (Model m) (Model m) ∞ (sheet P f hf z t g).symm (f ⁻¹' t.base) := by
  let := chartedSpace (m := m) P f hf
  intro b hb
  apply (smooth_of_fst_at P f hf _ b
    ((sheet P f hf z t g).continuousOn_symm.continuousAt
      ((sheet P f hf z t g).open_target.mem_nhds hb)) ?_).contMDiffWithinAt
  apply (contMDiffAt_id (I := Model m) (n := ∞)).congr_of_eventuallyEq
  filter_upwards [(sheet P f hf z t g).open_target.mem_nhds hb] with c hc
  exact (sheet P f hf z t g).right_inv hc

theorem sheet_symm_apply (z : Pullback P f)
    (t : LocalTrivialization (n := n) (G := G) P.projection) (g : G)
    (b : B') (hb : f b ∈ t.base) :
    (sheet P f hf z t g).symm b =
      ⟨(b, (t.sheet g).symm (f b)), (t.projection_inverse g _ hb).symm⟩ := by
  change (if hb : f b ∈ t.base then _ else _) = _
  rw [dite_eq_left hb]

def liftTrivialization [IsManifold (Model m) ∞ B'] (z : Pullback P f)
    (t : LocalTrivialization (n := n) (G := G) P.projection) :
    letI := chartedSpace (m := m) P f hf
    LocalTrivialization (n := m) (G := G) (fst P f) := by
  letI := chartedSpace (m := m) P f hf
  exact {
    base := f ⁻¹' t.base
    isOpen_base := t.isOpen_base.preimage hf
    sheet := sheet P f hf z t
    target _ := rfl
    projection _ _ _ := rfl
    smooth_inverse := smooth_sheet_inverse P f hf z t
    sheets y hy := t.sheets (snd P f y) ((equation P f y) ▸ hy)
    equivariant g h b hb := by
      rw [sheet_symm_apply P f hf z t _ b hb, sheet_symm_apply P f hf z t _ b hb]
      apply Subtype.ext
      exact Prod.ext rfl (t.equivariant g h (f b) hb) }

/-- The ordinary pullback bundle is derived from the original local sheets. -/
def bundle [IsManifold (Model m) ∞ B'] :
    letI := chartedSpace (m := m) P f hf
    Bundle (n := m) (G := G) (B := B') (E := Pullback P f) := by
  letI := chartedSpace (m := m) P f hf
  exact {
    projection := fst P f
    smooth_projection := smooth_fst P f hf
    smooth_action := smooth_action P f hf
    invariant _ _ := rfl
    triviality b := by
      obtain ⟨t, ht⟩ := P.triviality (f b)
      let z : Pullback P f := ⟨(b, (t.sheet 1).symm (f b)), (t.projection_inverse 1 _ ht).symm⟩
      exact ⟨liftTrivialization P f hf z t, ht⟩ }

section Maps
variable {E' E'' : Type} [TopologicalSpace E'] [TopologicalSpace E'']
  [ChartedSpace (Space n) E'] [ChartedSpace (Space n) E'']
  [MulAction G E'] [MulAction G E''] [IsManifold (Model m) ∞ B']
variable {Q : Bundle (n := n) (G := G) (B := B) (E := E')}
  {R : Bundle (n := n) (G := G) (B := B) (E := E'')}

/-- Pullback keeps the base point and applies the supplied bundle map in the fiber. -/
def map (k : Map P Q) :
    letI := chartedSpace (m := m) P f hf
    letI := chartedSpace (m := m) Q f hf
    Map (bundle (m := m) P f hf) (bundle (m := m) Q f hf) := by
  letI := chartedSpace (m := m) P f hf
  letI := chartedSpace (m := m) Q f hf
  exact {
    toFun z := ⟨(z.val.1, k.toFun z.val.2), z.property.trans (k.projection z.val.2).symm⟩
    smooth := smooth_of_fst Q f hf _
      (((continuous_fst P f).prodMk (k.smooth.continuous.comp (continuous_snd P f))).subtype_mk _)
      (smooth_fst P f hf)
    projection _ := rfl
    equivariant g z := Subtype.ext (Prod.ext rfl (k.equivariant g z.val.2)) }

theorem map_fst (a : Map P Q) (z : Pullback P f) :
    letI := chartedSpace (m := m) P f hf
    letI := chartedSpace (m := m) Q f hf
    fst Q f ((map (m := m) P f hf a).toFun z) = fst P f z := rfl

theorem map_snd (a : Map P Q) (z : Pullback P f) :
    letI := chartedSpace (m := m) P f hf
    letI := chartedSpace (m := m) Q f hf
    snd Q f ((map (m := m) P f hf a).toFun z) = a.toFun (snd P f z) := rfl

theorem map_ident :
    letI := chartedSpace (m := m) P f hf
    map P f hf (Map.ident P) = Map.ident (bundle (m := m) P f hf) := by
  let := chartedSpace (m := m) P f hf

  apply Map.ext
  rfl

theorem map_comp (k : Map P Q) (l : Map Q R) :
    letI := chartedSpace (m := m) P f hf
    letI := chartedSpace (m := m) Q f hf
    letI := chartedSpace (m := m) R f hf

    map (m := m) P f hf (k.comp l) = (map P f hf k).comp (map Q f hf l) := by
  let := chartedSpace (m := m) P f hf
  let := chartedSpace (m := m) Q f hf
  let := chartedSpace (m := m) R f hf

  apply Map.ext
  rfl

end Maps

section Identity
variable [IsManifold (Model n) ∞ B]

def identityEquiv : Pullback P (id : B → B) ≃ E where
  toFun := snd P id
  invFun e := ⟨(P.projection e, e), rfl⟩
  left_inv z := Subtype.ext (Prod.ext z.property.symm rfl)
  right_inv _ := rfl

def identityMap :
    letI := chartedSpace (m := n) P (id : B → B) continuous_id
    Map (bundle (m := n) P id continuous_id) P := by
  letI := chartedSpace (m := n) P (id : B → B) continuous_id
  exact {
    toFun := identityEquiv P
    smooth := smooth_snd P id continuous_id contMDiff_id
    projection z := z.property.symm
    equivariant _ _ := rfl }

def identityInverseMap :
    letI := chartedSpace (m := n) P (id : B → B) continuous_id
    Map P (bundle (m := n) P id continuous_id) := by
  letI := chartedSpace (m := n) P (id : B → B) continuous_id
  exact {
    toFun := (identityEquiv P).symm
    smooth := smooth_of_fst P id continuous_id _
      ((P.smooth_projection.continuous.prodMk continuous_id).subtype_mk _) P.smooth_projection
    projection _ := rfl
    equivariant g e := Subtype.ext (Prod.ext (P.invariant g e) rfl) }

theorem identityMap_inverse :
    letI := chartedSpace (m := n) P (id : B → B) continuous_id
 (identityMap P).comp (identityInverseMap P) =
    Map.ident (bundle (m := n) P id continuous_id) := by
  let := chartedSpace (m := n) P (id : B → B) continuous_id

  apply Map.ext
  funext z
  exact (identityEquiv P).left_inv z

theorem identityInverseMap_inverse :
    letI := chartedSpace (m := n) P (id : B → B) continuous_id
 (identityInverseMap P).comp (identityMap P) = Map.ident P := by
  let := chartedSpace (m := n) P (id : B → B) continuous_id

  apply Map.ext
  rfl

theorem identityMap_natural {E' : Type} [TopologicalSpace E']
    [ChartedSpace (Space n) E'] [MulAction G E']
    {Q : Bundle (n := n) (G := G) (B := B) (E := E')} (a : Map P Q) :
    letI := chartedSpace (m := n) P (id : B → B) continuous_id
    letI := chartedSpace (m := n) Q (id : B → B) continuous_id
    (identityMap P).comp a = (map P id continuous_id a).comp (identityMap Q) := by
  let := chartedSpace (m := n) P (id : B → B) continuous_id
  let := chartedSpace (m := n) Q (id : B → B) continuous_id
  apply Map.ext
  rfl

end Identity

section Composition
variable [IsManifold (Model m) ∞ B'] {k : ℕ} {B'' : Type}
  [TopologicalSpace B''] [ChartedSpace (Space k) B''] [IsManifold (Model k) ∞ B'']
  (g : B'' → B') (hg : Continuous g)

/-- Flatten the actual iterated fiber product, retaining both base and total points. -/
def compositionEquiv :
    letI := chartedSpace (m := m) P f hf
    Pullback (bundle (m := m) P f hf) g ≃ Pullback P (f ∘ g) := by
  letI := chartedSpace (m := m) P f hf
  exact {
    toFun z := ⟨(z.val.1, z.val.2.val.2), (congrArg f z.property).trans z.val.2.property⟩
    invFun z := ⟨(z.val.1, ⟨(g z.val.1, z.val.2), z.property⟩), rfl⟩
    left_inv z := by
      apply Subtype.ext
      refine Prod.ext rfl ?_
      exact Subtype.ext (Prod.ext z.property rfl)
    right_inv _ := rfl }

def compositionMap :
    letI := chartedSpace (m := m) P f hf
    letI := chartedSpace (m := k) (bundle (m := m) P f hf) g hg
    letI := chartedSpace (m := k) P (f ∘ g) (hf.comp hg)
    Map (bundle (m := k) (bundle (m := m) P f hf) g hg)
      (bundle (m := k) P (f ∘ g) (hf.comp hg)) := by
  letI := chartedSpace (m := m) P f hf
  letI := chartedSpace (m := k) (bundle (m := m) P f hf) g hg
  letI := chartedSpace (m := k) P (f ∘ g) (hf.comp hg)
  exact {
    toFun := compositionEquiv P f hf g
    smooth := smooth_of_fst P (f ∘ g) (hf.comp hg) _
      (((continuous_fst (bundle (m := m) P f hf) g).prodMk
        ((continuous_snd P f).comp (continuous_snd (bundle (m := m) P f hf) g))).subtype_mk _)
      (smooth_fst (bundle (m := m) P f hf) g hg)
    projection _ := rfl
    equivariant _ _ := rfl }

def compositionInverseMap :
    letI := chartedSpace (m := m) P f hf
    letI := chartedSpace (m := k) (bundle (m := m) P f hf) g hg
    letI := chartedSpace (m := k) P (f ∘ g) (hf.comp hg)
    Map (bundle (m := k) P (f ∘ g) (hf.comp hg))
      (bundle (m := k) (bundle (m := m) P f hf) g hg) := by
  letI := chartedSpace (m := m) P f hf
  letI := chartedSpace (m := k) (bundle (m := m) P f hf) g hg
  letI := chartedSpace (m := k) P (f ∘ g) (hf.comp hg)
  exact {
    toFun := (compositionEquiv P f hf g).symm
    smooth := smooth_of_fst (bundle (m := m) P f hf) g hg _
      (((continuous_fst P (f ∘ g)).prodMk
        (((hg.comp (continuous_fst P (f ∘ g))).prodMk
          (continuous_snd P (f ∘ g))).subtype_mk _)).subtype_mk _)
      (smooth_fst P (f ∘ g) (hf.comp hg))
    projection _ := rfl
    equivariant _ _ := rfl }

theorem compositionMap_fst (z :
    letI := chartedSpace (m := m) P f hf
    Pullback (bundle (m := m) P f hf) g) :
    letI := chartedSpace (m := m) P f hf
    letI := chartedSpace (m := k) (bundle (m := m) P f hf) g hg
    letI := chartedSpace (m := k) P (f ∘ g) (hf.comp hg)
    fst P (f ∘ g) ((compositionMap (m := m) (k := k) P f hf g hg).toFun z) = z.val.1 := rfl

theorem compositionMap_snd (z :
    letI := chartedSpace (m := m) P f hf
    Pullback (bundle (m := m) P f hf) g) :
    letI := chartedSpace (m := m) P f hf
    letI := chartedSpace (m := k) (bundle (m := m) P f hf) g hg
    letI := chartedSpace (m := k) P (f ∘ g) (hf.comp hg)
    snd P (f ∘ g) ((compositionMap (m := m) (k := k) P f hf g hg).toFun z) = z.val.2.val.2 := rfl

theorem compositionMap_inverse :
    letI := chartedSpace (m := m) P f hf
    letI := chartedSpace (m := k) (bundle (m := m) P f hf) g hg
    letI := chartedSpace (m := k) P (f ∘ g) (hf.comp hg)

    (compositionMap (m := m) (k := k) P f hf g hg).comp (compositionInverseMap P f hf g hg) =
      Map.ident (bundle (m := k) (bundle (m := m) P f hf) g hg) := by
  let := chartedSpace (m := m) P f hf
  let := chartedSpace (m := k) (bundle (m := m) P f hf) g hg
  let := chartedSpace (m := k) P (f ∘ g) (hf.comp hg)

  apply Map.ext
  funext z
  exact (compositionEquiv P f hf g).left_inv z

theorem compositionInverseMap_inverse :
    letI := chartedSpace (m := m) P f hf
    letI := chartedSpace (m := k) (bundle (m := m) P f hf) g hg
    letI := chartedSpace (m := k) P (f ∘ g) (hf.comp hg)

    (compositionInverseMap (m := m) (k := k) P f hf g hg).comp (compositionMap P f hf g hg) =
      Map.ident (bundle (m := k) P (f ∘ g) (hf.comp hg)) := by
  let := chartedSpace (m := m) P f hf
  let := chartedSpace (m := k) (bundle (m := m) P f hf) g hg
  let := chartedSpace (m := k) P (f ∘ g) (hf.comp hg)

  apply Map.ext
  rfl

theorem compositionMap_natural {E' : Type} [TopologicalSpace E']
    [ChartedSpace (Space n) E'] [MulAction G E']
    {Q : Bundle (n := n) (G := G) (B := B) (E := E')} (a : Map P Q) :
    letI := chartedSpace (m := m) P f hf
    letI := chartedSpace (m := k) (bundle (m := m) P f hf) g hg
    letI := chartedSpace (m := k) P (f ∘ g) (hf.comp hg)
    letI := chartedSpace (m := m) Q f hf
    letI := chartedSpace (m := k) (bundle (m := m) Q f hf) g hg
    letI := chartedSpace (m := k) Q (f ∘ g) (hf.comp hg)

    (compositionMap (m := m) (k := k) P f hf g hg).comp (map P (f ∘ g) (hf.comp hg) a) =
      (map (bundle (m := m) P f hf) g hg (map P f hf a)).comp
        (compositionMap Q f hf g hg) := by
  let := chartedSpace (m := m) P f hf
  let := chartedSpace (m := k) (bundle (m := m) P f hf) g hg
  let := chartedSpace (m := k) P (f ∘ g) (hf.comp hg)
  let := chartedSpace (m := m) Q f hf
  let := chartedSpace (m := k) (bundle (m := m) Q f hf) g hg
  let := chartedSpace (m := k) Q (f ∘ g) (hf.comp hg)

  apply Map.ext
  rfl

end Composition

end Pullback
end SquareKit.SmoothPrincipalBundle
