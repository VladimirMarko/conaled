import SquareKit.SmoothManifoldModel

/-! Ordinary smooth principal bundles in sheetwise local-triviality form.
The input uses ordinary open partial homeomorphisms only. Each forward sheet map
is the given smooth projection, and each inverse sheet map is smooth. Thus this
retains both directions of ordinary local diffeomorphisms and open sheet images. -/
noncomputable section
namespace SquareKit.SmoothPrincipalBundle
open ManifoldRealization
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]

/-- A product trivialization expressed by its open sheets. The unique sheet
condition supplies the discrete label coordinate; it is stronger than a fiber bijection. -/
structure LocalTrivialization (p : E → B) where
  base : Set B
  isOpen_base : IsOpen base
  sheet : G → OpenPartialHomeomorph E B
  target : ∀ g, (sheet g).target = base
  projection : ∀ g e, e ∈ (sheet g).source → sheet g e = p e
  smooth_inverse : ∀ g, ContMDiffOn (Model n) (Model n) ∞ (sheet g).symm base
  sheets : ∀ e, p e ∈ base → ∃! g, e ∈ (sheet g).source
  equivariant : ∀ g h b, b ∈ base → (sheet (g*h)).symm b = g • (sheet h).symm b

/-- Independently locally trivial ordinary bundle data. No represented atlas,
sheaf torsor, or quotient comparison occurs among the fields. -/
structure Bundle where
  projection : E → B
  smooth_projection : ContMDiff (Model n) (Model n) ∞ projection
  smooth_action : ∀ g : G, ContMDiff (Model n) (Model n) ∞ (fun e : E => g • e)
  invariant : ∀ (g : G) (e : E), projection (g • e) = projection e
  triviality : ∀ b, ∃ t : LocalTrivialization (n := n) (G := G) projection, b ∈ t.base

namespace LocalTrivialization
variable {p : E → B} (t : LocalTrivialization (n := n) (G := G) p)

theorem inverse_source (g : G) (b : B) (hb : b ∈ t.base) :
    (t.sheet g).symm b ∈ (t.sheet g).source :=
  (t.sheet g).map_target ((t.target g).symm ▸ hb)

theorem projection_inverse (g : G) (b : B) (hb : b ∈ t.base) :
    p ((t.sheet g).symm b) = b :=
  (t.projection g _ (t.inverse_source g b hb)).symm.trans
    ((t.sheet g).right_inv ((t.target g).symm ▸ hb))

theorem inverse_projection (g : G) (e : E) (he : e ∈ (t.sheet g).source) :
    (t.sheet g).symm (p e) = e := by
  rw [← t.projection g e he]
  exact (t.sheet g).left_inv he

theorem label_unique (g h : G) (b : B) (hb : b ∈ t.base)
    (he : (t.sheet g).symm b = (t.sheet h).symm b) : g = h := by
  have hp := t.projection_inverse g b hb
  obtain ⟨k,hk,hu⟩ := t.sheets ((t.sheet g).symm b) (by rw [hp]; exact hb)
  exact (hu g (t.inverse_source g b hb)).trans
    (hu h (by rw [he]; exact t.inverse_source h b hb)).symm

end LocalTrivialization
end SquareKit.SmoothPrincipalBundle

namespace SquareKit.SmoothPrincipalBundle.LocalTrivialization
open ManifoldRealization
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
variable {p : E → B} (t : LocalTrivialization (n := n) (G := G) p)

def label (e : E) (he : p e ∈ t.base) : G := (t.sheets e he).choose
theorem label_source (e : E) (he : p e ∈ t.base) : e ∈ (t.sheet (t.label e he)).source :=
  (t.sheets e he).choose_spec.1
theorem label_eq (e : E) (he : p e ∈ t.base) (g : G) (hg : e ∈ (t.sheet g).source) :
    t.label e he = g := ((t.sheets e he).choose_spec.2 g hg).symm

/-- Both inverse laws of the ordinary local product decomposition. -/
def productEquiv : {e : E // p e ∈ t.base} ≃ t.base × G where
  toFun e := (⟨p e.val,e.property⟩,t.label e.val e.property)
  invFun bg := ⟨(t.sheet bg.2).symm bg.1.val,
    (t.projection_inverse bg.2 bg.1.val bg.1.property).symm ▸ bg.1.property⟩
  left_inv e := Subtype.ext (t.inverse_projection _ _ (t.label_source e.val e.property))
  right_inv bg := by
    apply Prod.ext
    · exact Subtype.ext (t.projection_inverse bg.2 bg.1.val bg.1.property)
    · exact t.label_eq ((t.sheet bg.2).symm bg.1.val)
        (by rw [t.projection_inverse bg.2 bg.1.val bg.1.property]; exact bg.1.property)
        bg.2 (t.inverse_source bg.2 bg.1.val bg.1.property)

theorem action_on_sheet (g h : G) (e : E) (he : e ∈ (t.sheet h).source)
    (hb : p e ∈ t.base) : g • e = (t.sheet (g*h)).symm (p e) := by
  rw [t.equivariant g h (p e) hb, t.inverse_projection h e he]

end SquareKit.SmoothPrincipalBundle.LocalTrivialization

namespace SquareKit.SmoothPrincipalBundle
open ManifoldRealization
open scoped Manifold ContDiff
variable {n : ℕ} {G B : Type} [Group G] [Subsingleton G] [MulAction G B]
  [TopologicalSpace B] [ChartedSpace (Space n) B]

/-- The identity bundle checks the ordinary input without any compactness premise. -/
def identityBundle : Bundle (n := n) (G := G) (B := B) (E := B) where
  projection := id
  smooth_projection := contMDiff_id
  smooth_action g := by
    have hg : (fun e : B => g • e) = id := funext (fun e => by simp only [Subsingleton.elim g 1, one_smul, id_eq])
    rw [hg]
    exact contMDiff_id
  invariant g b := by simp only [Subsingleton.elim g 1, one_smul]
  triviality b := ⟨{
    base := Set.univ
    isOpen_base := isOpen_univ
    sheet _ := OpenPartialHomeomorph.refl B
    target _ := rfl
    projection _ _ _ := rfl
    smooth_inverse _ := contMDiff_id.contMDiffOn
    sheets _ _ := ⟨1,Set.mem_univ _,fun _ _ => Subsingleton.elim _ _⟩
    equivariant g h b _ := by simp only [Subsingleton.elim g 1, one_smul] }, Set.mem_univ b⟩
end SquareKit.SmoothPrincipalBundle

namespace SquareKit.SmoothPrincipalBundle.LocalTrivialization
open ManifoldRealization
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E] [TopologicalSpace G]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
variable {p : E → B} (t : LocalTrivialization (n := n) (G := G) p)

/-- The label coordinate is continuous because its fibers are the open sheets. -/
theorem continuous_label : Continuous (fun e : {e : E // p e ∈ t.base} => t.label e.val e.property) := by
  apply continuous_def.mpr
  intro s _
  have he : (fun e : {e : E // p e ∈ t.base} => t.label e.val e.property) ⁻¹' s =
      ⋃ g ∈ s, Subtype.val ⁻¹' (t.sheet g).source := by
    ext e
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨t.label e.val e.property,h,t.label_source e.val e.property⟩
    · rintro ⟨g,hg,he⟩
      rwa [t.label_eq e.val e.property g he]
  rw [he]
  exact isOpen_iUnion (fun g => isOpen_iUnion (fun _ => (t.sheet g).open_source.preimage continuous_subtype_val))
end SquareKit.SmoothPrincipalBundle.LocalTrivialization

namespace SquareKit.SmoothPrincipalBundle.Bundle
open ManifoldRealization
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
variable (P : Bundle (n := n) (G := G) (B := B) (E := E))

include P in
/-- Ordinary local sheets imply freeness, without selecting a global section. -/
theorem action_free (g h : G) (e : E) (he : g • e = h • e) : g = h := by
  obtain ⟨t,hb⟩ := P.triviality (P.projection e)
  obtain ⟨k,hk,_⟩ := t.sheets e hb
  have hlabel : g*k = h*k := t.label_unique _ _ _ hb (by
    rw [← t.action_on_sheet g k e hk hb, ← t.action_on_sheet h k e hk hb]
    exact he)
  exact mul_right_cancel hlabel
end SquareKit.SmoothPrincipalBundle.Bundle

namespace SquareKit.SmoothPrincipalBundle.LocalTrivialization
open ManifoldRealization
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
variable {p : E → B} (t : LocalTrivialization (n := n) (G := G) p)

/-- The sheet contract has an actual product homeomorphism, not just fiber
bijections. Smoothness is supplied sheetwise in both directions. -/
def productHomeomorph (hp : Continuous p) : {e : E // p e ∈ t.base} ≃ₜ t.base × G where
  toEquiv := t.productEquiv
  continuous_toFun := ((hp.comp continuous_subtype_val).subtype_mk _).prodMk t.continuous_label
  continuous_invFun := by
    apply continuous_prod_of_discrete_right.mpr
    intro g
    apply Continuous.subtype_mk
    exact ((t.sheet g).continuousOn_symm.mono (fun b hb => (t.target g).symm ▸ hb)).domRestrict
end SquareKit.SmoothPrincipalBundle.LocalTrivialization
