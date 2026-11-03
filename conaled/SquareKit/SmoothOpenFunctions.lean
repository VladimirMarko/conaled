import SquareKit.SmoothAlgebra

/-! Experimental full ordinary smooth-function algebras on open subsets.
Only smoothness on the open domain is required; no ambient smooth extension is assumed. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace SquareKit.SmoothAlgebra.OpenFunctions
variable {n : ℕ}

def extendZero (U : Set (Fin n → ℝ)) (g : U → ℝ) (x : Fin n → ℝ) : ℝ :=
  by classical exact if h : x ∈ U then g ⟨x,h⟩ else 0

@[simp] theorem extendZero_mem {U : Set (Fin n → ℝ)} (g : U → ℝ) (x : U) :
    extendZero U g x.val = g x := by simp [extendZero,x.property]

def algebra (U : Set (Fin n → ℝ)) : Subalgebra ℝ (U → ℝ) where
  carrier := {g | ContDiffOn ℝ ∞ (extendZero U g) U}
  zero_mem' := (contDiffOn_const (c := (0 : ℝ))).congr (by intro x hx; simp [extendZero,hx])
  one_mem' := (contDiffOn_const (c := (1 : ℝ))).congr (by intro x hx; simp [extendZero,hx])
  add_mem' {f g} hf hg := (hf.add hg).congr (by intro x hx; simp [extendZero,hx])
  mul_mem' {f g} hf hg := (hf.mul hg).congr (by intro x hx; simp [extendZero,hx])
  algebraMap_mem' r := (contDiffOn_const (c := r)).congr (by intro x hx; simp [extendZero,hx])

abbrev Carrier (U : Set (Fin n → ℝ)) := algebra U

/-- For an open domain this is exactly ordinary local smoothness at each point. -/
theorem smooth_iff {U : Set (Fin n → ℝ)} (hU : IsOpen U) (g : U → ℝ) :
    g ∈ algebra U ↔ ∀ x ∈ U, ContDiffAt ℝ ∞ (extendZero U g) x := by
  change ContDiffOn ℝ ∞ (extendZero U g) U ↔ _
  exact ⟨fun h x hx => h.contDiffAt (hU.mem_nhds hx), fun h x hx => (h x hx).contDiffWithinAt⟩

/-- The zero extension can be replaced by any ambient function agreeing on U.
No smoothness away from U is requested of that representative. -/
theorem representative_iff {U : Set (Fin n → ℝ)} (g : U → ℝ) (q : (Fin n → ℝ) → ℝ)
    (hq : ∀ x : U, q x.val = g x) : g ∈ algebra U ↔ ContDiffOn ℝ ∞ q U := by
  change ContDiffOn ℝ ∞ (extendZero U g) U ↔ _
  constructor <;> intro h
  · exact h.congr (fun x hx => (hq ⟨x,hx⟩).trans (extendZero_mem g ⟨x,hx⟩).symm)
  · exact h.congr (fun x hx => (extendZero_mem g ⟨x,hx⟩).trans (hq ⟨x,hx⟩).symm)

instance (U : Set (Fin n → ℝ)) : Structure (Carrier U) where
  act f g := ⟨fun x => f.val (fun i => (g i).val x), by
    apply (f.property.contDiffOn.comp (contDiffOn_pi.mpr (fun i => (show ContDiffOn ℝ ∞ (extendZero U (g i).val) U from (g i).property))) (fun _ _ => Set.mem_univ _)).congr
    intro x hx
    simp [extendZero,hx]⟩
  projection _ _ := rfl
  substitute _ _ _ := rfl
  constant _ _ _ := rfl
  addition _ := rfl
  multiplication _ := rfl

@[ext] theorem ext {U : Set (Fin n → ℝ)} {g h : Carrier U} (he : ∀ x, g.val x = h.val x) : g=h :=
  Subtype.ext (funext he)

def restrict {U V : Set (Fin n → ℝ)} (h : V ⊆ U) : Hom (Carrier U) (Carrier V) where
  toFun g := ⟨fun x => g.val ⟨x.val,h x.property⟩, by
    exact ((show ContDiffOn ℝ ∞ (extendZero U g.val) U from g.property).mono h).congr (by intro x hx; simp [extendZero,hx,h hx])⟩
  map_act _ _ := rfl

end SquareKit.SmoothAlgebra.OpenFunctions
