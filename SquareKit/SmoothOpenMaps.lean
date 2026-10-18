import SquareKit.SmoothLocalizationOpen

/-! Experimental ordinary smooth maps of Euclidean open domains. Smoothness is
coordinatewise ContDiffOn, with no smoothness requirement outside the domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace SquareKit.SmoothAlgebra.OpenFunctions
variable {n m k : ℕ} {U : Set (Fin n → ℝ)} {V : Set (Fin m → ℝ)} {W : Set (Fin k → ℝ)}

structure Map (U : Set (Fin n → ℝ)) (V : Set (Fin m → ℝ)) where
  toFun : U → V
  smooth : ∀ i, ContDiffOn ℝ ∞ (extendZero U (fun x => (toFun x).val i)) U

namespace Map
instance : CoeFun (Map U V) (fun _ => U → V) := ⟨Map.toFun⟩

@[ext] theorem ext {f g : Map U V} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g
  congr
  exact funext h

def representative (f : Map U V) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => extendZero U (fun y => (f y).val i) x

@[simp] theorem representative_mem (f : Map U V) (x : U) : f.representative x.val = (f x).val :=
  funext (fun _ => extendZero_mem _ x)

theorem smooth_representative (f : Map U V) : ContDiffOn ℝ ∞ f.representative U :=
  contDiffOn_pi.mpr f.smooth

/-- On an open set coordinatewise smoothness is ordinary local smoothness. -/
theorem smooth_iff (hU : IsOpen U) (f : U → V) :
    (∀ i, ContDiffOn ℝ ∞ (extendZero U (fun x => (f x).val i)) U) ↔
      ∀ x ∈ U, ContDiffAt ℝ ∞ (fun y i => extendZero U (fun z => (f z).val i) y) x := by
  rw [← contDiffOn_pi]
  exact ⟨fun h x hx => h.contDiffAt (hU.mem_nhds hx), fun h x hx => (h x hx).contDiffWithinAt⟩

/-- Pullback acts on all smooth functions, including those without ambient extensions. -/
def pullback (f : Map U V) : Hom (Carrier V) (Carrier U) where
  toFun g := ⟨fun x => g.val (f x), by
    apply (representative_iff _ (fun x => extendZero V g.val (f.representative x))
      (fun x => by rw [representative_mem, extendZero_mem])).mpr
    exact g.property.comp f.smooth_representative (fun x hx => by
      rw [show f.representative x = (f ⟨x,hx⟩).val from representative_mem f ⟨x,hx⟩]
      exact (f ⟨x,hx⟩).property)⟩
  map_act _ _ := rfl

def ident (U : Set (Fin n → ℝ)) : Map U U where
  toFun := id
  smooth i := (representative_iff _ (fun x => x i) (fun _ => rfl)).mpr
    (contDiff_apply ℝ (fun _ : Fin n => ℝ) i).contDiffOn

def comp (g : Map V W) (f : Map U V) : Map U W where
  toFun x := g (f x)
  smooth i := (f.pullback ⟨fun y => (g y).val i, g.smooth i⟩).property

theorem pullback_ident : (ident U).pullback = Hom.ident := Hom.ext (fun _ => rfl)
theorem pullback_comp (g : Map V W) (f : Map U V) :
    (comp g f).pullback = Hom.comp f.pullback g.pullback := rfl

end Map
end SquareKit.SmoothAlgebra.OpenFunctions
