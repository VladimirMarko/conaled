import Mathlib.Geometry.Diffeology.Basic

/-! Induced and coinduced diffeologies on Mathlib's plot foundation.
The coinduced construction uses generated plots, so its universal property
holds without a surjectivity assumption. No subspace topology is asserted. -/

noncomputable section
open Diffeology

namespace DiffeologicalSpace
variable {X Y Z : Type*}

/-- Pull back plots along a function. -/
@[instance_reducible]
def induced (f : X → Y) (d : DiffeologicalSpace Y) : DiffeologicalSpace X where
  plots _ := {p | @IsPlot _ d _ (f ∘ p)}
  constant_plots x := @isPlot_const _ d _ (f x)
  plot_reparam hp hf := isPlot_reparam hp hf
  locality h := d.locality fun x => by
    obtain ⟨u, hu, hx, hp⟩ := h x
    exact ⟨u, hu, hx, fun hf hs => hp hf hs⟩

/-- Generate the plots forced by smoothness of a function. -/
@[instance_reducible]
def coinduced (f : X → Y) (d : DiffeologicalSpace X) : DiffeologicalSpace Y :=
  generateFrom {q | ∃ p, @IsPlot _ d _ p ∧ q.2 = f ∘ p}

end DiffeologicalSpace

namespace Diffeology
variable {X Y Z : Type*}

theorem dSmooth_induced_iff [DiffeologicalSpace X] [d : DiffeologicalSpace Z]
    (f : Y → Z) (g : X → Y) :
    @DSmooth X Y _ (.induced f d) g ↔ DSmooth (f ∘ g) := Iff.rfl

theorem dSmooth_coinduced_iff [d : DiffeologicalSpace X] [DiffeologicalSpace Z]
    (f : X → Y) (g : Y → Z) :
    @DSmooth Y Z (.coinduced f d) _ g ↔ DSmooth (g ∘ f) := by
  constructor
  · intro h n p hp
    exact h n (f ∘ p) (DiffeologicalSpace.isPlot_generatedFrom_of_mem ⟨p, hp, rfl⟩)
  · intro h n p hp
    exact hp (.induced g inferInstance) (by
      rintro ⟨m, q⟩ ⟨r, hr, he⟩
      change IsPlot (g ∘ q)
      change q = f ∘ r at he
      rw [he]
      exact h m r hr)

instance subtypeDiffeology [d : DiffeologicalSpace X] (s : Set X) :
    DiffeologicalSpace s := .induced Subtype.val d

theorem dSmooth_subtype_val [DiffeologicalSpace X] {s : Set X} :
    DSmooth (Subtype.val : s → X) := fun _ _ h => h

theorem dSmooth_subtype_iff [DiffeologicalSpace X] [DiffeologicalSpace Y]
    {s : Set Y} {f : X → s} : DSmooth f ↔ DSmooth (fun x => (f x : Y)) := Iff.rfl

instance quotientDiffeology [d : DiffeologicalSpace X] (r : Setoid X) :
    DiffeologicalSpace (Quotient r) := .coinduced (Quotient.mk r) d

theorem dSmooth_quotient_mk [DiffeologicalSpace X] (r : Setoid X) :
    DSmooth (Quotient.mk r) := fun _ p hp =>
  DiffeologicalSpace.isPlot_generatedFrom_of_mem ⟨p, hp, rfl⟩

theorem dSmooth_quotient_iff [DiffeologicalSpace X] [DiffeologicalSpace Y]
    {r : Setoid X} {f : Quotient r → Y} :
    DSmooth f ↔ DSmooth (f ∘ Quotient.mk r) := dSmooth_coinduced_iff _ _

/-- Smooth descent of any map constant on the chosen equivalence classes. -/
theorem dSmooth_quotient_lift [DiffeologicalSpace X] [DiffeologicalSpace Y]
    {r : Setoid X} {f : X → Y} (hf : DSmooth f)
    (h : ∀ a b, r a b → f a = f b) : DSmooth (Quotient.lift f h) :=
  dSmooth_quotient_iff.mpr hf

/-- Smooth descent of a relation-preserving map. -/
theorem dSmooth_quotient_map [DiffeologicalSpace X] [DiffeologicalSpace Y]
    {r : Setoid X} {s : Setoid Y} {f : X → Y} (hf : DSmooth f)
    (h : ∀ a b, r a b → s (f a) (f b)) : DSmooth (Quotient.map f h) :=
  dSmooth_quotient_iff.mpr ((dSmooth_quotient_mk s).comp hf)

/-- A checked identity specialization of smooth quotient descent. -/
theorem quotient_map_id [DiffeologicalSpace X] (r : Setoid X) :
    Quotient.map id (fun _ _ h => h) = (id : Quotient r → Quotient r) := by
  funext q
  exact Quotient.inductionOn q fun _ => rfl

theorem quotient_map_comp {r : Setoid X} {s : Setoid Y} {t : Setoid Z}
    (f : X → Y) (g : Y → Z)
    (hf : ∀ a b, r a b → s (f a) (f b))
    (hg : ∀ a b, s a b → t (g a) (g b)) :
    Quotient.map (g ∘ f) (fun a b h => hg _ _ (hf a b h)) =
      Quotient.map g hg ∘ Quotient.map f hf := by
  funext q
  exact Quotient.inductionOn q fun _ => rfl

end Diffeology

namespace Diffeology
/-- A bijection smooth in both directions for the specified diffeologies. -/
structure SmoothEquiv (X Y : Type*) [DiffeologicalSpace X] [DiffeologicalSpace Y]
    extends X ≃ Y where
  smooth : DSmooth toEquiv
  smooth_symm : DSmooth toEquiv.symm
end Diffeology
