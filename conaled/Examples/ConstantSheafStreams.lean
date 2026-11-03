import SquareKit.ConstantSheafProducts
import SquareKit.ProductStreams
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Compactness.Compact

/-! Every finite prefix is preserved, while the full stream comparison is not.
The source space has the product topology; local constancy treats the stream
codomain as a discrete set, never with that product topology. -/
noncomputable section
namespace Examples.ConstantSheafStreams
open CategoryTheory Opposite TopologicalSpace CategoryTheory.Limits
open SquareKit.LocallyConstantSheaf
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := ⟨rfl⟩
abbrev Cantor := Nat → Bool
def space : TopCat := TopCat.of Cantor
abbrev whole : Opens space := ⊤

def coordinate (n : Nat) : LocallyConstant whole Bool :=
  (LocallyConstant.eval n).comap ⟨Subtype.val, continuous_subtype_val⟩

def coordinates : (power space Nat Bool).obj.obj (op whole) := coordinate

/-- A compact space has finite locally constant images; Cantor has infinitely
many distinct points, so its identity cannot be locally constant. -/
theorem identity_not_locallyConstant : ¬ IsLocallyConstant (id : Cantor → Cantor) := by
  intro h
  have finiteAll : (Set.univ : Set Cantor).Finite := by
    simpa only [Set.range_id] using h.range_finite
  have finiteType : Finite Cantor := Set.finite_univ_iff.mp finiteAll
  have inj : Function.Injective (fun n : Nat => (fun m : Nat => decide (n = m) : Cantor)) := by
    intro n m hnm
    have h := congrFun hnm n
    have hmn : m = n := by simpa using h.symm
    exact hmn.symm
  have : Finite Nat := Finite.of_injective _ inj
  exact not_finite Nat

/-- The coordinate family is a genuine global section of the product sheaf. -/
theorem coordinates_not_image :
    ¬ ∃ s : (obj space Cantor).obj.obj (op whole),
      (comparison space Nat Bool).hom.app (op whole) s = coordinates := by
  rintro ⟨s, hs⟩
  change LocallyConstant whole Cantor at s
  let f : LocallyConstant Cantor Cantor :=
    s.comap ⟨fun x => ⟨x, trivial⟩, continuous_id.subtype_mk _⟩
  have hf : (f : Cantor → Cantor) = id := by
    funext x n
    exact congrArg (fun k : Nat → LocallyConstant whole Bool => k n ⟨x, trivial⟩) hs
  exact identity_not_locallyConstant (hf ▸ f.isLocallyConstant)

theorem comparison_not_iso : ¬ IsIso (comparison space Nat Bool) := by
  intro h
  let := h
  apply coordinates_not_image
  refine ⟨(inv (comparison space Nat Bool)).hom.app (op whole) coordinates, ?_⟩
  exact congrArg (fun k : power space Nat Bool ⟶ power space Nat Bool =>
    k.hom.app (op whole) coordinates) (IsIso.inv_hom_id (comparison space Nat Bool))

theorem canonical_not_iso : ¬ IsIso (canonicalComparison space Nat Bool) := by
  intro h
  have : IsIso (comparison space Nat Bool) := by
    have h' : comparison space Nat Bool = canonicalComparison space Nat Bool ≫
        (SquareKit.SheafIndexedProduct.iso _).inv := by
      simp [canonicalComparison]
    rw [h']; infer_instance
  exact comparison_not_iso this

/-- The actual categorical product carries the same missing global section. -/
def categoricalCoordinates :
    (∏ᶜ (fun _ : Nat => obj space Bool)).obj.obj (op whole) :=
  (SquareKit.SheafIndexedProduct.iso _).hom.hom.app (op whole) coordinates

theorem categoricalCoordinates_not_image :
    ¬ ∃ s : (obj space Cantor).obj.obj (op whole),
      (canonicalComparison space Nat Bool).hom.app (op whole) s = categoricalCoordinates := by
  rintro ⟨s, hs⟩
  apply coordinates_not_image
  refine ⟨s, ?_⟩
  have hi := congrArg (fun z => (SquareKit.SheafIndexedProduct.iso
    (fun _ : Nat => obj space Bool)).inv.hom.app (op whole) z) hs
  let e := SquareKit.SheafIndexedProduct.iso (fun _ : Nat => obj space Bool)
  have cancel (z : (power space Nat Bool).obj.obj (op whole)) :
      e.inv.hom.app (op whole) (e.hom.hom.app (op whole) z) = z :=
    congrArg (fun k : power space Nat Bool ⟶ power space Nat Bool =>
      k.hom.app (op whole) z) e.hom_inv_id
  change e.inv.hom.app (op whole)
    (e.hom.hom.app (op whole) ((comparison space Nat Bool).hom.app (op whole) s)) =
    e.inv.hom.app (op whole) (e.hom.hom.app (op whole) coordinates) at hi
  simpa only [cancel] using hi

/-- A checked specialization for every finite prefix, including length zero. -/
def prefixIso (n : Nat) : obj space (Fin n → Bool) ≅ power space (Fin n) Bool :=
  finiteIso space (Fin n) Bool

def prefixSection (n : Nat) : LocallyConstant whole (Fin n → Bool) :=
  LocallyConstant.unflip (fun i : Fin n => coordinate i.val)

theorem prefix_coordinates (n : Nat) :
    (comparison space (Fin n) Bool).hom.app (op whole) (prefixSection n) =
      fun i : Fin n => coordinate i.val := rfl

theorem prefix_value (n : Nat) (x : whole) (i : Fin n) : prefixSection n x i = x.val i.val := rfl

open CategoryTheory.Endofunctor SquareKit.ProductStreams

/-- Transport the source head and tail, using the preserved binary product. -/
def transportedCoalgebra : Coalgebra (step (obj space Bool)) where
  V := obj space Cantor
  str := prod.lift (map space (fun s : Cantor => s 0))
    (map space (fun s : Cantor => fun n => s (n + 1)))

/-- The coordinate comparison also preserves the coalgebra structure. -/
def coalgebraComparison : transportedCoalgebra ⟶ coalgebra (obj space Bool) where
  f := canonicalComparison space Nat Bool
  h := by
    apply prod.hom_ext
    · simp only [step, prod.functor, Category.assoc, prod.map_fst, Category.comp_id,
        transportedCoalgebra, prod.lift_fst, coalgebra, head, canonical_projection]
    · simp only [step, prod.functor, Category.assoc, prod.map_snd, transportedCoalgebra,
        prod.lift_snd_assoc, coalgebra, prod.lift_snd]
      apply Pi.hom_ext
      intro n
      simp only [Category.assoc, tail, Pi.lift_comp_π, canonical_projection]
      rfl

/-- The source really is final; the transported coalgebra is not. -/
def sourceFinal : IsTerminal (functionCoalgebra Bool) := functionFinal Bool

/-- The stronger preservation contract has a checked ordinary-Type client. -/
def identityRouteFinal : IsTerminal (functionCoalgebra Bool) := by
  have pid : piComparison (𝟭 (Type 0)) (fun _ : Nat => Bool) = 𝟙 _ := by
    apply Pi.hom_ext
    intro n
    rw [Category.id_comp]
    exact piComparison_comp_π (𝟭 (Type 0)) (fun _ : Nat => Bool) n
  apply final_of_preservesPower (𝟭 (Type 0)) Bool (functionCoalgebra Bool).str
  simp only [Functor.id_map, pid, Category.comp_id]
  exact (functionComparison Bool).h

theorem transported_not_final : ¬ Nonempty (IsTerminal transportedCoalgebra) := by
  rintro ⟨h⟩
  exact canonical_not_iso (comparison_iso_of_final (obj space Bool) coalgebraComparison h)

theorem countable_power_not_preserved :
    ¬ PreservesLimit (Discrete.functor (fun _ : Nat => Bool)) (delta space) := by
  intro h
  apply canonical_not_iso
  rw [canonical_eq_piComparison]
  infer_instance

/-- This structure is obtained by mapping the source head/tail pair and applying
exactly the finite binary-product comparison already proved invertible. -/
theorem transported_structure : transportedCoalgebra.str =
    map space (fun s : Cantor => (s 0, fun n => s (n + 1))) ≫
      (binaryIso space Bool Cantor).hom ≫
      (SquareKit.SheafRelation.productIso (obj space Bool) (obj space Cantor)).hom := by
  apply prod.hom_ext
  · rw [Category.assoc, Category.assoc]
    erw [SquareKit.SheafRelation.productIso_fst]
    simp only [transportedCoalgebra, prod.lift_fst]
    rfl
  · rw [Category.assoc, Category.assoc]
    erw [SquareKit.SheafRelation.productIso_snd]
    simp only [transportedCoalgebra, prod.lift_snd]
    rfl

/-- For any proposed replacement route in this setting, an invertible coalgebra
comparison is sufficient, and requires no assumptions about arbitrary codata. -/
def final_when_comparison_invertible {S : Coalgebra (step (obj space Bool))}
    (f : S ⟶ coalgebra (obj space Bool)) [IsIso f.f] : IsTerminal S :=
  final_of_comparison (obj space Bool) f

end Examples.ConstantSheafStreams
