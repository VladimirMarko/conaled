import Applications.Probability.FiniteMH
import Mathlib.Probability.Kernel.Category.Stoch
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import SquareKit.CategoryMap

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Applications.Probability

/-- Nonnegative rational mass interpreted in the extended nonnegative reals. -/
noncomputable def mass (q : ℚ) : ℝ≥0∞ := ENNReal.ofReal q

@[simp] theorem mass_zero : mass 0 = 0 := by simp [mass]
@[simp] theorem mass_one : mass 1 = 1 := by simp [mass]
theorem mass_mul (a b : ℚ) (ha : 0 ≤ a) : mass (a * b) = mass a * mass b := by
  simp only [mass, Rat.cast_mul]
  exact ENNReal.ofReal_mul (by exact_mod_cast ha)
theorem mass_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    mass (∑ i ∈ s, f i) = ∑ i ∈ s, mass (f i) := by
  simp only [mass, Rat.cast_sum]
  exact ENNReal.ofReal_sum_of_nonneg (fun i hi => by exact_mod_cast hf i hi)

namespace Table
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Exact sequential composition; the right argument runs first. -/
def comp (g : Table β γ) (f : Table α β) : Table α γ where
  entry x z := ∑ y, f.entry x y * g.entry y z
  nonneg x z := Finset.sum_nonneg fun y _ => mul_nonneg (f.nonneg x y) (g.nonneg y z)
  sum_row x := by
    simp only [Finset.sum_comm (f := fun z y => f.entry x y * g.entry y z)]
    simp_rw [← Finset.mul_sum, g.sum_row, mul_one]
    exact f.sum_row x

def deterministic [DecidableEq β] (f : α → β) : Table α β where
  entry x y := if f x = y then 1 else 0
  nonneg _ _ := by split_ifs <;> norm_num
  sum_row x := by simp

variable [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]
  [MeasurableSpace γ] [MeasurableSingletonClass γ]

/-- Meaning of a finite table. Random-bit implementations are separate. -/
noncomputable def kernel (t : Table α β) : Kernel α β where
  toFun x := ∑ y, mass (t.entry x y) • Measure.dirac y
  measurable' := measurable_of_countable _

theorem kernel_apply (t : Table α β) (x : α) (s : Set β) :
    t.kernel x s = ∑ y, mass (t.entry x y) * s.indicator (fun _ => 1) y := by
  classical
  simp [kernel, Measure.finsetSum_apply, Measure.smul_apply,
    Set.indicator_apply]

@[simp] theorem kernel_singleton (t : Table α β) (x : α) (y : β) :
    t.kernel x {y} = mass (t.entry x y) := by
  classical
  simp [kernel, Measure.finsetSum_apply, Measure.smul_apply, Pi.single_apply]

instance (t : Table α β) : IsMarkovKernel t.kernel := ⟨fun x => ⟨by
  change (∑ y, mass (t.entry x y) • Measure.dirac y) Set.univ = 1
  simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← mass_sum _ _ (fun y _ => t.nonneg x y), t.sum_row, mass_one]⟩⟩

theorem lintegral_kernel (t : Table α β) (x : α) (f : β → ℝ≥0∞) :
    ∫⁻ y, f y ∂t.kernel x = ∑ y, mass (t.entry x y) * f y := by
  simp [kernel, lintegral_finsetSum_measure, lintegral_smul_measure]

theorem kernel_comp (g : Table β γ) (f : Table α β) :
    (comp g f).kernel = g.kernel ∘ₖ f.kernel := by
  apply Kernel.ext
  intro x
  apply Measure.ext_of_singleton
  intro z
  rw [kernel_singleton, Kernel.comp_apply' _ _ _ (measurableSet_singleton z), lintegral_kernel]
  simp_rw [kernel_singleton]
  exact (mass_sum _ _ (fun y _ => mul_nonneg (f.nonneg x y) (g.nonneg y z))).trans
    (Finset.sum_congr rfl fun y _ => mass_mul _ _ (f.nonneg x y))

theorem kernel_deterministic [DecidableEq β] (f : α → β) :
    (deterministic f).kernel = Kernel.deterministic f (measurable_of_countable _) := by
  apply Kernel.ext
  intro x
  apply Measure.ext_of_singleton
  intro y
  classical
  by_cases h : f x = y <;> simp [kernel_singleton, deterministic, mass,
    Kernel.deterministic_apply, h]

end Table
end Applications.Probability

namespace Applications.Probability
namespace Table

/-- Repeated finite execution retains exact rational entries. -/
def steps {α : Type*} [Fintype α] [DecidableEq α] (t : Table α α) : ℕ → Table α α
  | 0 => deterministic id
  | n + 1 => comp t (steps t n)

end Table

/-- The objects carry their finite coordinate system; arrows are stochastic tables. -/
structure FiniteSpace where
  carrier : Type
  finite : Fintype carrier
  decEq : DecidableEq carrier

instance : CoeSort FiniteSpace Type := ⟨FiniteSpace.carrier⟩
instance (X : FiniteSpace) : Fintype X := X.finite
instance (X : FiniteSpace) : DecidableEq X := X.decEq
instance (X : FiniteSpace) : MeasurableSpace X := ⊤
instance (X : FiniteSpace) : MeasurableSingletonClass X := ⟨fun _ => trivial⟩

def tableOps : SquareKit.CategoryOps FiniteSpace where
  Hom X Y := Table X Y
  ident := Table.deterministic id
  comp := Table.comp

noncomputable def stochOps := SquareKit.ofCategory Stoch

/-- Table interpretation is a map into Mathlib's Markov category. -/
noncomputable def tableMeaning : SquareKit.RawMap tableOps stochOps where
  obj X := ⟨SFinKer.of X⟩
  map {X Y} t := by
    change Table X Y at t
    exact ⟨⟨t.kernel, inferInstance⟩, inferInstance⟩

/-- Semantic equality retains the whole joint law, not only marginals. -/
noncomputable def tableEquiv := tableMeaning.induced (SquareKit.equality stochOps)

theorem tableMeaning_laws :
    SquareKit.MapLaws tableMeaning tableEquiv (SquareKit.equality stochOps) := by
  apply SquareKit.RawMap.inducedLaws
  · intro X
    change tableMeaning.map (Table.deterministic id : Table X X) = _
    apply CategoryTheory.WideSubcategory.hom_ext
    apply SFinKer.Hom.ext
    exact Table.kernel_deterministic id
  · intro X Y Z g f
    apply CategoryTheory.WideSubcategory.hom_ext
    apply SFinKer.Hom.ext
    exact Table.kernel_comp g f

/-- Existing transport establishes the category laws for executable tables. -/
theorem tableCategoryLaws : SquareKit.CategoryLaws tableOps tableEquiv :=
  SquareKit.RawMap.transportLaws tableMeaning_laws
    (tableMeaning.induced_reflects _) (SquareKit.equalityCongr _)
    (SquareKit.ofCategoryLaws Stoch)

noncomputable def kernelSteps {α : Type*} [MeasurableSpace α] (k : Kernel α α) :
    ℕ → Kernel α α
  | 0 => Kernel.id
  | n + 1 => k ∘ₖ kernelSteps k n

/-- Finite iteration commutes with the table interpretation's composition law. -/
theorem table_steps_meaning (X : FiniteSpace) (t : Table X X) (n : ℕ) :
    (t.steps n).kernel = kernelSteps t.kernel n := by
  induction n with
  | zero => exact Table.kernel_deterministic id
  | succ n ih =>
    have h := tableMeaning_laws.comp t (t.steps n)
    have hk : (Table.comp t (t.steps n)).kernel = t.kernel ∘ₖ (t.steps n).kernel :=
      congrArg (fun k : (tableMeaning.obj X ⟶ tableMeaning.obj X) => k.hom.hom) h
    simpa only [Table.steps, kernelSteps, ih] using hk

/-- Two stationary transitions compose without requiring the composite to be reversible. -/
theorem invariant_comp {α : Type*} [MeasurableSpace α] {k l : Kernel α α}
    {π : Measure α} (hk : k.Invariant π) (hl : l.Invariant π) :
    (k ∘ₖ l).Invariant π := hk.comp hl

theorem invariant_steps {α : Type*} [MeasurableSpace α] {k : Kernel α α}
    {π : Measure α} (hk : k.Invariant π) (n : ℕ) : (kernelSteps k n).Invariant π := by
  induction n with
  | zero => exact Measure.bind_dirac
  | succ n ih => exact hk.comp ih

end Applications.Probability
