import Applications.Probability.FiniteKernel

/-! Exact table equality reflected from the whole stochastic kernel. -/
namespace Applications.Probability
open MeasureTheory ProbabilityTheory

/-- Clipping is injective only on the stated nonnegative rational domain. -/
theorem mass_injective_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : mass a = mass b) : a = b := by
  have h' := congrArg ENNReal.toReal h
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (0 : ℝ) ≤ b := by exact_mod_cast hb
  simp only [mass, ENNReal.toReal_ofReal ha', ENNReal.toReal_ofReal hb'] at h'
  exact_mod_cast h'

namespace Table
variable {α β : Type*} [Fintype α] [Fintype β]

omit [Fintype α] in
@[ext] theorem ext {s t : Table α β} (h : ∀ x y, s.entry x y = t.entry x y) : s = t := by
  cases s
  cases t
  congr
  funext x y
  exact h x y

variable [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Singleton observations recover every exact nonnegative rational entry. -/
theorem kernel_injective : Function.Injective (kernel (α := α) (β := β)) := by
  intro s t h
  apply ext
  intro x y
  apply mass_injective_nonneg (s.nonneg x y) (t.nonneg x y)
  simpa only [kernel_singleton] using congrArg (fun k : Kernel α β => k x {y}) h

theorem kernel_eq_iff {s t : Table α β} : s.kernel = t.kernel ↔ s = t :=
  ⟨fun h => kernel_injective h, congrArg kernel⟩

end Table

theorem tableMeaning_injective {X Y : FiniteSpace} :
    Function.Injective (tableMeaning.map (a := X) (b := Y)) := by
  intro s t h
  apply Table.kernel_injective
  exact congrArg (fun k : (tableMeaning.obj X ⟶ tableMeaning.obj Y) => k.hom.hom) h

theorem tableEquiv_iff_eq {X Y : FiniteSpace} (s t : Table X Y) :
    tableEquiv.Rel s t ↔ s = t :=
  ⟨fun h => tableMeaning_injective h, fun h => congrArg tableMeaning.map h⟩

theorem tableEquiv_iff_entries {X Y : FiniteSpace} (s t : Table X Y) :
    tableEquiv.Rel s t ↔ ∀ x y, s.entry x y = t.entry x y := by
  rw [tableEquiv_iff_eq]
  exact ⟨fun h => by cases h; intro x y; rfl, Table.ext⟩

theorem tableMeaning_equality_laws :
    SquareKit.MapLaws tableMeaning (SquareKit.equality tableOps) (SquareKit.equality stochOps) where
  congr h := congrArg tableMeaning.map h
  ident := tableMeaning_laws.ident
  comp := tableMeaning_laws.comp

theorem tableMeaning_reflects :
    tableMeaning.Reflects (SquareKit.equality tableOps) (SquareKit.equality stochOps) :=
  fun h => tableMeaning_injective h

/-- Actual table laws use the same generic transport as the semantic facade. -/
theorem tableEqualityLaws : SquareKit.CategoryLaws tableOps (SquareKit.equality tableOps) :=
  SquareKit.RawMap.transportLaws tableMeaning_equality_laws tableMeaning_reflects
    (SquareKit.equalityCongr _) (SquareKit.ofCategoryLaws Stoch)

namespace Table
variable {W X Y Z : FiniteSpace}

theorem deterministic_id_comp (f : Table X Y) : comp (deterministic id) f = f :=
  tableEqualityLaws.id_comp f

theorem comp_deterministic_id (f : Table X Y) : comp f (deterministic id) = f :=
  tableEqualityLaws.comp_id f

theorem comp_assoc (h : Table Y Z) (g : Table X Y) (f : Table W X) :
    comp (comp h g) f = comp h (comp g f) := tableEqualityLaws.assoc h g f

/-- Concatenating iteration retains exact tables, not only their kernels. -/
theorem steps_add (t : Table X X) (n m : ℕ) :
    t.steps (n + m) = comp (t.steps m) (t.steps n) := by
  induction m with
  | zero => simpa only [Nat.add_zero, steps] using (deterministic_id_comp (t.steps n)).symm
  | succ m ih =>
    change comp t (t.steps (n + m)) = comp (comp t (t.steps m)) (t.steps n)
    rw [ih]
    exact (comp_assoc t (t.steps m) (t.steps n)).symm

end Table
end Applications.Probability
