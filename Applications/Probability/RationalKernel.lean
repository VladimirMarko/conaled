import Applications.Probability.FiniteKernelEquality
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
/-! Native rational finite kernels and exact table reconstruction. -/
set_option autoImplicit false
set_option warningAsError true
namespace Applications.Probability
variable {α β γ α' β' α'' β'' : Type*}
  [Fintype α] [Fintype β] [Fintype γ] [Fintype α'] [Fintype β'] [Fintype α''] [Fintype β'']
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]
  [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [MeasurableSpace α'] [MeasurableSingletonClass α']
  [MeasurableSpace β'] [MeasurableSingletonClass β']
  [MeasurableSpace α''] [MeasurableSingletonClass α'']
  [MeasurableSpace β''] [MeasurableSingletonClass β'']
/-- A native Markov kernel with rational singleton masses. Row sums are derived. -/
structure RationalKernel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  kernel : Kernel α β
  markov : IsMarkovKernel kernel
  rational : ∀ x y, ∃ q : ℚ, 0 ≤ q ∧ mass q = kernel x {y}
attribute [instance] RationalKernel.markov
omit [Fintype α] [Fintype β] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
@[ext] theorem RationalKernel.ext {k l : RationalKernel α β} (h : k.kernel = l.kernel) : k = l := by
  cases k
  cases l
  cases h
  rfl
/-- Reconstruct entries; finite additivity and the Markov law prove normalization. -/
noncomputable def RationalKernel.table (k : RationalKernel α β) : Table α β where
  entry x y := (k.rational x y).choose
  nonneg x y := (k.rational x y).choose_spec.1
  sum_row x := by
    apply mass_injective_nonneg (Finset.sum_nonneg fun y _ => (k.rational x y).choose_spec.1) (by norm_num)
    rw [mass_sum _ _ (fun y _ => (k.rational x y).choose_spec.1), mass_one]
    simp_rw [(k.rational _ _).choose_spec.2]
    simp
@[simp] theorem RationalKernel.table_kernel (k : RationalKernel α β) : k.table.kernel = k.kernel := by
  apply Kernel.ext
  intro x
  apply Measure.ext_of_singleton
  intro y
  rw [Table.kernel_singleton]
  exact (k.rational x y).choose_spec.2
noncomputable def Table.rationalKernel (t : Table α β) : RationalKernel α β where
  kernel := t.kernel
  markov := inferInstance
  rational x y := ⟨t.entry x y,t.nonneg x y,(t.kernel_singleton x y).symm⟩
@[simp] theorem Table.rationalKernel_table (t : Table α β) : t.rationalKernel.table = t :=
  Table.kernel_injective t.rationalKernel.table_kernel
@[simp] theorem RationalKernel.table_rationalKernel (k : RationalKernel α β) : k.table.rationalKernel = k :=
  RationalKernel.ext k.table_kernel
/-- Full kernel data, with rationality, is equivalent to an exact table. -/
noncomputable def tableKernelEquiv : Table α β ≃ RationalKernel α β where
  toFun := Table.rationalKernel
  invFun := RationalKernel.table
  left_inv := Table.rationalKernel_table
  right_inv := RationalKernel.table_rationalKernel
noncomputable def RationalKernel.comp (g : RationalKernel β γ) (f : RationalKernel α β) : RationalKernel α γ where
  kernel := g.kernel ∘ₖ f.kernel
  markov := inferInstance
  rational x y := by
    refine ⟨(g.table.comp f.table).entry x y, (g.table.comp f.table).nonneg x y, ?_⟩
    rw [← Table.kernel_singleton, Table.kernel_comp, g.table_kernel, f.table_kernel]
@[simp] theorem RationalKernel.comp_table (g : RationalKernel β γ) (f : RationalKernel α β) :
    (g.comp f).table = g.table.comp f.table := by
  apply Table.kernel_injective
  rw [RationalKernel.table_kernel, Table.kernel_comp, g.table_kernel, f.table_kernel]
  rfl
/-- Change input and output coordinates through native kernel comap and map. -/
noncomputable def RationalKernel.relabel (k : RationalKernel α β) (e : α ≃ α') (f : β ≃ β') : RationalKernel α' β' where
  kernel := (k.kernel.comap e.symm (measurable_of_countable _)).map f
  markov := Kernel.IsMarkovKernel.map _ (measurable_of_countable _)
  rational x y := by
    obtain ⟨q,hq,h⟩ := k.rational (e.symm x) (f.symm y)
    refine ⟨q,hq,?_⟩
    rw [Kernel.map_apply' _ (measurable_of_countable _) _ (measurableSet_singleton _), Kernel.comap_apply']
    have hs : f ⁻¹' ({y} : Set β') = {f.symm y} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, ← Equiv.eq_symm_apply]
    rwa [hs]
omit [Fintype α] [Fintype β'] [MeasurableSingletonClass α] in
@[simp] theorem RationalKernel.relabel_singleton (k : RationalKernel α β) (e : α ≃ α') (f : β ≃ β') (x : α') (y : β') :
    (k.relabel e f).kernel x {y} = k.kernel (e.symm x) {f.symm y} := by
  rw [relabel, Kernel.map_apply' _ (measurable_of_countable _) _ (measurableSet_singleton _), Kernel.comap_apply']
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff, ← Equiv.eq_symm_apply]
@[simp] theorem RationalKernel.relabel_table_entry (k : RationalKernel α β) (e : α ≃ α') (f : β ≃ β') (x : α') (y : β') :
    (k.relabel e f).table.entry x y = k.table.entry (e.symm x) (f.symm y) := by
  apply mass_injective_nonneg ((k.relabel e f).table.nonneg x y) (k.table.nonneg _ _)
  rw [← Table.kernel_singleton, ← Table.kernel_singleton, table_kernel, table_kernel, relabel_singleton]
@[simp] theorem RationalKernel.relabel_refl (k : RationalKernel α β) : k.relabel (Equiv.refl α) (Equiv.refl β) = k := by
  apply RationalKernel.ext
  apply Kernel.ext
  intro x
  apply Measure.ext_of_singleton
  intro y
  simp
omit [Fintype α] [MeasurableSingletonClass α] in
@[simp] theorem RationalKernel.relabel_trans (k : RationalKernel α β)
    (e : α ≃ α') (f : β ≃ β') (e' : α' ≃ α'') (f' : β' ≃ β'') :
    (k.relabel e f).relabel e' f' = k.relabel (e.trans e') (f.trans f') := by
  apply RationalKernel.ext
  apply Kernel.ext
  intro x
  apply Measure.ext_of_singleton
  intro y
  simp
theorem RationalKernel.table_entry_eq (k : RationalKernel α β) (x : α) (y : β)
    (q : ℚ) (hq : 0 ≤ q) (h : k.kernel x {y} = mass q) : k.table.entry x y = q := by
  apply mass_injective_nonneg (k.table.nonneg x y) hq
  rw [← Table.kernel_singleton, k.table_kernel, h]

end Applications.Probability

namespace Applications.Probability
open MeasureTheory ProbabilityTheory
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]
  [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [MeasurableSpace δ] [MeasurableSingletonClass δ]
noncomputable def RationalKernel.ident (α : Type*) [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] : RationalKernel α α := by
  classical
  exact (Table.deterministic id).rationalKernel
@[simp] theorem RationalKernel.ident_kernel : (RationalKernel.ident α).kernel = Kernel.id := by
  classical
  exact Table.kernel_deterministic id
@[simp] theorem RationalKernel.comp_ident (k : RationalKernel α β) : k.comp (.ident α) = k := by
  apply RationalKernel.ext
  change k.kernel ∘ₖ (RationalKernel.ident α).kernel = k.kernel
  rw [ident_kernel, Kernel.comp_id]
@[simp] theorem RationalKernel.ident_comp (k : RationalKernel α β) : (RationalKernel.ident β).comp k = k := by
  apply RationalKernel.ext
  change (RationalKernel.ident β).kernel ∘ₖ k.kernel = k.kernel
  rw [ident_kernel, Kernel.id_comp]
theorem RationalKernel.comp_assoc (h : RationalKernel γ δ) (g : RationalKernel β γ) (f : RationalKernel α β) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply RationalKernel.ext
  exact Kernel.comp_assoc _ _ _
end Applications.Probability

namespace Applications.Probability
open ProbabilityTheory
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]
  [MeasurableSpace γ] [MeasurableSingletonClass γ]

@[simp] theorem Table.rationalKernel_comp (g : Table β γ) (f : Table α β) :
    (g.comp f).rationalKernel = g.rationalKernel.comp f.rationalKernel :=
  RationalKernel.ext (Table.kernel_comp g f)

@[simp] theorem RationalKernel.ident_table [DecidableEq α] :
    (RationalKernel.ident α).table = Table.deterministic id := by
  apply Table.kernel_injective
  rw [RationalKernel.table_kernel, RationalKernel.ident_kernel, Table.kernel_deterministic]
  rfl
end Applications.Probability
