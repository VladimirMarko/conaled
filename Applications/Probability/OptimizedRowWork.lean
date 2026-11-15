import Applications.Probability.NormalizedRow
import Applications.Probability.LinearRowSelector
import Applications.Probability.SamplerWorkload
import Applications.Probability.InitializedProducer

/-!
# Normalized preparation and linear selection in measured workloads

LCM is an explicitly priced natural-number primitive, like the existing model's
logarithm and arithmetic. Prices do not claim arithmetic bit complexity. Row
weights and compiled rows occupy real arrays, with construction charged per entry.
Linear selection needs no cumulative cache. Its declared lookup price includes
stored weight access; no constant-time arbitrary-list indexing is assumed.
-/
namespace Applications.Probability.OptimizedRowWork
open SamplerWork CoinPaths MeasureTheory
open scoped BigOperators ENNReal

structure Tariff where
  base : SamplerWork.Tariff
  lcm : ℕ

/-- The same reverse LCM fold used in normalization supplies its own operation
count. Numerator conversion, quotient and multiplication are charged per weight. -/
def prepareMetered {α β : Type} [Fintype β] {m : ℕ}
    (t : Table α β) (e : Fin m ≃ β) (x : α) (τ : Tariff) : PreparedRow β × ℕ :=
  let q := fun i => t.entry x (e i)
  let d := NormalizedWeights.common m (fun i => (q i).den)
  let data := Array.ofFn (fun i => ((q i).num.toNat*(d.1/(q i).den),(3 : ℕ)))
  let row : PreparedRow β :=
    { size := m
      weight := fun i => (data[i.val]'(by simp [data])).1
      outcome := e
      total := d.1
      total_eq := by
        dsimp [data,d]
        simp only [Array.getElem_ofFn]
        exact (NormalizedWeights.sum_weight q (fun i => t.nonneg x (e i))
          ((e.sum_comp (t.entry x)).trans (t.sum_row x))).symm
      positive := NormalizedWeights.denominator_pos q }
  (row,d.2*τ.lcm+(∑ i : Fin m,(data[i.val]'(by simp [data])).2)*τ.base.arithmetic+
    3*m*(τ.base.entry+τ.base.projection)+m*τ.base.store)

theorem prepareMetered_value {α β : Type} [Fintype β] {m : ℕ}
    (t : Table α β) (e : Fin m ≃ β) (x : α) (τ : Tariff) :
    (prepareMetered t e x τ).1=t.prepareNormalized e x := by
  simp [prepareMetered,Table.prepareNormalized,NormalizedWeights.denominator]

def preparationCost (m : ℕ) (τ : Tariff) : ℕ :=
  m*τ.lcm+3*m*τ.base.arithmetic+3*m*(τ.base.entry+τ.base.projection)+m*τ.base.store

theorem prepareMetered_cost {α β : Type} [Fintype β] {m : ℕ}
    (t : Table α β) (e : Fin m ≃ β) (x : α) (τ : Tariff) :
    (prepareMetered t e x τ).2=preparationCost m τ := by
  simp [prepareMetered,preparationCost,NormalizedWeights.common_count]
  ring_nf
  simp

/-- Compilation charges each input-enumeration evaluation separately from the
row-entry evaluations. Each later lookup includes inverse enumeration. -/
def compileLoader {α : Type} [Fintype α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (τ : Tariff) : SamplerWorkload.Loader α × ℕ :=
  let rows := Array.ofFn (fun i => prepareMetered t e (e i) τ)
  (fun x => ((rows[(e.symm x).val]'(by simp [rows])).1,τ.base.lookup),
    (∑ i : Fin m,(rows[i.val]'(by simp [rows])).2)+m*(τ.base.store+τ.base.entry))

theorem compileLoader_value {α : Type} [Fintype α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (τ : Tariff) (x : α) :
    ((compileLoader t e τ).1 x).1=t.prepareNormalized e x := by
  simp [compileLoader,prepareMetered_value]

theorem compileLoader_setup {α : Type} [Fintype α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (τ : Tariff) :
    (compileLoader t e τ).2=m*preparationCost m τ+m*(τ.base.store+τ.base.entry) := by
  simp [compileLoader,prepareMetered_cost]

theorem compileLoader_lookup {α : Type} [Fintype α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (τ : Tariff) (x : α) :
    ((compileLoader t e τ).1 x).2=τ.base.lookup := rfl

/-- Each retained row holds exactly m multiplicities; compiling all m rows
adds m references. The count excludes immutable enumeration/function closures. -/
def storedEntries (m : ℕ) : ℕ := m*m+m

def sourceCharge {β : Type} (p : PreparedRow β) (τ : SamplerWork.Tariff) (ω : Tape)
    (q : PreparedRow.State) : ℕ :=
  match BoundedUniform.step p.total ω q with
  | .inl a => bitBase τ+τ.arithmetic+(LinearRowSelector.rowSelect p τ a.1).2
  | .inr _ => bitBase τ+τ.arithmetic+if q.2.1≤1 then initialization τ else 0

def measuredStep {β : Type} (p : PreparedRow β) (τ : SamplerWork.Tariff) (ω : Tape) :
    Progress.Machine (PreparedRow.State × ℕ) ((β × ℕ) × ℕ) := fun (q,c) =>
  match BoundedUniform.step p.total ω q with
  | .inl a =>
    let r := LinearRowSelector.rowSelect p τ a.1
    .inl ((r.1,a.2),c+bitBase τ+τ.arithmetic+r.2)
  | .inr q' => .inr (q',c+bitBase τ+τ.arithmetic+if q.2.1≤1 then initialization τ else 0)

theorem measuredStep_eq {β : Type} (p : PreparedRow β) (τ : SamplerWork.Tariff) (ω : Tape) :
    measuredStep p τ ω=SamplerWork.meter (p.step ω) (sourceCharge p τ ω) := by
  funext qc
  rcases qc with ⟨q,c⟩
  cases h : BoundedUniform.step p.total ω q with
  | inl a => simp [measuredStep,SamplerWork.meter,PreparedRow.step,Progress.mapReturn,sourceCharge,h,
      LinearRowSelector.rowSelect_value,Nat.add_assoc]
  | inr q' => simp [measuredStep,SamplerWork.meter,PreparedRow.step,Progress.mapReturn,sourceCharge,h,Nat.add_assoc]

def perBitBound {β : Type} (p : PreparedRow β) (τ : SamplerWork.Tariff) : ℕ :=
  bitBase τ+τ.arithmetic+initialization τ+
    (p.size*(τ.lookup+2*τ.arithmetic)+τ.arithmetic+τ.outcome)

theorem sourceCharge_bound {β : Type} (p : PreparedRow β) (τ : SamplerWork.Tariff) (ω : Tape)
    (q : PreparedRow.State) : sourceCharge p τ ω q≤perBitBound p τ := by
  unfold sourceCharge
  split
  · rename_i a he
    have h := LinearRowSelector.rowSelect_bound p τ a.1
    unfold perBitBound
    omega
  · split <;> (unfold perBitBound; omega)

theorem measured_evaluates {β : Type} (p : PreparedRow β) (τ : SamplerWork.Tariff) {ω : Tape}
    {s : ℕ} {a : β} {t k : ℕ}
    (h : Progress.Evaluates (p.step ω) (p.start s) (a,t) k) :
    ∃ w, Progress.Evaluates (measuredStep p τ ω) (p.start s,initialization τ) ((a,t),w) k ∧
      w ≤ initialization τ+k*perBitBound p τ := by
  rw [measuredStep_eq]
  exact SamplerWork.meter_evaluates h (sourceCharge_bound p τ ω) (initialization τ)

theorem measured_evaluates_inv {β : Type} (p : PreparedRow β) (τ : SamplerWork.Tariff) {ω : Tape}
    {s : ℕ} {a : β} {t k w : ℕ}
    (h : Progress.Evaluates (measuredStep p τ ω) (p.start s,initialization τ) ((a,t),w) k) :
    Progress.Evaluates (p.step ω) (p.start s) (a,t) k := by
  rw [measuredStep_eq] at h
  exact SamplerWork.meter_evaluates_inv h

open SamplerWorkload

/-- The existing eager loader and output policy, with linear selection. -/
def tick {α : Type} (load : Loader α) (τ : SamplerWork.Tariff) (o : Overhead) (ω : Tape)
    (_ : Unit) (z : State α) : Resources.Measured (State α) ℕ :=
  match measuredStep z.row τ ω (z.blockState,0) with
  | .inr (q,c) => (⟨z.semantic,z.row,q,z.emitted⟩,c)
  | .inl ((a,t),c) =>
    Resources.bind (load a) fun row =>
      (⟨a,row,row.start t,a::z.emitted⟩,c+initialization τ+o.emit)

theorem tick_value {α : Type} (load : Loader α) (τ : SamplerWork.Tariff) (o : Overhead)
    (ω : Tape) (u : Unit) (z : State α) :
    (tick load τ o ω u z).1=(SamplerWorkload.tick load τ o ω u z).1 := by
  cases h : BoundedUniform.step z.row.total ω z.blockState <;>
    simp [tick,measuredStep,SamplerWorkload.tick,SamplerWork.measuredStep,h,
      LinearRowSelector.rowSelect_value,SamplerWork.rowSelect_value,Resources.bind]

theorem run_value {α : Type} (load : Loader α) (τ : SamplerWork.Tariff) (o : Overhead)
    (ω : Tape) (commands : List Unit) (z : State α) :
    (Resources.run (tick load τ o ω) commands z).1=
      (Resources.run (SamplerWorkload.tick load τ o ω) commands z).1 := by
  induction commands generalizing z with
  | nil => rfl
  | cons u us ih => simp only [Resources.run_cons,ih,tick_value]

def workload {α : Type} (load : Loader α) (τ : SamplerWork.Tariff) (o : Overhead) (ω : Tape)
    (x : α) (s bits : ℕ) (chain : Bool) :
    Resources.Measured (List α × TableProducer.State α) ℕ :=
  Resources.bind (beginWork load τ x s) fun z =>
    Resources.bind (Resources.run (tick load τ o ω) (List.replicate bits ()) z) (finish o chain)

theorem workload_value {α : Type} (load : Loader α) (τ : SamplerWork.Tariff) (o : Overhead) (ω : Tape)
    (x : α) (s bits : ℕ) (chain : Bool) :
    (workload load τ o ω x s bits chain).1=
      (SamplerWorkload.workload load τ o ω x s bits chain).1 := by
  simp only [workload,SamplerWorkload.workload,Resources.bind_value,run_value]

theorem workload_delivers {α : Type} (load : Loader α) (p : α → PreparedRow α)
    (hl : ∀ x,(load x).1=p x) (τ : SamplerWork.Tariff) (o : Overhead) (ω : Tape)
    (x : α) (s : ℕ) {ys : List α} {z : TableProducer.State α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.step p ω) (TableProducer.start p x s) ys z k)
    (chain : Bool) : (workload load τ o ω x s k chain).1=(ys,z) := by
  rw [workload_value]
  exact SamplerWorkload.workload_delivers load p hl τ o ω x s h chain

/-- Explicit preparation cost comparison; savings depend on the primitive LCM tariff. -/
theorem preparation_comparison (m : ℕ) (τ : Tariff) :
    preparationCost m τ≤SamplerWorkload.preparationCost m τ.base ↔
      m*τ.lcm≤m*τ.base.arithmetic := by
  unfold preparationCost SamplerWorkload.preparationCost
  constructor <;> intro h <;> nlinarith

/-- The declared storage measure follows the sizes of the actual compiled rows. -/
def compileStorage {α : Type} [Fintype α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (τ : Tariff) : ℕ :=
  let rows := Array.ofFn (fun i => prepareMetered t e (e i) τ)
  rows.size+∑ i : Fin m,(rows[i.val]'(by simp [rows])).1.size

theorem compileStorage_eq {α : Type} [Fintype α] {m : ℕ}
    (t : Table α α) (e : Fin m ≃ α) (τ : Tariff) :
    compileStorage t e τ=storedEntries m := by
  simp [compileStorage,prepareMetered_value,Table.prepareNormalized,storedEntries,Nat.add_comm]

end Applications.Probability.OptimizedRowWork

namespace Applications.Probability.Table
open CoinPaths MeasureTheory
open scoped ENNReal
variable {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}

theorem normalized_prefix_mass (t : Table α α) (e : Fin m ≃ α) (x : α) (s : ℕ) (ys : List α) :
    law (TableProducer.prefixEvent (t.prepareNormalized e) x s ys)=mass (RowChain.pathMass t x ys) :=
  TableProducer.prefix_mass_rows t (t.prepareNormalized e) (t.prepareNormalized_returns_mass e) x s ys

theorem normalized_endpoint_mass (t : Table α α) (e : Fin m ≃ α) (n : ℕ) (x y : α) (s : ℕ) :
    law (TableProducer.endpointEvent (t.prepareNormalized e) n x s y)=mass ((t.steps n).entry x y) := by
  rw [TableProducer.endpoint_eq]
  exact RowChain.rows_final_mass t _ (t.prepareNormalized_returns_mass e) n x y s

omit [DecidableEq α] in
theorem normalized_productive (t : Table α α) (e : Fin m ≃ α) (x : α) (s : ℕ) :
    ProbabilityProgress.AlmostSureProductive law (TableProducer.step (t.prepareNormalized e))
      (fun _ => TableProducer.start (t.prepareNormalized e) x s) :=
  TableProducer.almostSureProductive_rows _ x s

theorem normalized_stationary_blocks (initial : Table Unit α) (t : Table α α) (e : Fin m ≃ α)
    (hπ : ∀ a, ∑ x, mass (initial.entry () x)*mass (t.entry x a)=mass (initial.entry () a))
    (n s : ℕ) (ys : List α) :
    law (InitializedProducer.blockEvent (initial.prepareNormalized e ()) (t.prepareNormalized e) n s ys)=
      ∑ a, mass (initial.entry () a)*mass (RowChain.pathMass t a ys) :=
  InitializedProducer.stationary_blocks_rows t _ _ _
    (initial.prepareNormalized_returns_mass e ()) (t.prepareNormalized_returns_mass e) hπ n s ys

theorem normalized_joint (initial : Table Unit α) (t : Table α α) (e : Fin m ≃ α)
    (s : ℕ) (a : α) (ys : List α) :
    law (InitializedProducer.jointEvent (initial.prepareNormalized e ()) (t.prepareNormalized e) s a ys)=
      mass (initial.entry () a)*mass (RowChain.pathMass t a ys) := by
  rw [InitializedProducer.joint_mass,initial.prepareNormalized_returns_mass,normalized_prefix_mass]
end Applications.Probability.Table

namespace Applications.Probability.FiniteMH
open CoinPaths MeasureTheory
open scoped ENNReal

theorem normalized_stationary_blocks {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (model : FiniteMH α) {m : ℕ} (e : Fin m ≃ α) (n s : ℕ) (ys : List α) :
    law (InitializedProducer.blockEvent ((InitializedProducer.targetInitial model).prepareNormalized e ())
      (model.transition.prepareNormalized e) n s ys)=
      ∑ a, mass (model.target a)*mass (RowChain.pathMass model.transition a ys) := by
  apply Table.normalized_stationary_blocks
  intro a
  change ∑ x, mass (model.target x)*mass (model.transition.entry x a)=mass (model.target a)
  simp_rw [← mass_mul _ _ (model.target_nonneg _)]
  rw [← mass_sum _ _ (fun x _ => mul_nonneg (model.target_nonneg x) (model.transition.nonneg x a)),
    model.stationary]
end Applications.Probability.FiniteMH
