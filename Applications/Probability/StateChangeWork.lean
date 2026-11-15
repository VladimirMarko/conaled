import Applications.Probability.InitializedProducerWork

/-! Measured execution of the existing state-change filter. Every completed raw
row loads its successor, even when its unchanged output is suppressed. -/
namespace Applications.Probability.StateChangeWork
open SamplerWork SamplerWorkload
variable {α : Type} [DecidableEq α]

/-- Equality testing is charged on every completed raw transition. -/
def tick (load : Loader α) (τ : Tariff) (o : Overhead) (compareCost : ℕ)
    (ω : CoinPaths.Tape) (_ : Unit) (z : State α) : Resources.Measured (State α) ℕ :=
  match measuredStep z.row τ ω (z.blockState,0) with
  | .inr (q,c) => (⟨z.semantic,z.row,q,z.emitted⟩,c)
  | .inl ((a,t),c) => Resources.bind (load a) fun row =>
      (⟨a,row,row.start t,if a=z.semantic then z.emitted else a::z.emitted⟩,
        c+initialization τ+compareCost+(if a=z.semantic then 0 else o.emit))

def observe (p : α → PreparedRow α) (ω : CoinPaths.Tape)
    (z : TableProducer.State α × List α) : TableProducer.State α × List α :=
  match TableProducer.changes p ω z.1 with
  | .inl (a,q) => (q,a::z.2)
  | .inr q => (q,z.2)

theorem tick_value (load : Loader α) (p : α → PreparedRow α)
    (hl : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (compareCost : ℕ)
    (ω : CoinPaths.Tape) (z : State α) (hz : Valid p z) :
    project (tick load τ o compareCost ω () z).1=observe p ω (project z) ∧
      Valid p (tick load τ o compareCost ω () z).1 := by
  have hrow : z.row=p z.semantic := hz
  rw [tick,measuredStep_eq]
  cases h : z.row.step ω z.blockState with
  | inl a =>
    rcases a with ⟨a,t⟩
    by_cases ha : a=z.semantic <;>
      simp [meter,h,Resources.bind,project,erase,observe,TableProducer.changes,
        TableProducer.step,hl,← hrow,TableProducer.start,Valid,ha]
  | inr q =>
    simp [meter,h,project,erase,observe,TableProducer.changes,
      TableProducer.step,← hrow,Valid]

theorem run_value (load : Loader α) (p : α → PreparedRow α)
    (hl : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (compareCost : ℕ)
    (ω : CoinPaths.Tape) (commands : List Unit) (z : State α) (hz : Valid p z) :
    project (Resources.run (tick load τ o compareCost ω) commands z).1=
      commands.foldl (fun z _ => observe p ω z) (project z) :=
  Resources.run_value_fusion _ _ project (Valid p)
    (fun u z h => by cases u; exact (tick_value load p hl τ o compareCost ω z h).2)
    (fun u z h => by cases u; exact (tick_value load p hl τ o compareCost ω z h).1)
    commands z hz

theorem evaluates_observe {p : α → PreparedRow α} {ω : CoinPaths.Tape}
    {s : TableProducer.State α} {r : α × TableProducer.State α} {k : ℕ}
    (h : Progress.Evaluates (TableProducer.changes p ω) s r k) (acc : List α) :
    (List.replicate k ()).foldl (fun z _ => observe p ω z) (s,acc)=(r.2,r.1::acc) := by
  induction h with
  | done he => simp [List.replicate_succ,observe,he]
  | next he _ ih => simpa [List.replicate_succ,observe,he] using ih

theorem delivers_observe {p : α → PreparedRow α} {ω : CoinPaths.Tape}
    {s t : TableProducer.State α} {ys : List α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.changes p ω) s ys t k) (acc : List α) :
    (List.replicate k ()).foldl (fun z _ => observe p ω z) (s,acc)=(t,ys.reverse++acc) := by
  induction h generalizing acc with
  | nil => simp
  | cons first rest ih =>
    rw [List.replicate_add,List.foldl_append,evaluates_observe first,ih]
    simp

theorem run_delivers (load : Loader α) (p : α → PreparedRow α)
    (hl : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (compareCost : ℕ)
    (ω : CoinPaths.Tape) (z : State α) (hz : Valid p z)
    {ys : List α} {t : TableProducer.State α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.changes p ω) (erase z) ys t k) :
    project (Resources.run (tick load τ o compareCost ω) (List.replicate k ()) z).1=
      (t,ys.reverse++z.emitted) := by
  rw [run_value load p hl τ o compareCost ω _ z hz]
  exact delivers_observe h z.emitted

/-- Actual per-bit charge; suppressed returns still prepare and initialize the
successor row and pay the comparison, but do not pay output emission. -/
theorem tick_cost (load : Loader α) (τ : Tariff) (o : Overhead) (compareCost : ℕ)
    (ω : CoinPaths.Tape) (z : State α) :
    (tick load τ o compareCost ω () z).2=sourceCharge z.row τ ω z.blockState+
      match z.row.step ω z.blockState with
      | .inl (a,_) => (load a).2+initialization τ+compareCost+
          (if a=z.semantic then 0 else o.emit)
      | .inr _ => 0 := by
  rw [tick,measuredStep_eq]
  cases h : z.row.step ω z.blockState with
  | inl a => rcases a with ⟨a,t⟩; simp [meter,h,Resources.bind,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  | inr q => simp [meter,h]

theorem tick_bound (load : Loader α) (p : α → PreparedRow α)
    (τ : Tariff) (o : Overhead) (compareCost : ℕ) (ω : CoinPaths.Tape) (M L : ℕ)
    (hm : ∀ x,perBitBound (p x) τ≤M) (hl : ∀ x,(load x).2≤L)
    (z : State α) (hz : Valid p z) :
    (tick load τ o compareCost ω () z).2≤M+L+initialization τ+compareCost+o.emit := by
  rw [tick_cost]
  have hc := sourceCharge_bound z.row τ ω z.blockState
  have hr : z.row=p z.semantic := hz
  have hx : perBitBound z.row τ≤M := by rw [hr]; exact hm z.semantic
  cases hs : z.row.step ω z.blockState with
  | inl a =>
    rcases a with ⟨a,t⟩
    have hload := hl a
    change sourceCharge z.row τ ω z.blockState+((load a).2+initialization τ+compareCost+
      (if a=z.semantic then 0 else o.emit))≤_
    split_ifs <;> omega
  | inr q => simp only [Nat.add_zero]; omega

theorem run_bound (load : Loader α) (p : α → PreparedRow α)
    (he : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (compareCost : ℕ)
    (ω : CoinPaths.Tape) (M L : ℕ) (hm : ∀ x,perBitBound (p x) τ≤M)
    (hl : ∀ x,(load x).2≤L) (commands : List Unit) (z : State α) (hz : Valid p z) :
    (Resources.run (tick load τ o compareCost ω) commands z).2≤
      commands.length*(M+L+initialization τ+compareCost+o.emit) := by
  induction commands generalizing z with
  | nil => simp
  | cons u us ih =>
    cases u
    rw [Resources.run_cons]
    have h₁ := tick_bound load p τ o compareCost ω M L hm hl z hz
    have h₂ := ih _ (tick_value load p he τ o compareCost ω z hz).2
    simp only [List.length_cons]
    nlinarith

def workload (load : Loader α) (τ : Tariff) (o : Overhead) (compareCost : ℕ)
    (ω : CoinPaths.Tape) (x : α) (s bits : ℕ) :
    Resources.Measured (List α × TableProducer.State α) ℕ :=
  Resources.bind (beginWork load τ x s) fun z =>
    Resources.bind (Resources.run (tick load τ o compareCost ω) (List.replicate bits ()) z)
      (finish o false)

theorem workload_delivers (load : Loader α) (p : α → PreparedRow α)
    (he : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (compareCost : ℕ)
    (ω : CoinPaths.Tape) (x : α) (s : ℕ) {ys : List α} {t : TableProducer.State α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.changes p ω) (TableProducer.start p x s) ys t k) :
    (workload load τ o compareCost ω x s k).1=(ys,t) := by
  have hi := beginWork_value load p he τ x s
  have hs : erase (beginWork load τ x s).1=TableProducer.start p x s := congrArg Prod.fst hi.1
  have hd := run_delivers load p he τ o compareCost ω (beginWork load τ x s).1 hi.2 (hs.symm ▸ h)
  have hem : (beginWork load τ x s).1.emitted=[] := congrArg Prod.snd hi.1
  rw [hem,List.append_nil] at hd
  have hstate := congrArg Prod.fst hd
  have hout := congrArg Prod.snd hd
  simp only [project] at hstate hout
  simp [workload,Resources.bind,finish,hout,hstate]

theorem workload_bound (load : Loader α) (p : α → PreparedRow α)
    (he : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (compareCost : ℕ)
    (ω : CoinPaths.Tape) (M L : ℕ) (hm : ∀ x,perBitBound (p x) τ≤M)
    (hl : ∀ x,(load x).2≤L) (x : α) (s : ℕ)
    {ys : List α} {t : TableProducer.State α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.changes p ω) (TableProducer.start p x s) ys t k) :
    (workload load τ o compareCost ω x s k).2≤
      (load x).2+initialization τ+k*(M+L+initialization τ+compareCost+o.emit)+ys.length*o.finish := by
  have hi := beginWork_value load p he τ x s
  have hs : erase (beginWork load τ x s).1=TableProducer.start p x s := congrArg Prod.fst hi.1
  have hd := run_delivers load p he τ o compareCost ω (beginWork load τ x s).1 hi.2 (hs.symm ▸ h)
  have hem : (beginWork load τ x s).1.emitted=[] := congrArg Prod.snd hi.1
  have hout := congrArg Prod.snd hd
  simp only [project,hem,List.append_nil] at hout
  have hb := run_bound load p he τ o compareCost ω M L hm hl (List.replicate k ()) _ hi.2
  simp only [List.length_replicate] at hb
  simp only [workload,Resources.bind,finish,hout,List.length_reverse,Bool.false_eq_true,ite_false,Nat.add_zero]
  change (load x).2+initialization τ+(_+_)≤_
  omega

open CoinPaths MeasureTheory
private theorem tick_bit (load : Loader α) (τ : Tariff) (o : Overhead) (compareCost : ℕ) (ω η : Tape)
    (z : State α) (h : ω z.blockState.1=η z.blockState.1) :
    StateChangeWork.tick load τ o compareCost ω () z=StateChangeWork.tick load τ o compareCost η () z := by
  simp [StateChangeWork.tick,measuredStep,BoundedUniform.step,h]

/-- Finite workload observations are measurable by splitting on the one bit
inspected at each tick. Cached rows need no measurable function-space structure. -/
theorem measurable_run (load : Loader α) (τ : Tariff) (o : Overhead) (compareCost : ℕ)
    (commands : List Unit) (z : State α) :
    Measurable (fun ω : Tape =>
      ((Resources.run (StateChangeWork.tick load τ o compareCost ω) commands z).1.emitted.length,
       (Resources.run (StateChangeWork.tick load τ o compareCost ω) commands z).2)) := by
  induction commands generalizing z with
  | nil => simpa only [Resources.run_nil] using (measurable_const : Measurable (fun _ : Tape => (z.emitted.length,(0 : ℕ))))
  | cons u cs ih =>
    cases u
    let a := StateChangeWork.tick load τ o compareCost (fun _ => true) () z
    let b := StateChangeWork.tick load τ o compareCost (fun _ => false) () z
    have he : (fun ω : Tape =>
        ((Resources.run (StateChangeWork.tick load τ o compareCost ω) (()::cs) z).1.emitted.length,
         (Resources.run (StateChangeWork.tick load τ o compareCost ω) (()::cs) z).2))=
        fun ω => if ω z.blockState.1=true then
          ((Resources.run (StateChangeWork.tick load τ o compareCost ω) cs a.1).1.emitted.length,
            a.2+(Resources.run (StateChangeWork.tick load τ o compareCost ω) cs a.1).2)
        else ((Resources.run (StateChangeWork.tick load τ o compareCost ω) cs b.1).1.emitted.length,
            b.2+(Resources.run (StateChangeWork.tick load τ o compareCost ω) cs b.1).2) := by
      funext ω
      cases hb : ω z.blockState.1
      · have ht := tick_bit load τ o compareCost ω (fun _ => false) z hb
        simp [Resources.run_cons,ht,b]
      · have ht := tick_bit load τ o compareCost ω (fun _ => true) z hb
        simp [Resources.run_cons,ht,a]
    rw [he]
    have hbit : Measurable (fun ω : Tape => ω z.blockState.1) := measurable_pi_apply _
    exact Measurable.ite (hbit (measurableSet_singleton true))
      ((ih a.1).fst.prodMk (measurable_const.add (ih a.1).snd))
      ((ih b.1).fst.prodMk (measurable_const.add (ih b.1).snd))

theorem measurable_workload (load : Loader α) (τ : Tariff) (o : Overhead) (compareCost : ℕ)
    (x : α) (s k : ℕ)  :
    Measurable (fun ω : Tape => (StateChangeWork.workload load τ o compareCost ω x s k).2) := by
  have hm := measurable_run load τ o compareCost (List.replicate k ()) (beginWork load τ x s).1
  exact measurable_const.add (hm.snd.add ((hm.fst.mul measurable_const).add measurable_const))

end Applications.Probability.StateChangeWork
