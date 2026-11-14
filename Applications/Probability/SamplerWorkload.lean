import Applications.Probability.SamplerWork
import Applications.Probability.TableProducer
import Applications.Resources.Workload

/-!
# Measured resumable sampler workloads

The existing resource executor runs bit steps. A cached prepared row survives
pauses; loaders run initially and after each emission, including preparation of
the next row after the last observed output. Output lists are accumulated in
reverse order. Meter bookkeeping and proof erasure have no recursive charge.
-/
namespace Applications.Probability.SamplerWorkload
open SamplerWork
variable {α : Type}

/-- Completed-output handling is distinct from row outcome interpretation.
`finish` prices each output when materializing its chronological observation;
`admin` prices the finite-chain terminal administrative return. -/
structure Overhead where
  emit : ℕ
  finish : ℕ
  admin : ℕ

structure State (α : Type) where
  semantic : α
  row : PreparedRow α
  blockState : PreparedRow.State
  emitted : List α

def erase (z : State α) : TableProducer.State α := (z.semantic,z.blockState)

def Valid (p : α → PreparedRow α) (z : State α) : Prop := z.row=p z.semantic

/-- A loader returns both the actual prepared row and its declared charge. -/
abbrev Loader (α : Type) := α → Resources.Measured (PreparedRow α) ℕ

def beginWork (load : Loader α) (τ : Tariff) (x : α) (s : ℕ) :
    Resources.Measured (State α) ℕ :=
  Resources.bind (load x) fun row =>
    (⟨x,row,row.start s,[]⟩,initialization τ)

/-- One actual measured row step; acceptance alone loads and initializes the
next row. No previously read bit or cached preparation is executed again. -/
def tick (load : Loader α) (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape)
    (_ : Unit) (z : State α) : Resources.Measured (State α) ℕ :=
  match measuredStep z.row τ ω (z.blockState,0) with
  | .inr (q,c) => (⟨z.semantic,z.row,q,z.emitted⟩,c)
  | .inl ((a,t),c) =>
    Resources.bind (load a) fun row =>
      (⟨a,row,row.start t,a::z.emitted⟩,c+initialization τ+o.emit)

/-- Pure observation of the existing producer step, used only for erasure. -/
def observe (p : α → PreparedRow α) (ω : CoinPaths.Tape)
    (z : TableProducer.State α × List α) : TableProducer.State α × List α :=
  match TableProducer.step p ω z.1 with
  | .inl (a,q) => (q,a::z.2)
  | .inr q => (q,z.2)

def project (z : State α) : TableProducer.State α × List α := (erase z,z.emitted)

theorem beginWork_value (load : Loader α) (p : α → PreparedRow α)
    (hl : ∀ x,(load x).1=p x) (τ : Tariff) (x : α) (s : ℕ) :
    project (beginWork load τ x s).1=(TableProducer.start p x s,[]) ∧
      Valid p (beginWork load τ x s).1 := by
  simp [beginWork,Resources.bind,project,erase,TableProducer.start,Valid,hl]

theorem tick_value (load : Loader α) (p : α → PreparedRow α)
    (hl : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape)
    (z : State α) (hz : Valid p z) :
    project (tick load τ o ω () z).1=observe p ω (project z) ∧
      Valid p (tick load τ o ω () z).1 := by
  have hrow : z.row=p z.semantic := hz
  rw [tick,measuredStep_eq]
  cases h : z.row.step ω z.blockState with
  | inl a =>
    rcases a with ⟨a,t⟩
    simp [meter,h,Resources.bind,project,erase,observe,TableProducer.step,hl,← hrow,
      TableProducer.start,Valid]
  | inr q =>
    simp [meter,h,project,erase,observe,TableProducer.step,← hrow,Valid]

theorem run_valid (load : Loader α) (p : α → PreparedRow α)
    (hl : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape)
    (commands : List Unit) (z : State α) (hz : Valid p z) :
    Valid p (Resources.run (tick load τ o ω) commands z).1 :=
  Resources.run_invariant _ (Valid p) (fun u z h => by
    cases u; exact (tick_value load p hl τ o ω z h).2) commands z hz

theorem run_value (load : Loader α) (p : α → PreparedRow α)
    (hl : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape)
    (commands : List Unit) (z : State α) (hz : Valid p z) :
    project (Resources.run (tick load τ o ω) commands z).1=
      commands.foldl (fun z _ => observe p ω z) (project z) :=
  Resources.run_value_fusion _ _ project (Valid p)
    (fun u z h => by cases u; exact (tick_value load p hl τ o ω z h).2)
    (fun u z h => by cases u; exact (tick_value load p hl τ o ω z h).1) commands z hz

theorem evaluates_observe {p : α → PreparedRow α} {ω : CoinPaths.Tape}
    {s : TableProducer.State α} {r : α × TableProducer.State α} {k : ℕ}
    (h : Progress.Evaluates (TableProducer.step p ω) s r k) (acc : List α) :
    (List.replicate k ()).foldl (fun z _ => observe p ω z) (s,acc)=(r.2,r.1::acc) := by
  induction h with
  | done he => simp [List.replicate_succ,observe,he]
  | next he _ ih => simpa [List.replicate_succ,observe,he] using ih

theorem delivers_observe {p : α → PreparedRow α} {ω : CoinPaths.Tape}
    {s t : TableProducer.State α} {ys : List α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.step p ω) s ys t k) (acc : List α) :
    (List.replicate k ()).foldl (fun z _ => observe p ω z) (s,acc)=(t,ys.reverse++acc) := by
  induction h generalizing acc with
  | nil => simp
  | cons first rest ih =>
    rw [List.replicate_add,List.foldl_append,evaluates_observe first,ih]
    simp

/-- Any actual finite delivery is the stopped resource workload at its exact
bit count. This includes dependent successive rows and arbitrary partial starts. -/
theorem run_delivers (load : Loader α) (p : α → PreparedRow α)
    (hl : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape)
    (z : State α) (hz : Valid p z) {ys : List α} {t : TableProducer.State α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.step p ω) (erase z) ys t k) :
    project (Resources.run (tick load τ o ω) (List.replicate k ()) z).1=
      (t,ys.reverse++z.emitted) := by
  rw [run_value load p hl τ o ω _ z hz]
  exact delivers_observe h z.emitted

theorem tick_cost (load : Loader α) (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape)
    (z : State α) :
    (tick load τ o ω () z).2=sourceCharge z.row τ ω z.blockState+
      match z.row.step ω z.blockState with
      | .inl (a,_) => (load a).2+initialization τ+o.emit
      | .inr _ => 0 := by
  rw [tick,measuredStep_eq]
  cases h : z.row.step ω z.blockState with
  | inl a => rcases a with ⟨a,t⟩; simp [meter,h,Resources.bind,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  | inr q => simp [meter,h]

theorem tick_bound (load : Loader α) (p : α → PreparedRow α)
    (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape) (M L : ℕ)
    (hm : ∀ x,perBitBound (p x) τ≤M) (hl : ∀ x,(load x).2≤L)
    (z : State α) (hz : Valid p z) :
    (tick load τ o ω () z).2≤M+L+initialization τ+o.emit := by
  rw [tick_cost]
  have hc := sourceCharge_bound z.row τ ω z.blockState
  have hr : z.row=p z.semantic := hz
  have hx : perBitBound z.row τ≤M := by rw [hr]; exact hm z.semantic
  cases hs : z.row.step ω z.blockState with
  | inl a =>
    rcases a with ⟨a,t⟩
    change sourceCharge z.row τ ω z.blockState+((load a).2+initialization τ+o.emit)≤_
    simpa only [Nat.add_assoc] using Nat.add_le_add (hc.trans hx)
      (Nat.add_le_add_right (Nat.add_le_add_right (hl a) (initialization τ)) o.emit)
  | inr q => simp only [Nat.add_zero]; omega

theorem run_bound (load : Loader α) (p : α → PreparedRow α)
    (he : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape)
    (M L : ℕ) (hm : ∀ x,perBitBound (p x) τ≤M) (hl : ∀ x,(load x).2≤L)
    (commands : List Unit) (z : State α) (hz : Valid p z) :
    (Resources.run (tick load τ o ω) commands z).2≤
      commands.length*(M+L+initialization τ+o.emit) := by
  induction commands generalizing z with
  | nil => simp
  | cons u us ih =>
    cases u
    rw [Resources.run_cons]
    have h₁ := tick_bound load p τ o ω M L hm hl z hz
    have h₂ := ih _ (tick_value load p he τ o ω z hz).2
    simp only [List.length_cons]
    nlinarith

/-- Materialize the chronological output list. The declared per-output handling
charge covers reversing the accumulated list. Finite chains add one admin fee. -/
def finish (o : Overhead) (chain : Bool) (z : State α) :
    Resources.Measured (List α × TableProducer.State α) ℕ :=
  ((z.emitted.reverse,erase z),z.emitted.length*o.finish+if chain then o.admin else 0)

/-- Initialization is outside the empty post-initialization workload. -/
def workload (load : Loader α) (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape)
    (x : α) (s bits : ℕ) (chain : Bool) :
    Resources.Measured (List α × TableProducer.State α) ℕ :=
  Resources.bind (beginWork load τ x s) fun z =>
    Resources.bind (Resources.run (tick load τ o ω) (List.replicate bits ()) z) (finish o chain)

theorem workload_delivers (load : Loader α) (p : α → PreparedRow α)
    (he : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape)
    (x : α) (s : ℕ) {ys : List α} {t : TableProducer.State α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.step p ω) (TableProducer.start p x s) ys t k)
    (chain : Bool) : (workload load τ o ω x s k chain).1=(ys,t) := by
  have hi := beginWork_value load p he τ x s
  have hs : erase (beginWork load τ x s).1=TableProducer.start p x s := congrArg Prod.fst hi.1
  have ho := run_delivers load p he τ o ω (beginWork load τ x s).1 hi.2 (hs.symm ▸ h)
  have hem : (beginWork load τ x s).1.emitted=[] := congrArg Prod.snd hi.1
  rw [hem,List.append_nil] at ho
  have hstate := congrArg Prod.fst ho
  have hout := congrArg Prod.snd ho
  simp only [project] at hstate hout
  simp [workload,Resources.bind,finish,hout,hstate]

/-- The eager-prefetch finite-chain adapter preserves the original chain trace.
Its resource model retains the next prepared row even after its final output. -/
theorem workload_trace (load : Loader α) (p : α → PreparedRow α)
    (he : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape)
    {n x s ys t k} (h : RowChain.Trace p ω n x s ys t k) :
    (workload load τ o ω x s (k-1) true).1=
      (ys,TableProducer.start p (RowChain.finalState x ys) t) :=
  workload_delivers load p he τ o ω x s (TableProducer.delivers_of_trace h) true

theorem workload_admin (load : Loader α) (τ : Tariff) (o : Overhead)
    (ω : CoinPaths.Tape) (x : α) (s bits : ℕ) :
    (workload load τ o ω x s bits true).2=
      (workload load τ o ω x s bits false).2+o.admin := by
  simp [workload,Resources.bind,finish,Nat.add_assoc]

theorem workload_bound (load : Loader α) (p : α → PreparedRow α)
    (he : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape)
    (M L : ℕ) (hm : ∀ x,perBitBound (p x) τ≤M) (hl : ∀ x,(load x).2≤L)
    (x : α) (s : ℕ) {ys : List α} {t : TableProducer.State α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.step p ω) (TableProducer.start p x s) ys t k)
    (chain : Bool) : (workload load τ o ω x s k chain).2≤
      (load x).2+initialization τ+k*(M+L+initialization τ+o.emit)+
        ys.length*o.finish+(if chain then o.admin else 0) := by
  have hi := beginWork_value load p he τ x s
  have hs : erase (beginWork load τ x s).1=TableProducer.start p x s := congrArg Prod.fst hi.1
  have hd := run_delivers load p he τ o ω (beginWork load τ x s).1 hi.2 (hs.symm ▸ h)
  have hem : (beginWork load τ x s).1.emitted=[] := congrArg Prod.snd hi.1
  have hout := congrArg Prod.snd hd
  simp only [project,hem,List.append_nil] at hout
  have hb := run_bound load p he τ o ω M L hm hl (List.replicate k ()) _ hi.2
  simp only [List.length_replicate] at hb
  simp only [workload,Resources.bind,finish,hout,List.length_reverse]
  change (load x).2+initialization τ+(_+(_+_))≤_
  omega

theorem workload_zero (load : Loader α) (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape)
    (x : α) (s : ℕ) (chain : Bool) :
    (workload load τ o ω x s 0 chain).2=(load x).2+initialization τ+
      (if chain then o.admin else 0) := by
  simp [workload,beginWork,Resources.bind,finish,Nat.add_assoc]

/-- Two dependent rows are actual successive executions with their intermediate
cursor retained, and the same measured workload emits both outputs. -/
theorem workload_pair (load : Loader α) (p : α → PreparedRow α)
    (he : ∀ x,(load x).1=p x) (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape)
    {x a b : α} {s t u i j : ℕ}
    (h₁ : Progress.Evaluates ((p x).step ω) ((p x).start s) (a,t) i)
    (h₂ : Progress.Evaluates ((p a).step ω) ((p a).start t) (b,u) j) :
    (workload load τ o ω x s (i+j) false).1=([a,b],TableProducer.start p b u) := by
  apply workload_delivers load p he
  exact .cons (TableProducer.evaluates_of_row h₁)
    (.cons (TableProducer.evaluates_of_row h₂) (.nil _))

def preparationCost (m : ℕ) (τ : Tariff) : ℕ :=
  4*m*τ.arithmetic+3*m*(τ.entry+τ.projection)+m*τ.store

def prepareLoader [Fintype α] {m : ℕ} (t : Table α α) (e : Fin m ≃ α) (τ : Tariff) : Loader α :=
  fun x => prepareMetered t e x τ

theorem prepareLoader_value [Fintype α] {m : ℕ} (t : Table α α) (e : Fin m ≃ α)
    (τ : Tariff) (x : α) : (prepareLoader t e τ x).1=t.prepare e x := prepareMetered_value _ _ _ _

theorem prepareLoader_cost [Fintype α] {m : ℕ} (t : Table α α) (e : Fin m ≃ α)
    (τ : Tariff) (x : α) : (prepareLoader t e τ x).2=preparationCost m τ := prepareMetered_cost _ _ _ _

/-- Materialize each measured row once. Row-array storage is charged separately
from the row's internal weight storage. Lookup includes inverse enumeration. -/
def compileLoader [Fintype α] {m : ℕ} (t : Table α α) (e : Fin m ≃ α) (τ : Tariff) :
    Resources.Measured (Loader α) ℕ :=
  let data := Array.ofFn (fun i => prepareMetered t e (e i) τ)
  ((fun x => ((data[(e.symm x).val]'(by simp [data])).1,τ.lookup)),
    (∑ i : Fin m,(data[i.val]'(by simp [data])).2)+m*τ.store)

theorem compileLoader_value [Fintype α] {m : ℕ} (t : Table α α) (e : Fin m ≃ α)
    (τ : Tariff) (x : α) : ((compileLoader t e τ).1 x).1=t.compile e e x := by
  simp [compileLoader,prepareMetered_value,Table.compile_eq]

theorem compileLoader_setup [Fintype α] {m : ℕ} (t : Table α α) (e : Fin m ≃ α)
    (τ : Tariff) : (compileLoader t e τ).2=m*(preparationCost m τ+τ.store) := by
  simp [compileLoader,prepareMetered_cost,preparationCost]
  ring

theorem compileLoader_lookup [Fintype α] {m : ℕ} (t : Table α α) (e : Fin m ≃ α)
    (τ : Tariff) (x : α) : ((compileLoader t e τ).1 x).2=τ.lookup := rfl

def freeLoader (p : α → PreparedRow α) : Loader α := fun x => (p x,0)

private theorem tick_loader (load : Loader α) (p : α → PreparedRow α)
    (he : ∀ x,(load x).1=p x) (L : ℕ) (hc : ∀ x,(load x).2=L)
    (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape) (z : State α) :
    (tick load τ o ω () z).1=(tick (freeLoader p) τ o ω () z).1 ∧
    (tick load τ o ω () z).2+z.emitted.length*L=
      (tick (freeLoader p) τ o ω () z).2+(tick (freeLoader p) τ o ω () z).1.emitted.length*L := by
  cases h : measuredStep z.row τ ω (z.blockState,0) with
  | inl a =>
    rcases a with ⟨⟨a,t⟩,c⟩
    simp [tick,h,Resources.bind,he,hc,freeLoader]
    ring
  | inr q => simp [tick,h]

private theorem run_loader (load : Loader α) (p : α → PreparedRow α)
    (he : ∀ x,(load x).1=p x) (L : ℕ) (hc : ∀ x,(load x).2=L)
    (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape) (cs : List Unit) (z : State α) :
    (Resources.run (tick load τ o ω) cs z).1=(Resources.run (tick (freeLoader p) τ o ω) cs z).1 ∧
    (Resources.run (tick load τ o ω) cs z).2+z.emitted.length*L=
      (Resources.run (tick (freeLoader p) τ o ω) cs z).2+
        (Resources.run (tick (freeLoader p) τ o ω) cs z).1.emitted.length*L := by
  induction cs generalizing z with
  | nil => simp
  | cons u cs ih =>
    cases u
    obtain ⟨hv,hcost⟩ := tick_loader load p he L hc τ o ω z
    obtain ⟨hr,hrest⟩ := ih (tick (freeLoader p) τ o ω () z).1
    simp only [Resources.run_cons,hv]
    constructor
    · exact hr
    · change (tick load τ o ω () z).2+
        (Resources.run (tick load τ o ω) cs (tick (freeLoader p) τ o ω () z).1).2+
        z.emitted.length*L=(tick (freeLoader p) τ o ω () z).2+
        (Resources.run (tick (freeLoader p) τ o ω) cs (tick (freeLoader p) τ o ω () z).1).2+
        (Resources.run (tick (freeLoader p) τ o ω) cs (tick (freeLoader p) τ o ω () z).1).1.emitted.length*L
      omega

/-- Every stopped n-output workload loads exactly n+1 rows, including the
initial row and the next-row state retained after its last output. -/
theorem workload_loader_cost (load : Loader α) (p : α → PreparedRow α)
    (he : ∀ x,(load x).1=p x) (L : ℕ) (hc : ∀ x,(load x).2=L)
    (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape) (x : α) (s : ℕ)
    {ys : List α} {t : TableProducer.State α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.step p ω) (TableProducer.start p x s) ys t k)
    (chain : Bool) :
    (workload load τ o ω x s k chain).2=
      (workload (freeLoader p) τ o ω x s k chain).2+(ys.length+1)*L := by
  let z := (beginWork (freeLoader p) τ x s).1
  have hi : (beginWork load τ x s).1=z := by simp [z,beginWork,Resources.bind,he,freeLoader]
  obtain ⟨hv,hcost⟩ := run_loader load p he L hc τ o ω (List.replicate k ()) z
  have hz : Valid p z := rfl
  have hd := run_delivers (freeLoader p) p (fun _ => rfl) τ o ω z hz h
  have hout := congrArg Prod.snd hd
  change (Resources.run (tick (freeLoader p) τ o ω) (List.replicate k ()) z).1.emitted=ys.reverse++[] at hout
  simp only [List.append_nil] at hout
  have hzlen : z.emitted.length=0 := rfl
  rw [hzlen,hout,List.length_reverse] at hcost
  simp only [Nat.zero_mul,Nat.add_zero] at hcost
  simp only [workload,Resources.bind,hi,hv,finish]
  change (load x).2+initialization τ+(_+_)=0+initialization τ+(_+_)+(ys.length+1)*L
  rw [hc]
  simp only [Nat.add_mul,Nat.one_mul]
  dsimp only [z] at hcost ⊢
  omega

/-- Materialization amortizes precisely when setup plus retained-row lookups
costs no more than the same n+1 executed per-draw preparations. -/
theorem compile_amortizes [Fintype α] {m : ℕ} (t : Table α α) (e : Fin m ≃ α)
    (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape) (x : α) (s : ℕ)
    {ys : List α} {z : TableProducer.State α} {k : ℕ}
    (h : Progress.Delivers (TableProducer.step (t.prepare e) ω)
      (TableProducer.start (t.prepare e) x s) ys z k) (chain : Bool) :
    (compileLoader t e τ).2+(workload (compileLoader t e τ).1 τ o ω x s k chain).2≤
      (workload (prepareLoader t e τ) τ o ω x s k chain).2 ↔
    m*(preparationCost m τ+τ.store)+(ys.length+1)*τ.lookup≤(ys.length+1)*preparationCost m τ := by
  rw [workload_loader_cost (compileLoader t e τ).1 (t.prepare e)
    (fun x => (compileLoader_value t e τ x).trans (Table.compile_eq _ _ _ _)) τ.lookup
    (compileLoader_lookup _ _ _) τ o ω x s h chain,
    workload_loader_cost (prepareLoader t e τ) (t.prepare e) (prepareLoader_value _ _ _)
      (preparationCost m τ) (prepareLoader_cost _ _ _) τ o ω x s h chain,compileLoader_setup]
  omega

/-- Pause/resume is existing measured composition, retaining cached state and
partial block. Charges add in execution order with no initialization replay. -/
theorem resume (load : Loader α) (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape)
    (first later : List Unit) (z : State α) :
    Resources.run (tick load τ o ω) (first++later) z=
      Resources.bind (Resources.run (tick load τ o ω) first z)
        (Resources.run (tick load τ o ω) later) := Resources.run_append _ _ _ _

theorem reweight {C : Type} [AddMonoid C] (h : ℕ →+ C)
    (load : Loader α) (τ : Tariff) (o : Overhead) (ω : CoinPaths.Tape)
    (commands : List Unit) (z : State α) :
    Resources.reweight h (Resources.run (tick load τ o ω) commands z)=
      Resources.run (fun u z => Resources.reweight h (tick load τ o ω u z)) commands z :=
  Resources.reweight_run _ _ _ _

end Applications.Probability.SamplerWorkload
