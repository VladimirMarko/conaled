import Applications.Sequences.BoundedSummary
import Applications.Optimization.Basic

/-! Exact costs for indexed bounded buffers (#239). Tariffs count declared
primitive operations, not Lean allocation or wall-clock performance. -/
namespace Resources.BoundedSummary
open Sequences.BoundedSummary
open Sequences.BoundedSummary.Buffer

structure Tariff where
  visit : Nat := 1
  combine : Nat := 1
  cacheWrite : Nat := 1
  cacheRead : Nat := 1
  slotWrite : Nat := 1
  emit : Nat := 1
  control : Nat := 1
  deriving DecidableEq, Repr

def scanM (t : Tariff) : (n : Nat) → (Fin n → Bool) → Measured Parity Nat
  | 0, _ => (1,t.visit)
  | n+1,f => let r := scanM t n (fun i => f i.succ)
             (measure (f 0) * r.1,t.visit+t.combine+r.2)

theorem scanM_exact (t : Tariff) (n : Nat) (f : Fin n → Bool) :
    scanM t n f = (scan n f,t.visit*(n+1)+t.combine*n) := by
  induction n with
  | zero => simp [scanM,scan]
  | succ n ih => simp only [scanM,scan,ih]; congr 1; ring

/-- Ordered export uses one indexed read and output constructor per element. -/
def exportM (t : Tariff) : (n : Nat) → (Fin n → Bool) → Measured (List Bool) Nat
  | 0,_ => ([],t.visit)
  | n+1,f => let r := exportM t n (fun i => f i.succ)
             (f 0 :: r.1,t.visit+t.emit+r.2)

theorem exportM_exact (t : Tariff) (n : Nat) (f : Fin n → Bool) :
    exportM t n f = (List.ofFn f,t.visit*(n+1)+t.emit*n) := by
  induction n with
  | zero => simp [exportM]
  | succ n ih => rw [exportM,ih,List.ofFn_succ]; congr 1; ring

/-- Independent length-dependent primitive tariff; successful append has an
indexed write and counter/control update, not linked-list traversal. -/
def charge (cached : Bool) (t : Tariff) (N : Nat) : Command → Nat → Nat
  | .append _,n => t.control + if n < N then
      t.slotWrite+t.control+(if cached then t.combine+t.cacheWrite else 0) else 0
  | .query,n => if cached then t.cacheRead else t.visit*(n+1)+t.combine*n
  | .observe,n => t.visit*(n+1)+t.emit*n

def plainM (t : Tariff) : Command → Buffer N → Measured (Buffer N × Reply) Nat
  | .append x,b => (plainStep (.append x) b,charge false t N (.append x) b.size.val)
  | .query,b => let r := scanM t b.size.val b.read; ((b,.summary r.1),r.2)
  | .observe,b => let r := exportM t b.size.val b.read; ((b,.sequence r.1),r.2)

def cachedM (t : Tariff) : Command → Cached N → Measured (Cached N × Reply) Nat
  | .append x,c => (cachedStep (.append x) c,charge true t N (.append x) c.1.size.val)
  | .query,c => ((c,.summary c.2),t.cacheRead)
  | .observe,c => let r := exportM t c.1.size.val c.1.read; ((c,.sequence r.1),r.2)

theorem plainM_exact (t : Tariff) (cmd : Command) (b : Buffer N) :
    plainM t cmd b = (plainStep cmd b,charge false t N cmd b.decode.length) := by
  cases cmd <;> simp [plainM,plainStep,charge,scanM_exact,exportM_exact,query,decode]

theorem cachedM_exact (t : Tariff) (cmd : Command) (c : Cached N) :
    cachedM t cmd c = (cachedStep cmd c,charge true t N cmd c.1.decode.length) := by
  cases cmd <;> simp [cachedM,cachedStep,charge,exportM_exact,decode]

/-- The accumulated reply list is a ghost trace. Its storage is not charged as
an implementation log; emitted full-sequence values have their own charge. -/
def liftM (step : Command → R → Measured (R × Reply) Nat) (cmd : Command)
    (s : R × List Reply) : Measured (R × List Reply) Nat :=
  let r := step cmd s.1
  ((r.1.1,s.2 ++ [r.1.2]),r.2)

theorem run_erasure (step : Command → R → Measured (R × Reply) Nat)
    (meaning : Command → R → R × Reply)
    (h : ∀ cmd r, (step cmd r).1 = meaning cmd r) (cs : List Command) (r : R) :
    (run (liftM step) cs (r,[])).1 = trace meaning cs r := by
  exact run_value_fusion (liftM step) (advance meaning) id (fun _ => True)
    (fun _ _ _ => trivial) (fun cmd s _ => by simp [liftM,advance,h]) cs (r,[]) trivial

theorem plain_erasure (t : Tariff) (cs : List Command) (b : Buffer N) :
    (run (liftM (plainM t)) cs (b,[])).1 = trace plainStep cs b :=
  run_erasure _ _ (fun cmd b => by rw [plainM_exact]) cs b

theorem cached_erasure (t : Tariff) (cs : List Command) (c : Cached N) :
    (run (liftM (cachedM t)) cs (c,[])).1 = trace cachedStep cs c :=
  run_erasure _ _ (fun cmd c => by rw [cachedM_exact]) cs c

/-- Specification-side exact recurrence, using the actual current abstract history. -/
def budget (cached : Bool) (t : Tariff) (N : Nat) : List Command → List Bool → Nat
  | [],_ => 0
  | cmd::cs,xs => charge cached t N cmd xs.length + budget cached t N cs (spec N cmd xs).1

theorem run_cost (step : Command → R → Measured (R × Reply) Nat)
    (meaning : Command → R → R × Reply) (d : R → List Bool) (P : R → Prop)
    (closed : ∀ cmd r, P r → P (meaning cmd r).1)
    (sim : ∀ cmd r, P r → (d (meaning cmd r).1,(meaning cmd r).2) = spec N cmd (d r))
    (exactStep : ∀ cmd r, step cmd r = (meaning cmd r,charge cached t N cmd (d r).length))
    (cs : List Command) (s : R × List Reply) (hs : P s.1) :
    (run (liftM step) cs s).2 = budget cached t N cs (d s.1) := by
  induction cs generalizing s with
  | nil => rfl
  | cons cmd cs ih =>
    simp only [run_cons,liftM,exactStep,budget]
    rw [ih _ (closed cmd s.1 hs)]
    have h := congrArg Prod.fst (sim cmd s.1 hs)
    change d (meaning cmd s.1).1 = (spec N cmd (d s.1)).1 at h
    simpa only using congrArg (fun xs => charge cached t N cmd (d s.1).length + budget cached t N cs xs) h

theorem plain_cost (t : Tariff) (cs : List Command) (b : Buffer N) :
    (run (liftM (plainM t)) cs (b,[])).2 = budget false t N cs b.decode :=
  run_cost _ plainStep decode (fun _ => True) (fun _ _ _ => trivial)
    (fun cmd b _ => plain_step cmd b) (plainM_exact t) cs (b,[]) trivial

theorem cached_cost (t : Tariff) (cs : List Command) (c : Cached N) (h : Valid c) :
    (run (liftM (cachedM t)) cs (c,[])).2 = budget true t N cs c.1.decode :=
  run_cost _ cachedStep (fun c => c.1.decode) Valid cached_closed cached_step
    (cachedM_exact t) cs (c,[]) h

/-- Segment composition retains the actual intermediate state. -/
theorem sequential (t : Tariff) (xs ys : List Command) (b : Buffer N) :
    run (liftM (plainM t)) (xs++ys) (b,[]) =
      bind (run (liftM (plainM t)) xs (b,[])) (run (liftM (plainM t)) ys) := run_append _ _ _ _

def scale (k : Nat) : Nat →+ Nat where
  toFun n := k*n
  map_zero' := by simp
  map_add' := by simp [Nat.mul_add]

theorem change_units (k : Nat) (t : Tariff) (cs : List Command) (b : Buffer N) :
    reweight (scale k) (run (liftM (plainM t)) cs (b,[])) =
      run (fun cmd s => reweight (scale k) (liftM (plainM t) cmd s)) cs (b,[]) :=
  reweight_run _ _ _ _

/-- Construction initializes every slot and the length; cached construction also
writes its empty parity. These costs are outside the per-command recurrence. -/
def construct (cached : Bool) (t : Tariff) (N : Nat) : Nat :=
  N*t.slotWrite+t.control+(if cached then t.cacheWrite else 0)
def total (cached : Bool) (t : Tariff) (N : Nat) (cs : List Command) : Nat :=
  construct cached t N + budget cached t N cs []

def plainProgram (t : Tariff) (N : Nat) (cs : List Command) :=
  bind (empty N,construct false t N)
    (fun b => run (liftM (plainM t)) cs (b,[]))
def cachedProgram (t : Tariff) (N : Nat) (cs : List Command) :=
  bind ((empty N,(1 : Parity)),construct true t N)
    (fun c => run (liftM (cachedM t)) cs (c,[]))

theorem plainProgram_cost (t : Tariff) (N : Nat) (cs : List Command) :
    (plainProgram t N cs).2 = total false t N cs := by
  simp only [plainProgram,bind,plain_cost,decode_empty,total]

theorem cachedProgram_cost (t : Tariff) (N : Nat) (cs : List Command) :
    (cachedProgram t N cs).2 = total true t N cs := by
  have h : Valid (empty N,(1 : Parity)) := ⟨trivial,rfl⟩
  simp only [cachedProgram,bind,cached_cost t cs _ h,decode_empty,total]

/-- Copy all capacity slots before cache conversion; no unproved sharing assumption. -/
def clone (b : Buffer N) : Buffer N :=
  ⟨Vector.ofFn (Dijkstra.Store.lookup b.slots),b.size⟩

theorem clone_eq (b : Buffer N) : clone b = b := by
  have h : Vector.ofFn (Dijkstra.Store.lookup b.slots) = b.slots := by
    apply Vector.ext
    intro i hi
    simp [Dijkstra.Store.lookup]
  cases b
  simpa [clone] using h

def convert (t : Tariff) (b : Buffer N) : Measured (Cached N) Nat :=
  let copied := clone b
  let r := scanM t copied.size.val copied.read
  ((copied,r.1),N*(t.visit+t.slotWrite)+r.2+t.cacheWrite)

theorem convert_exact (t : Tariff) (b : Buffer N) :
    convert t b = (cache b,N*(t.visit+t.slotWrite)+
      t.visit*(b.size.val+1)+t.combine*b.size.val+t.cacheWrite) := by
  unfold convert
  rw [clone_eq]
  dsimp only
  rw [scanM_exact]
  simp [cache,query,Nat.add_assoc]

theorem convert_valid (t : Tariff) (b : Buffer N) : Valid (convert t b).1 := by
  rw [convert_exact]; exact cache_valid b

/-- Fixed storage units in the declared target: N Boolean slots, one bounded
counter, plus an optional Boolean cache. Output trace is external. -/
def retained (cached : Bool) (N : Nat) : Nat := N+1+(if cached then 1 else 0)
def conversionPeak (N : Nat) : Nat := retained false N + retained true N

theorem peak_covers (N : Nat) : retained false N ≤ conversionPeak N ∧
    retained true N ≤ conversionPeak N := by simp [conversionPeak]

/-- Stack-frame counts are separate from fixed buffer cells. This is an
explicit recursive-scanner model, not a claim about compiler stack frames. -/
def scanFrames (n : Nat) := n+1
def operationPeak (cached : Bool) (N n : Nat) := retained cached N + scanFrames n + n
def conversionWorkingPeak (N : Nat) := conversionPeak N + scanFrames N

theorem operation_peak_bound (cached : Bool) (b : Buffer N) :
    operationPeak cached N b.size.val ≤ retained cached N + (N+1) + N := by
  have := b.size.isLt
  simp only [operationPeak,scanFrames]
  omega

inductive Candidate where | plain | cached | stateless
  deriving DecidableEq, Repr
/-- Restrict to the two proved realizations; a state-free full-history service is unavailable. -/
def eligible : Set Candidate := {c | c ≠ .stateless}
/-- Restrict the no-rejection workload comparison to capacity-admitted words. -/
def admittedCandidates (N : Nat) (cs : List Command) : Set Candidate :=
  {c | c ∈ eligible ∧ Admitted N cs}

theorem admitted_candidates {N : Nat} {cs : List Command} (h : Admitted N cs) :
    admittedCandidates N cs = eligible := by
  ext c
  simp [admittedCandidates,h]

def candidateCost (t : Tariff) (N : Nat) (cs : List Command) : Candidate → Nat
  | .plain => total false t N cs
  | .cached => total true t N cs
  | .stateless => 0

theorem unavailable (t : Tariff) (N : Nat) (cs : List Command) :
    Candidate.stateless ∉ Optimization.minimizers eligible (candidateCost t N cs) := by
  intro h; exact h.1 rfl

end Resources.BoundedSummary
