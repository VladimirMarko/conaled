import Applications.Resources.BoundedSummary

/-! Finite byte-slot machine, with explicit environmental refusals (#253).
The finite types describe a machine contract, not Lean's physical representation. -/
namespace Sequences.ByteBuffer
open BoundedSummary

abbrev Byte := Fin 256
def encode (b : Bool) : Byte := if b then 1 else 0
def bit (b : Byte) : Bool := b != 0
@[simp] theorem bit_encode (b : Bool) : bit (encode b) = b := by cases b <;> decide

/-- Capacity and counter both fit the selected finite word range `0..W`.
All slots are bytes; the representation relation separately requires Boolean bytes. -/
structure Machine (W N : Nat) where
  fits : N ≤ W
  slots : Vector Byte N
  size : Fin (N+1)
  parity : Parity
  deriving DecidableEq

def Machine.buffer (m : Machine W N) : Buffer N := ⟨m.slots.map bit,m.size⟩
def Machine.decode (m : Machine W N) : List Bool := m.buffer.decode
@[simp] theorem decode_length (m : Machine W N) : m.decode.length = m.size.val :=
  BoundedSummary.decode_length m.buffer

def Machine.counter (m : Machine W N) : Fin (W+1) :=
  ⟨m.size.val, by have := m.size.isLt; have := m.fits; omega⟩
def BytesValid (m : Machine W N) : Prop := ∀ i : Fin N, m.slots[i.val] = encode (bit m.slots[i.val])
def Valid (cached : Bool) (m : Machine W N) : Prop :=
  BytesValid m ∧ (cached = true → m.parity = parity m.decode)

def empty (fits : N ≤ W) : Machine W N :=
  ⟨fits,Vector.replicate N 0,⟨0,by omega⟩,1⟩
@[simp] theorem empty_decode (fits : N ≤ W) : (empty fits).decode = [] := rfl

theorem empty_valid (cached : Bool) (fits : N ≤ W) : Valid cached (empty fits) := by
  constructor
  · intro i; simp [empty,encode,bit]
  · intro _; rfl

/-- One indexed write followed by guarded, non-wrapping counter increment. -/
def push (cached : Bool) (m : Machine W N) (x : Bool) (room : m.size.val < N) : Machine W N :=
  { m with slots := m.slots.set m.size.val (encode x)
           size := ⟨m.size.val+1,by omega⟩
           parity := if cached then m.parity * measure x else m.parity }

theorem buffer_push (cached : Bool) (m : Machine W N) (x : Bool) (h : m.size.val < N) :
    (push cached m x h).buffer = BoundedSummary.push m.buffer x h := by
  have hs : (m.slots.set m.size.val (encode x)).map bit =
      Dijkstra.Store.write (m.slots.map bit) ⟨m.size.val,h⟩ x := by
    apply Vector.ext
    intro i hi
    simp [Dijkstra.Store.write,Vector.getElem_set]
  exact congrArg (fun slots => Buffer.mk slots ⟨m.size.val+1,by omega⟩) hs

theorem decode_push (cached : Bool) (m : Machine W N) (x : Bool) (h : m.size.val < N) :
    (push cached m x h).decode = m.decode ++ [x] := by
  exact (congrArg Buffer.decode (buffer_push cached m x h)).trans (BoundedSummary.decode_push _ _ _)

theorem push_valid (cached : Bool) (m : Machine W N) (x : Bool)
    (h : m.size.val < N) (v : Valid cached m) : Valid cached (push cached m x h) := by
  constructor
  · intro i
    simp only [push,Vector.getElem_set]
    split
    · simp
    · exact v.1 i
  · intro hc
    subst cached
    change m.parity * measure x = parity (push true m x h).decode
    rw [decode_push]
    exact (congrArg (fun p => p * measure x) (v.2 rfl)).trans
      (by simp [parity,OrderedSummary.summary_append,OrderedSummary.summary_singleton])

/-- Accumulator loop over finite indexed reads. Recursive notation specifies
iteration; it does not assert tail-call optimization by any compiler. -/
def scanAcc : (n : Nat) → (Fin n → Bool) → Parity → Parity
  | 0,_,acc => acc
  | n+1,f,acc => scanAcc n (fun i => f i.succ) (acc * measure (f 0))

theorem scanAcc_correct (n : Nat) (f : Fin n → Bool) (acc : Parity) :
    scanAcc n f acc = acc * scan n f := by
  induction n generalizing acc with
  | zero => simp [scanAcc,scan]
  | succ n ih => simp only [scanAcc,scan,ih,mul_assoc]

def queryLoop (m : Machine W N) : Parity := scanAcc m.size.val m.buffer.read 1
@[simp] theorem queryLoop_correct (m : Machine W N) : queryLoop m = parity m.decode := by
  simp [queryLoop,scanAcc_correct,Machine.decode,← query_correct,query,Machine.buffer]

def step (cached : Bool) : Command → Machine W N → Machine W N × Reply
  | .append x,m => if h : m.size.val < N then (push cached m x h,.appended true)
                  else (m,.appended false)
  | .query,m => (m,.summary (if cached then m.parity else queryLoop m))
  | .observe,m => (m,.sequence m.decode)

theorem step_simulation (cached : Bool) (cmd : Command) (m : Machine W N)
    (v : Valid cached m) :
    ((step cached cmd m).1.decode,(step cached cmd m).2) = spec N cmd m.decode := by
  cases cmd with
  | append x =>
    simp only [step,spec,decode_length]
    split <;> simp [decode_push]
  | query => cases cached <;> simp [step,spec,Machine.decode,v.2]
  | observe => rfl

theorem step_valid (cached : Bool) (cmd : Command) (m : Machine W N)
    (v : Valid cached m) : Valid cached (step cached cmd m).1 := by
  cases cmd with
  | append x => simp only [step]; split; exact push_valid _ _ _ _ v; exact v
  | query => exact v
  | observe => exact v

/-- Reuse #239's client theorem rather than proving a second trace induction. -/
theorem trace_simulation (cached : Bool) (cs : List Command) (m : Machine W N)
    (v : Valid cached m) :
    ((trace (step cached) cs m).1.decode,(trace (step cached) cs m).2) =
      trace (spec N) cs m.decode :=
  trace_preserves (step cached) Machine.decode (Valid cached)
    (step_valid cached) (step_simulation cached) cs m v

theorem overflow_preserves (cached : Bool) (m : Machine W N) (x : Bool)
    (full : m.size.val = N) : step cached (.append x) m = (m,.appended false) := by
  simp [step,full]

theorem increment_no_wrap (cached : Bool) (m : Machine W N) (x : Bool)
    (room : m.size.val < N) :
    (push cached m x room).counter.val = m.counter.val + 1 ∧ m.counter.val + 1 ≤ W := by
  have := m.fits
  exact ⟨rfl,by dsimp [Machine.counter]; omega⟩

/-- Copy all slots into a separately owned destination in the operational contract.
Extensional equality alone does not imply physical separation; the event model
and adapter impose that ownership obligation. -/
def convert (m : Machine W N) : Machine W N :=
  { m with slots := Vector.ofFn (fun i => m.slots[i.val])
           parity := queryLoop m }

theorem convert_buffer (m : Machine W N) : (convert m).buffer = m.buffer := by
  have h : Vector.ofFn (fun i : Fin N => m.slots[i.val]) = m.slots := by
    apply Vector.ext; intro i hi; simp
  simp [convert,Machine.buffer,h]

theorem convert_decode (m : Machine W N) : (convert m).decode = m.decode :=
  congrArg Buffer.decode (convert_buffer m)

theorem convert_valid (m : Machine W N) (v : BytesValid m) : Valid true (convert m) := by
  constructor
  · intro i; simpa [convert] using v i
  · intro _; change queryLoop m = parity (convert m).decode
    rw [convert_decode]; exact queryLoop_correct _

/-- Allocation failures concern construction/copy; output refusal concerns a
snapshot request. Neither is a capacity-overflow reply. -/
inductive Failure where | allocation | output
  deriving DecidableEq, Repr
abbrev Outcome := Except Failure Reply

def construct (fits : N ≤ W) (available : Bool) : Except Failure (Machine W N) :=
  if available then .ok (empty fits) else .error .allocation

def copy (m : Machine W N) (available : Bool) : Machine W N × Except Failure (Machine W N) :=
  (m,if available then .ok (convert m) else .error .allocation)

/-- Fallible preparation precedes mutation. Snapshot allocation is separately
reported; no interruption or failure during the commit primitive is modeled. -/
def attempt (cached : Bool) (allocationAvailable outputAvailable : Bool) (cmd : Command) (m : Machine W N) :
    Machine W N × Outcome :=
  if allocationAvailable = false then (m,.error .allocation)
  else if cmd = .observe ∧ outputAvailable = false then (m,.error .output)
  else let s := step cached cmd m; (s.1,.ok s.2)

def specAttempt (N : Nat) (allocationAvailable outputAvailable : Bool) (cmd : Command) (xs : List Bool) :
    List Bool × Outcome :=
  if allocationAvailable = false then (xs,.error .allocation)
  else if cmd = .observe ∧ outputAvailable = false then (xs,.error .output)
  else let s := spec N cmd xs; (s.1,.ok s.2)

theorem attempt_simulation (cached allocationAvailable outputAvailable : Bool) (cmd : Command) (m : Machine W N)
    (v : Valid cached m) :
    ((attempt cached allocationAvailable outputAvailable cmd m).1.decode,(attempt cached allocationAvailable outputAvailable cmd m).2) =
      specAttempt N allocationAvailable outputAvailable cmd m.decode := by
  unfold attempt specAttempt
  split
  · rfl
  · split
    · rfl
    · exact congrArg (fun s : List Bool × Reply => (s.1,Except.ok s.2)) (step_simulation _ _ _ v)

theorem output_failure_preserves (cached : Bool) (m : Machine W N) :
    attempt cached true false .observe m = (m,.error .output) := by simp [attempt]

theorem successful_specialization (cached : Bool) (cmd : Command) (m : Machine W N) :
    attempt cached true true cmd m = ((step cached cmd m).1,.ok (step cached cmd m).2) := by
  simp [attempt]

theorem copy_failure_preserves (m : Machine W N) :
    copy m false = (m,.error .allocation) := rfl

theorem allocation_failure_preserves (cached outputAvailable : Bool) (cmd : Command)
    (m : Machine W N) : attempt cached false outputAvailable cmd m = (m,.error .allocation) := rfl

/-- Ghost observations; the implementation does not retain a reply log. -/
def attemptTrace (cached : Bool) (requests : List (Bool × Bool × Command)) (m : Machine W N) :=
  requests.foldl (fun s request =>
    let t := attempt cached request.1 request.2.1 request.2.2 s.1
    (t.1,s.2 ++ [t.2])) (m,([] : List Outcome))

theorem attempt_valid (cached allocationAvailable outputAvailable : Bool) (cmd : Command)
    (m : Machine W N) (v : Valid cached m) :
    Valid cached (attempt cached allocationAvailable outputAvailable cmd m).1 := by
  unfold attempt
  split
  · exact v
  · split
    · exact v
    · exact step_valid _ _ _ v

def specAttemptTrace (N : Nat) (requests : List (Bool × Bool × Command)) (xs : List Bool) :=
  requests.foldl (fun s request =>
    let t := specAttempt N request.1 request.2.1 request.2.2 s.1
    (t.1,s.2 ++ [t.2])) (xs,([] : List Outcome))

theorem attempt_trace_simulation (cached : Bool) (requests : List (Bool × Bool × Command))
    (m : Machine W N) (v : Valid cached m) :
    ((attemptTrace cached requests m).1.decode,(attemptTrace cached requests m).2) =
      specAttemptTrace N requests m.decode := by
  apply SquareKit.ListFusion.foldl_reachable
    (fun s (request : Bool × Bool × Command) => let t := attempt cached request.1 request.2.1 request.2.2 s.1
      (t.1,s.2 ++ [t.2]))
    (fun s (request : Bool × Bool × Command) => let t := specAttempt N request.1 request.2.1 request.2.2 s.1
      (t.1,s.2 ++ [t.2]))
    (fun s => (s.1.decode,s.2)) (fun s => Valid cached s.1) (m,[]) v
  · intro s request hs; exact attempt_valid _ _ _ _ _ hs
  · intro s request hs
    have h := attempt_simulation cached request.1 request.2.1 request.2.2 s.1 hs
    exact congrArg (fun t : List Bool × Outcome => (t.1,s.2 ++ [t.2])) h

theorem successful_trace (cached : Bool) (cs : List Command) (m : Machine W N) :
    attemptTrace cached (cs.map (fun c => (true,true,c))) m =
      ((trace (step cached) cs m).1,(trace (step cached) cs m).2.map Except.ok) := by
  unfold attemptTrace
  rw [List.foldl_map]
  symm
  apply SquareKit.ListFusion.foldl_reachable
    (fun s c => advance (step cached) c s)
    (fun s c => let t := attempt cached true true c s.1; (t.1,s.2 ++ [t.2]))
    (fun s => (s.1,s.2.map Except.ok)) (fun _ => True) (m,[]) trivial
  · intros; trivial
  · intro s c _
    simp [advance,successful_specialization]

end Sequences.ByteBuffer
