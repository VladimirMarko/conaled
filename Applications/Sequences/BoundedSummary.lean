import Applications.Sequences.OrderedSummary
import Applications.Dijkstra.Store
import Applications.Resources.Workload
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-! Fixed-capacity ordered Boolean buffers (#239). Indexed reads/writes and a
bounded counter describe the target model; no allocator or machine-code claim. -/
namespace Sequences.BoundedSummary
open OrderedSummary

/-- XOR as an ordinary monoid, separate from length. -/
structure Parity where
  value : Bool
  deriving DecidableEq, Repr
instance : Monoid Parity where
  one := ⟨false⟩
  mul x y := ⟨x.value ^^ y.value⟩
  one_mul x := by cases x with | mk x => cases x <;> rfl
  mul_one x := by cases x with | mk x => cases x <;> rfl
  mul_assoc x y z := by
    cases x with | mk x => cases y with | mk y => cases z with | mk z =>
    cases x <;> cases y <;> cases z <;> rfl

def measure (b : Bool) : Parity := ⟨b⟩
def parity (xs : List Bool) : Parity := summary measure xs

/-- All slots are initialized; only the prefix selected by the bounded counter is public. -/
structure Buffer (N : Nat) where
  slots : Dijkstra.Store.Store N Bool
  size : Fin (N+1)
  deriving DecidableEq

def Buffer.read (b : Buffer N) (i : Fin b.size.val) : Bool :=
  Dijkstra.Store.lookup b.slots ⟨i.val, by have := i.isLt; have := b.size.isLt; omega⟩
def Buffer.decode (b : Buffer N) : List Bool := List.ofFn b.read

open Buffer

@[simp] theorem decode_length (b : Buffer N) : b.decode.length = b.size.val := List.length_ofFn

theorem capacity (b : Buffer N) : b.decode.length ≤ N := by
  rw [decode_length]; have := b.size.isLt; omega

def empty (N : Nat) : Buffer N := ⟨Vector.replicate N false, ⟨0, by omega⟩⟩
@[simp] theorem decode_empty : (empty N).decode = [] := rfl

def push (b : Buffer N) (x : Bool) (h : b.size.val < N) : Buffer N :=
  ⟨Dijkstra.Store.write b.slots ⟨b.size.val,h⟩ x, ⟨b.size.val+1, by omega⟩⟩

theorem decode_push (b : Buffer N) (x : Bool) (h : b.size.val < N) :
    (push b x h).decode = b.decode ++ [x] := by
  unfold decode
  change List.ofFn (fun i : Fin (b.size.val+1) => (push b x h).read i) = _
  rw [List.ofFn_succ_last]
  congr 1
  · apply congrArg List.ofFn
    funext i
    simp only [Buffer.read, push, Dijkstra.Store.lookup_write]
    split
    · rename_i he
      have := congrArg Fin.val he
      have := i.isLt
      simp only [Fin.val_castSucc] at *
      omega
    · rfl
  · simp [Buffer.read, push, Dijkstra.Store.lookup_write]

/-- Total overflow returns false and leaves the buffer unchanged. -/
def tryPush (b : Buffer N) (x : Bool) : Buffer N × Bool :=
  if h : b.size.val < N then (push b x h,true) else (b,false)

theorem overflow (b : Buffer N) (x : Bool) (h : b.size.val = N) : tryPush b x = (b,false) := by
  simp [tryPush,h]

/-- Scan finite indexed positions directly, without constructing a history list. -/
def scan : (n : Nat) → (Fin n → Bool) → Parity
  | 0, _ => 1
  | n+1, f => measure (f 0) * scan n (fun i => f i.succ)

theorem scan_summary (n : Nat) (f : Fin n → Bool) : scan n f = parity (List.ofFn f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ]
    change measure (f 0) * scan n _ = summary measure ([f 0] ++ _)
    rw [summary_append, summary_singleton, ih]
    rfl

def query (b : Buffer N) : Parity := scan b.size.val b.read
@[simp] theorem query_correct (b : Buffer N) : query b = parity b.decode := scan_summary _ _

abbrev Cached (N : Nat) := Buffer N × Parity
def Valid (c : Cached N) : Prop := OrderedSummary.Valid (fun _ => True) decode measure c

def cache (b : Buffer N) : Cached N := (b,query b)
theorem cache_valid (b : Buffer N) : Valid (cache b) := ⟨trivial,query_correct b⟩

def cachedPush (c : Cached N) (x : Bool) : Cached N × Bool :=
  if h : c.1.size.val < N then ((push c.1 x h,c.2 * measure x),true) else (c,false)

theorem cachedPush_valid {c : Cached N} (h : Valid c) (x : Bool) :
    Valid (cachedPush c x).1 := by
  unfold cachedPush
  split
  · rename_i room
    refine ⟨trivial, ?_⟩
    change c.2 * measure x = summary measure (decode (push c.1 x room))
    rw [decode_push, summary_append, summary_singleton, h.2]
  · exact h

inductive Command where
  | append (value : Bool) | query | observe
  deriving DecidableEq, Repr
inductive Reply where
  | appended (accepted : Bool) | summary (value : Parity) | sequence (xs : List Bool)
  deriving DecidableEq, Repr

/-- Independent observable contract, including overflow. -/
def spec (N : Nat) : Command → List Bool → List Bool × Reply
  | .append x, xs => if xs.length < N then (xs ++ [x],.appended true) else (xs,.appended false)
  | .query, xs => (xs,.summary (parity xs))
  | .observe, xs => (xs,.sequence xs)

def plainStep : Command → Buffer N → Buffer N × Reply
  | .append x, b => let t := tryPush b x; (t.1,.appended t.2)
  | .query, b => (b,.summary (query b))
  | .observe, b => (b,.sequence b.decode)

def cachedStep : Command → Cached N → Cached N × Reply
  | .append x, c => let t := cachedPush c x; (t.1,.appended t.2)
  | .query, c => (c,.summary c.2)
  | .observe, c => (c,.sequence c.1.decode)

theorem plain_step (cmd : Command) (b : Buffer N) :
    ((plainStep cmd b).1.decode,(plainStep cmd b).2) = spec N cmd b.decode := by
  cases cmd with
  | append x => simp only [plainStep,tryPush,spec,decode_length]; split <;> simp [decode_push]
  | query => simp [plainStep,spec]
  | observe => rfl

theorem cached_step (cmd : Command) (c : Cached N) (h : Valid c) :
    ((cachedStep cmd c).1.1.decode,(cachedStep cmd c).2) = spec N cmd c.1.decode := by
  cases cmd with
  | append x => simp only [cachedStep,cachedPush,spec,decode_length]; split <;> simp [decode_push]
  | query => exact Prod.ext rfl (congrArg Reply.summary h.2)
  | observe => rfl

theorem cached_closed (cmd : Command) (c : Cached N) (h : Valid c) :
    Valid (cachedStep cmd c).1 := by
  cases cmd with
  | append x => exact cachedPush_valid h x
  | query => exact h
  | observe => exact h

/-- Accumulate actual public replies in order. The log is an observation,
not a bounded implementation field or a free storage promise. -/
def advance (step : Command → R → R × Reply) (cmd : Command)
    (s : R × List Reply) : R × List Reply :=
  let t := step cmd s.1
  (t.1,s.2 ++ [t.2])
def trace (step : Command → R → R × Reply) (cmds : List Command) (r : R) :=
  cmds.foldl (fun s c => advance step c s) (r,[])

/-- One reachable-fusion theorem serves both concrete operations. -/
theorem trace_preserves (step : Command → R → R × Reply) (decodeR : R → List Bool)
    (P : R → Prop) (closed : ∀ cmd r, P r → P (step cmd r).1)
    (law : ∀ cmd r, P r → (decodeR (step cmd r).1,(step cmd r).2) = spec N cmd (decodeR r))
    (cmds : List Command) (r : R) (h : P r) :
    (decodeR (trace step cmds r).1,(trace step cmds r).2) = trace (spec N) cmds (decodeR r) := by
  apply SquareKit.ListFusion.foldl_reachable
    (fun s c => advance step c s) (fun s c => advance (spec N) c s)
    (fun s => (decodeR s.1,s.2)) (fun s => P s.1) (r,[]) h
  · intro s c hs; exact closed c s.1 hs
  · intro s c hs
    have hl := law c s.1 hs
    unfold advance
    rw [← hl]

/-- The local plain simulation is also an ordinary relational square. -/
def stepSquare (cmd : Command) : Relational.RelSquare
    ⟨Buffer N,List Bool,fun b xs => b.decode = xs⟩
    ⟨Buffer N × Reply,List Bool × Reply,fun b xs => (b.1.decode,b.2) = xs⟩ where
  impl := plainStep cmd
  spec := spec N cmd
  preserves h := by rw [← h]; exact plain_step cmd _

theorem plain_trace (cmds : List Command) (b : Buffer N) :
    ((trace plainStep cmds b).1.decode,(trace plainStep cmds b).2) = trace (spec N) cmds b.decode :=
  trace_preserves plainStep decode (fun _ => True) (fun _ _ _ => trivial)
    (fun cmd b _ => (stepSquare cmd).preserves (show b.decode = b.decode from rfl)) cmds b trivial

theorem cached_trace (cmds : List Command) (c : Cached N) (h : Valid c) :
    ((trace cachedStep cmds c).1.1.decode,(trace cachedStep cmds c).2) = trace (spec N) cmds c.1.decode :=
  trace_preserves cachedStep (fun c => c.1.decode) Valid cached_closed cached_step cmds c h

/-- Initial caches and plain buffers produce exactly the same replies and history. -/
theorem traces_equal (cmds : List Command) (b : Buffer N) :
    ((trace plainStep cmds b).1.decode,(trace plainStep cmds b).2) =
      ((trace cachedStep cmds (cache b)).1.1.decode,(trace cachedStep cmds (cache b)).2) :=
  (plain_trace cmds b).trans (cached_trace cmds (cache b) (cache_valid b)).symm

def batch (xs : List Bool) := xs.map Command.append ++ [.query]
def everyPrefix (xs : List Bool) : List Command := xs.flatMap (fun x => [.append x,.query])

/-- Count requested appends independently of implementation replies. -/
def appends (cs : List Command) : Nat :=
  (cs.filter (fun c => match c with | .append _ => true | _ => false)).length

def Admitted (N : Nat) (cs : List Command) : Prop := appends cs ≤ N

/-- The total bound implies the same bound at every prefix. -/
theorem admitted_prefix {N : Nat} {xs ys : List Command} (h : Admitted N (xs++ys)) :
    Admitted N xs := by
  unfold Admitted appends at *
  simp only [List.filter_append,List.length_append] at h
  omega

/-- Every requested append has room along the independent history transition. -/
def Within (N : Nat) : List Command → List Bool → Prop
  | [],_ => True
  | .append x::cs,xs => xs.length < N ∧ Within N cs (xs++[x])
  | .query::cs,xs => Within N cs xs
  | .observe::cs,xs => Within N cs xs

theorem within_of_bound (cs : List Command) (xs : List Bool)
    (h : xs.length + appends cs ≤ N) : Within N cs xs := by
  induction cs generalizing xs with
  | nil => trivial
  | cons cmd cs ih =>
    cases cmd with
    | append x =>
      have count : appends (.append x::cs) = appends cs + 1 := by simp [appends]
      rw [count] at h
      exact ⟨by omega, ih (xs++[x]) (by simp only [List.length_append,List.length_singleton]; omega)⟩
    | query => apply ih xs; simpa [appends] using h
    | observe => apply ih xs; simpa [appends] using h

theorem admitted_within {cs : List Command} (h : Admitted N cs) : Within N cs [] :=
  within_of_bound cs [] (by simpa [Admitted] using h)

/-- Each ordinary accepted append has precisely the requested singleton meaning. -/
theorem accepted_append (xs : List Bool) (x : Bool) (h : xs.length < N) :
    spec N (.append x) xs = (xs++[x],.appended true) := by simp [spec,h]

/-- Cache validity survives arbitrary traces, including rejected overflow commands. -/
theorem cached_trace_valid (cs : List Command) (c : Cached N) (h : Valid c) :
    Valid (trace cachedStep cs c).1 := by
  have general : ∀ (cs : List Command) (s : Cached N × List Reply), Valid s.1 →
      Valid (cs.foldl (fun s cmd => advance cachedStep cmd s) s).1 := by
    intro cs
    induction cs with
    | nil => intro s hs; exact hs
    | cons cmd cs ih =>
      intro s hs
      exact ih (advance cachedStep cmd s) (cached_closed cmd s.1 hs)
  exact general cs (c,[]) h

/-- Prefix lengths factor through final length; elements cannot be recovered this way. -/
theorem prefix_elimination (b : Buffer N) :
    b.decode.inits.map List.length = List.range (b.size.val+1) := by
  rw [Symmetric.lengths_inits,decode_length]

theorem stateless_impossible : ¬ ∃ answer : Unit → List Bool,
    answer () = [false] ∧ answer () = [true] := by
  rintro ⟨answer,hf,ht⟩
  have h := hf.symm.trans ht
  cases h

/-- A deterministic executor with no retained state replies from the current
command alone. The two capacity-one histories require different final replies. -/
def statelessReplies (reply : Command → Reply) (cs : List Command) := cs.map reply

theorem no_stateless_trace : ¬ ∃ reply : Command → Reply,
    ∀ cs, Admitted 1 cs → statelessReplies reply cs = (trace (spec 1) cs []).2 := by
  rintro ⟨reply,h⟩
  have hf := congrArg (fun rs : List Reply => rs[1]?)
    (h [.append false,.observe] (by change appends _ ≤ 1; decide))
  have ht := congrArg (fun rs : List Reply => rs[1]?)
    (h [.append true,.observe] (by change appends _ ≤ 1; decide))
  change some (reply .observe) = some (.sequence [false]) at hf
  change some (reply .observe) = some (.sequence [true]) at ht
  have bad := (Option.some.inj hf).symm.trans (Option.some.inj ht)
  cases bad

end Sequences.BoundedSummary
