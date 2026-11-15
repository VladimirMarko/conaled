import Applications.Languages.DerivativeNormalization
import Applications.Languages.RetainedSnapshot
import Applications.Resources.Measured

/-! Four native policies and an executable, explicit-map cost realization.
The cost fragment is transport spines over a list-valued universal parser.
It is deliberately narrower than the exact semantic policy theorem. -/
namespace LanguageWitnesses.ParserWorkload
open RetainedSnapshot

inductive Policy where
  | ordinary | retained | normalized | combined
  deriving DecidableEq, Repr

def Policy.normalizes : Policy → Bool
  | .normalized | .combined => true
  | _ => false

def Policy.retains : Policy → Bool
  | .retained | .combined => true
  | _ => false

def prepare {P : Language Bool} (policy : Policy) (p : Parser P) : Parser P :=
  if policy.normalizes then DerivativeNormalization.normalize p else p

/-- Setup occurs once. The returned function owns the prepared parser or tree. -/
def session {P : Language Bool} (policy : Policy) (p : Parser P) (depth : Nat) :
    (q : Request) → Option (Decision (P q.2)) :=
  let p' := prepare policy p
  if policy.retains then
    let tree := (build p' depth).1
    fun q => query tree q.1 q.2
  else fun q => if admissible depth q then some (p'.parse q.2) else none

theorem prepare_exact {P : Language Bool} (policy) (p : Parser P) (w) :
    (prepare policy p).parse w = p.parse w := by
  unfold prepare
  split
  · exact DerivativeNormalization.normalize_exact _ _
  · rfl

theorem session_exact {P : Language Bool} (policy) (p : Parser P) (depth) (q) :
    session policy p depth q =
      if admissible depth q then some (p.parse q.2) else none := by
  unfold session
  split
  · dsimp only
    rw [query_build, prepare_exact]; rfl
  · dsimp only
    rw [prepare_exact]

abbrev Payload : Type := List Bool × PUnit
abbrev L : Language Bool := fun _ => Payload

/-- Explicit closure syntax. Shift retains its prefix symbol and child closure. -/
inductive Map where
  | identity | flip
  | compose : Map → Map → Map
  | shift : Bool → Map → Map
  deriving Repr, DecidableEq

def flipIso : Iso Payload Payload where
  forward x := (x.1.map Bool.not, x.2)
  backward x := (x.1.map Bool.not, x.2)
  backward_forward := by intro x; simp [Function.comp_def]
  forward_backward := by intro x; simp [Function.comp_def]

def Map.iso : Map → List Bool → Iso Payload Payload
  | .identity, _ => Iso.refl _
  | .flip, _ => flipIso
  | .compose f g, w => (f.iso w).trans (g.iso w)
  | .shift b f, w => f.iso (b :: w)

inductive Spine where
  | base : List Bool → Spine
  | transport : Map → Spine → Spine
  deriving Repr, DecidableEq

def Spine.native : Spine → Parser L
  | .base xs => .scale (.yes xs) .universal
  | .transport f p => .transport f.iso p.native

def Spine.derive (p : Spine) (b : Bool) : Spine := match p with
  | .base xs => .base xs
  | .transport f p => .transport (.shift b f) (p.derive b)

theorem Spine.derive_native (p : Spine) (b) :
    (p.derive b).native = p.native.derive b := by
  induction p with
  | base => rfl
  | transport f p ih => simp only [Spine.derive, Spine.native, Parser.derive, ih]; rfl

def Spine.pack : Spine → Spine × Map
  | .base xs => (.base xs, .identity)
  | .transport f p => let r := p.pack; (r.1, .compose r.2 f)

def Spine.normalize (p : Spine) : Spine :=
  let r := p.pack; .transport r.2 r.1

theorem Spine.pack_native (p : Spine) :
    DerivativeNormalization.pack p.native =
      ⟨L, p.pack.1.native, p.pack.2.iso⟩ := by
  induction p with
  | base => rfl
  | transport f p ih =>
    change (let s := DerivativeNormalization.pack p.native;
      (⟨s.source, s.base, fun w => (s.witness w).trans (f.iso w)⟩ : DerivativeNormalization.Packed L)) = _
    rw [ih]
    rfl

theorem Spine.normalize_native (p : Spine) :
    p.normalize.native = DerivativeNormalization.normalize p.native := by
  unfold Spine.normalize DerivativeNormalization.normalize
  rw [p.pack_native]
  rfl

/-- Events describe the represented execution, excluding instrumentation overhead. -/
inductive Kind where
  | derivative | nullable | normalization | map | closure | snapshot | validation | traversal | allocation
  deriving DecidableEq, Repr
abbrev Trace := List (Kind × Nat)

def charge (k : Kind) (n : Nat := 1) : Trace := [(k,n)]
def alloc (n : Nat) : Trace := charge .allocation n
def Trace.count (t : Trace) (k : Kind) : Nat :=
  ((t.filter (fun e => e.1 == k)).map Prod.snd).sum

/-- Map execution visits closure nodes; flip traverses and copies its list.
Shift materializes a prefix cons; composition keeps intermediate lists in arena. -/
def Map.run : Map → List Bool → Payload → Payload × Trace
  | .identity, _, x => (x, charge .map)
  | .flip, _, x => ((x.1.map Bool.not, x.2),
      charge .map (x.1.length + 1) ++ alloc (2 * x.1.length + 1))
  | .compose f g, w, x =>
      let a := f.run w x
      let b := g.run w a.1
      (b.1, charge .map ++ a.2 ++ b.2)
  | .shift b f, w, x =>
      let a := f.run (b :: w) x
      (a.1, charge .map ++ alloc 2 ++ a.2)

theorem Map.run_result (f : Map) (w) (x) :
    (f.run w x).1 = (f.iso w).forward x := by
  induction f generalizing w x with
  | identity | flip => rfl
  | compose f g ih jh => simp [Map.run, Map.iso, Iso.trans, ih, jh]
  | shift b f ih => exact ih _ _

def Spine.deriveRun : Spine → Bool → Spine × Trace
  | .base xs, _ => (.base xs, charge .derivative 2 ++ alloc 3)
  | .transport f p, b =>
      let r := p.deriveRun b
      (.transport (.shift b f) r.1,
        charge .derivative ++ charge .closure ++ alloc 5 ++ r.2)

theorem Spine.deriveRun_result (p : Spine) (b) : (p.deriveRun b).1 = p.derive b := by
  induction p <;> simp_all [Spine.deriveRun, Spine.derive]

def Spine.nullableRun : Spine → Payload × Trace
  | .base xs => ((xs, ⟨⟩), charge .nullable 2 ++ alloc 2)
  | .transport f p =>
      let r := p.nullableRun
      let s := f.run [] r.1
      (s.1, charge .nullable ++ r.2 ++ s.2 ++ alloc 1)

theorem Spine.nullableRun_result (p : Spine) :
    Decision.yes p.nullableRun.1 = p.native.nullable := by
  induction p with
  | base => rfl
  | transport f p ih =>
    simp only [Spine.nullableRun, Spine.native, Parser.nullable]
    rw [← ih, Decision.map, Map.run_result]

def Spine.parseRun (p : Spine) : List Bool → Payload × Trace
  | [] => p.nullableRun
  | b :: w =>
      let d := p.deriveRun b
      let r := d.1.parseRun w
      (r.1, d.2 ++ r.2)

theorem Spine.parseRun_result (p : Spine) (w) :
    Decision.yes (p.parseRun w).1 = p.native.parse w := by
  induction w generalizing p with
  | nil => exact p.nullableRun_result
  | cons b w ih =>
    simp only [Spine.parseRun, Parser.parse]
    rw [ih, Spine.deriveRun_result, Spine.derive_native]
    rfl

def Spine.packRun : Spine → (Spine × Map) × Trace
  | .base xs => ((.base xs, .identity), charge .normalization ++ charge .closure ++ alloc 1)
  | .transport f p =>
      let r := p.packRun
      ((r.1.1, .compose r.1.2 f),
        charge .normalization ++ r.2 ++ charge .closure ++ alloc 3)

theorem Spine.packRun_result (p : Spine) : p.packRun.1 = p.pack := by
  induction p <;> simp_all [Spine.packRun, Spine.pack]

def Spine.normalizeRun (p : Spine) : Spine × Trace :=
  let r := p.packRun
  (.transport r.1.2 r.1.1, r.2 ++ charge .normalization ++ alloc 2)

theorem Spine.normalizeRun_result (p : Spine) : p.normalizeRun.1 = p.normalize := by
  simp [Spine.normalizeRun, Spine.normalize, Spine.packRun_result]

def Spine.buildRun (p : Spine) : (n : Nat) → Tree L n × Trace
  | 0 =>
      let d := p.nullableRun
      (.leaf (.yes d.1), d.2 ++ charge .snapshot ++ alloc 2)
  | n+1 =>
      let d := p.nullableRun
      let dl := p.deriveRun false
      let l := dl.1.buildRun n
      let dr := p.deriveRun true
      let r := dr.1.buildRun n
      (.node (.yes d.1) l.1 r.1,
        d.2 ++ dl.2 ++ l.2 ++ dr.2 ++ r.2 ++ charge .snapshot ++ alloc 4)

theorem Spine.buildRun_result (p : Spine) (n) :
    (p.buildRun n).1 = (build p.native n).1 := by
  induction n generalizing p with
  | zero => simp only [Spine.buildRun, build, Spine.nullableRun_result]
  | succ n ih =>
    simp only [Spine.buildRun, build, Spine.nullableRun_result, ih,
      Spine.deriveRun_result, Spine.derive_native]
    rfl

/-- The validation tariff evaluates both comparisons and traverses the word length.
Naturals/comparisons are unit primitives; this is not bit complexity. -/
def validation (q : Request) : Trace := charge .validation (q.2.length + 2)

def directQuery (p : Spine) (m : Nat) (q : Request) : Option (Decision Payload) × Trace :=
  if admissible m q then
    let r := p.parseRun q.2
    (some (.yes r.1), validation q ++ r.2 ++ alloc 1)
  else (none, validation q ++ alloc 1)

def retainedQuery {m} (t : Tree L m) (q : Request) : Option (Decision Payload) × Trace :=
  if h : admissible m q then
    let r := t.lookupCounted q.2 (Nat.le_trans h.2 h.1)
    (some r.1, validation q ++ charge .traversal r.2 ++ alloc 1)
  else (none, validation q ++ alloc 1)

theorem directQuery_result (p : Spine) (m q) :
    (directQuery p m q).1 = if admissible m q then some (p.native.parse q.2) else none := by
  unfold directQuery
  split <;> simp_all [Spine.parseRun_result]

theorem retainedQuery_result {m} (t : Tree L m) (q) :
    (retainedQuery t q).1 = query t q.1 q.2 := by
  by_cases h : q.1 ≤ m ∧ q.2.length ≤ q.1
  · simp [retainedQuery, query, admissible, h, Tree.lookupCounted_correct]
  · simp [retainedQuery, query, admissible, h]

structure Setup (m : Nat) where
  parser : Spine
  tree : Option (Tree L m)
  events : Trace

def setup (policy : Policy) (p : Spine) (m : Nat) : Setup m :=
  let n := if policy.normalizes then p.normalizeRun else (p, [])
  if policy.retains then
    let b := n.1.buildRun m
    ⟨n.1, some b.1, n.2 ++ b.2⟩
  else ⟨n.1, none, n.2⟩

def Setup.query {m} (s : Setup m) (q : Request) : Option (Decision Payload) × Trace :=
  match s.tree with
  | some t => retainedQuery t q
  | none => directQuery s.parser m q

theorem setup_query_result (policy : Policy) (p : Spine) (m q) :
    ((setup policy p m).query q).1 = session policy p.native m q := by
  cases policy <;>
    simp [setup, Setup.query, Policy.normalizes, Policy.retains, session, prepare,
      retainedQuery_result, directQuery_result, Spine.buildRun_result,
      Spine.normalizeRun_result, Spine.normalize_native]

/-- Slots in the caller-owned source graph. Constructors include captured fields.
Source graphs are trees; new closures reference those existing nodes. -/
def Map.slots : Map → Nat
  | .identity | .flip => 1
  | .compose f g => 3 + f.slots + g.slots
  | .shift _ f => 3 + f.slots

def Spine.slots : Spine → Nat
  | .base xs => 3 + 2 * xs.length + 2
  | .transport f p => 2 + f.slots + p.slots

structure Run where
  /-- Logical transcript of synchronously consumed outputs, not an owned output list. -/
  answers : List (Option (Decision Payload))
  setupEvents : Trace
  queryEvents : List Trace
  initial : Nat

/-- Setup arena lives throughout the batch. Each query arena is released after
its answer has been consumed; the logical transcript does not retain pointers. -/
def execute (policy : Policy) (p : Spine) (m : Nat) (qs : List Request) : Run :=
  let s := setup policy p m
  let rs := qs.map s.query
  ⟨rs.map Prod.fst, s.events, rs.map Prod.snd, p.slots⟩

theorem execute_exact (policy : Policy) (p : Spine) (m qs) :
    (execute policy p m qs).answers =
      qs.map (fun q => if admissible m q then some (p.native.parse q.2) else none) := by
  simp only [execute, List.map_map]
  apply List.map_congr_left
  intro q _
  exact (setup_query_result policy p m q).trans (session_exact policy p.native m q)

def Run.count (r : Run) (k : Kind) : Nat :=
  r.setupEvents.count k + ((r.queryEvents.map (fun t => t.count k)).sum)

def Run.cumulative (r : Run) : Nat := r.count .allocation

def Run.peak (r : Run) : Nat :=
  r.initial + r.setupEvents.count .allocation +
    (r.queryEvents.map (fun t => t.count .allocation)).foldl max 0

theorem execute_count_repeated (policy : Policy) (p : Spine) (m : Nat)
    (q : Request) (k : Nat) (kind : Kind) :
    (execute policy p m (List.replicate k q)).count kind =
      (setup policy p m).events.count kind +
        k * (((setup policy p m).query q).2.count kind) := by
  simp [execute, Run.count]

/-- Existing resource observations can consume any category without changing
its value. The measured bind charges both the derivative and continuation. -/
theorem parse_category_cons (p : Spine) (b : Bool) (w : List Bool) (kind : Kind) :
    Resources.reweight (fun t : Trace => t.count kind) (p.parseRun (b :: w)) =
      Resources.bind
        (Resources.reweight (fun t : Trace => t.count kind) (p.deriveRun b))
        (fun q => Resources.reweight (fun t : Trace => t.count kind) (q.parseRun w)) := by
  simp [Spine.parseRun, Resources.reweight, Resources.bind, Trace.count,
    List.filter_append, List.map_append, List.sum_append]

/-- Equal positive tariffs per operation event and per allocated slot. Initial
source construction is outside the session, equally for all four policies. -/
def Run.work (r : Run) : Nat :=
  ([Kind.derivative, .nullable, .normalization, .map, .closure,
    .snapshot, .validation, .traversal, .allocation].map r.count).sum

end LanguageWitnesses.ParserWorkload
