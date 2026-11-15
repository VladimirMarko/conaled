import Applications.Languages.WitnessTrie

/-! An explicit finite binary-alphabet snapshot. Both children are stored data,
not a function which recomputes derivatives when applied. Logical costs count
parser derivative calls, decision cells, and traversed snapshot edges. -/
namespace LanguageWitnesses
namespace RetainedSnapshot

inductive Tree : Language Bool → Nat → Type 1 where
  | leaf {P} : Decision (P []) → Tree P 0
  | node {P n} : Decision (P []) → Tree (derivative P false) n →
      Tree (derivative P true) n → Tree P (n+1)

def Tree.toTrie {P} : {n : Nat} → Tree P n → WitnessTrie P n
  | _, .leaf d => .leaf d
  | _, .node d l r => .node d (fun | false => l.toTrie | true => r.toTrie)

/-- Each recursive build explicitly evaluates each derivative once. The second
component counts precisely those calls, including both finite branches. -/
def build {P : Language Bool} (p : Parser P) : (n : Nat) → Tree P n × Nat
  | 0 => (.leaf p.nullable, 0)
  | n+1 =>
    let l := build (p.derive false) n
    let r := build (p.derive true) n
    (.node p.nullable l.1 r.1, 2 + l.2 + r.2)

def cells : Nat → Nat
  | 0 => 1
  | n+1 => 1 + 2 * cells n

def Tree.size {P} : {n : Nat} → Tree P n → Nat
  | _, .leaf _ => 1
  | _, .node _ l r => 1 + l.size + r.size

theorem Tree.size_eq {P} {n} (t : Tree P n) : t.size = cells n := by
  induction t with
  | leaf => rfl
  | node d l r il ir => simp [Tree.size, cells, il, ir, Nat.succ_mul, Nat.add_assoc]

theorem build_work {P : Language Bool} (p : Parser P) (n) :
    (build p n).2 + 1 = cells n := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    simp only [build, cells]
    have hl := ih (p.derive false)
    have hr := ih (p.derive true)
    omega

theorem build_toTrie {P : Language Bool} (p : Parser P) (n) :
    (build p n).1.toTrie = WitnessTrie.unfold p n := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    simp only [build, Tree.toTrie, WitnessTrie.unfold]
    congr 1
    funext b
    cases b <;> exact ih _

def Tree.lookup {P} : {n : Nat} → Tree P n → (w : List Bool) → w.length ≤ n → Decision (P w)
  | _, .leaf d, [], _ => d
  | _, .leaf _, _ :: _, h => False.elim (Nat.not_succ_le_zero _ h)
  | _, .node d _ _, [], _ => d
  | _, .node _ l _, false :: w, h => l.lookup w (Nat.le_of_succ_le_succ h)
  | _, .node _ _ r, true :: w, h => r.lookup w (Nat.le_of_succ_le_succ h)

theorem Tree.lookup_toTrie {P} {n} (t : Tree P n) (w) (h : w.length ≤ n) :
    t.lookup w h = t.toTrie.lookup w h := by
  induction t generalizing w with
  | leaf d => cases w <;> simp_all [Tree.lookup, Tree.toTrie, WitnessTrie.lookup]
  | node d l r il ir =>
    cases w with
    | nil => rfl
    | cons b w => cases b <;> simp_all [Tree.lookup, Tree.toTrie, WitnessTrie.lookup] <;> rfl

/-- Count stored edges traversed, with no parser or derivative in the lookup. -/
def Tree.lookupCounted {P} : {n : Nat} → Tree P n → (w : List Bool) →
    w.length ≤ n → Decision (P w) × Nat
  | _, .leaf d, [], _ => (d, 0)
  | _, .leaf _, _ :: _, h => False.elim (Nat.not_succ_le_zero _ h)
  | _, .node d _ _, [], _ => (d, 0)
  | _, .node _ l _, false :: w, h =>
    let r := l.lookupCounted w (Nat.le_of_succ_le_succ h)
    (r.1, r.2 + 1)
  | _, .node _ _ r, true :: w, h =>
    let s := r.lookupCounted w (Nat.le_of_succ_le_succ h)
    (s.1, s.2 + 1)

theorem Tree.lookupCounted_correct {P} {n} (t : Tree P n) (w) (h : w.length ≤ n) :
    t.lookupCounted w h = (t.lookup w h, w.length) := by
  induction t generalizing w with
  | leaf d =>
    cases w with
    | nil => rfl
    | cons b w => exact False.elim (Nat.not_succ_le_zero _ h)
  | node d l r il ir =>
    cases w with
    | nil => rfl
    | cons b w => cases b <;> simp_all [Tree.lookupCounted, Tree.lookup]

theorem lookup_build {P : Language Bool} (p : Parser P) (n) (w) (h : w.length ≤ n) :
    (build p n).1.lookup w h = p.parse w := by
  rw [Tree.lookup_toTrie, build_toTrie, WitnessTrie.lookup_unfold]

/-- A request declares a visible depth. A too-deep view or too-long word fails
explicitly; it never quietly runs the parser or consumes an input character. -/
def query {P} {m} (t : Tree P m) (depth : Nat) (w : List Bool) : Option (Decision (P w)) :=
  if h : depth ≤ m ∧ w.length ≤ depth then some (t.lookup w (Nat.le_trans h.2 h.1)) else none

theorem query_hit {P} {m} (t : Tree P m) (depth : Nat) (w : List Bool) :
    (query t depth w).isSome = decide (depth ≤ m ∧ w.length ≤ depth) := by
  unfold query
  split <;> simp_all

theorem query_build {P : Language Bool} (p : Parser P) (m depth) (w : List Bool) :
    query (build p m).1 depth w =
      if depth ≤ m ∧ w.length ≤ depth then some (p.parse w) else none := by
  unfold query
  split <;> simp_all [lookup_build]

/-- Querying a shallower view agrees with actual native restriction, including
its selected nullable-star decision. The stored tree itself is retained. -/
theorem query_restricted {P} {m} (t : Tree P m) (depth) (h : depth ≤ m)
    (w : List Bool) (hw : w.length ≤ depth) :
    query t depth w = some ((WitnessTrie.truncate depth h t.toTrie).lookup w hw) := by
  simp [query, h, hw, Tree.lookup_toTrie, WitnessTrie.lookup_truncate]

abbrev Request := Nat × List Bool

def admissible (m : Nat) (q : Request) : Prop := q.1 ≤ m ∧ q.2.length ≤ q.1
instance (m : Nat) (q : Request) : Decidable (admissible m q) := inferInstanceAs (Decidable (_ ∧ _))

structure Counts where
  hits : Nat := 0
  misses : Nat := 0
  edges : Nat := 0
  checks : Nat := 0
  deriving DecidableEq, Repr

/-- Batch execution returns actual decisions alongside the accounting. The
caller retains the same tree for the entire batch; no derivative call occurs. -/
def batch {P} {m} (t : Tree P m) : (qs : List Request) →
    List ((q : Request) × Option (Decision (P q.2))) × Counts
  | [] => ([], {})
  | q :: qs =>
    let result := query t q.1 q.2
    let rest := batch t qs
    let ok := result.isSome
    (⟨q, result⟩ :: rest.1,
      { hits := rest.2.hits + if ok then 1 else 0
        misses := rest.2.misses + if ok then 0 else 1
        edges := rest.2.edges + if ok then q.2.length else 0
        checks := rest.2.checks + 2 })

/-- Recomputing baseline: each admitted request independently parses its word.
Each consumed symbol invokes Parser.derive once; rejected requests cost none. -/
def parseCounted {P : Language Bool} (p : Parser P) : (w : List Bool) → Decision (P w) × Nat
  | [] => (p.nullable, 0)
  | b :: w =>
    let rest := parseCounted (p.derive b) w
    (rest.1, rest.2 + 1)

theorem parseCounted_correct {P : Language Bool} (p : Parser P) (w) :
    parseCounted p w = (p.parse w, w.length) := by
  induction w generalizing P with
  | nil => rfl
  | cons b w ih => simp [parseCounted, Parser.parse, ih]

def baselineDerivatives (m : Nat) (qs : List Request) : Nat :=
  (qs.map (fun q => if admissible m q then q.2.length else 0)).sum

theorem baseline_instrumented {P : Language Bool} (p : Parser P) (m) (qs) :
    (qs.map (fun q => if admissible m q then (parseCounted p q.2).2 else 0)).sum =
      baselineDerivatives m qs := by
  simp [parseCounted_correct, baselineDerivatives]

theorem batch_edges {P} {m} (t : Tree P m) (qs) :
    (batch t qs).2.edges = baselineDerivatives m qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    by_cases h : q.1 ≤ m ∧ q.2.length ≤ q.1 <;>
      simp [batch, baselineDerivatives, query_hit, admissible, h] at * <;> omega

theorem batch_checks {P} {m} (t : Tree P m) (qs) :
    (batch t qs).2.checks = 2 * qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [batch, ih, Nat.mul_add]

theorem batch_results {P} {m} (p : Parser P) (qs) :
    (batch (build p m).1 qs).1 = qs.map (fun q =>
      ⟨q, if admissible m q then some (p.parse q.2) else none⟩) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [batch, List.map_cons, ih, query_build]
    rfl

theorem batch_hits_misses {P} {m} (t : Tree P m) (qs) :
    (batch t qs).2.hits + (batch t qs).2.misses = qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [batch, List.length_cons]
    split <;> omega

theorem batch_output_size {P} {m} (t : Tree P m) (qs) :
    (batch t qs).1.length = qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [batch, ih]

/-- Repeated requests share the precomputed prefix tree. -/
theorem repeated_baseline (m : Nat) (q : Request) (k : Nat) (h : admissible m q) :
    baselineDerivatives m (List.replicate k q) = k * q.2.length := by
  simp [baselineDerivatives, h]

theorem repeated_saves {P : Language Bool} (p : Parser P) (m k : Nat)
    (q : Request) (h : admissible m q) (enough : cells m ≤ k * q.2.length) :
    (build p m).2 < baselineDerivatives m (List.replicate k q) := by
  rw [repeated_baseline m q k h]
  have := build_work p m
  omega

end RetainedSnapshot
end LanguageWitnesses
