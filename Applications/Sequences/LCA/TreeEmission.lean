import Applications.Sequences.LCA.TreeBackend

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.LCA.TreeBackend
open Resources

/-- Word arithmetic and writes are separate primitive events. A cached branch
    stores its count and two child references; a leaf stores its tag. -/
def addWord (a b : Nat) : Measured Nat Nat := (a + b, 1)
def cacheLeaf : Measured Tree.Cached Nat := (.singleton, 1)
def cacheBranch (n : Nat) (t c : Tree.Cached) : Measured Tree.Cached Nat := (.attach n t c, 3)
def emitPair (a d : Nat) : Measured (Nat × Nat) Nat := ((a,d), 2)

/-- Each node is visited once to cache counts; count fields are read through
    `readWord` and the stored sum flows from `addWord`. -/
def cacheM : Tree → Measured Tree.Cached Nat
  | .singleton => cacheLeaf
  | .attach t c =>
      Resources.bind (cacheM t) fun ct =>
      Resources.bind (cacheM c) fun cc =>
      Resources.bind (readWord ct.count) fun nt =>
      Resources.bind (readWord cc.count) fun nc =>
      Resources.bind (addWord nt nc) fun n => cacheBranch n ct cc

theorem cacheM_value (t : Tree) : (cacheM t).1 = t.cache := by
  induction t with
  | singleton => rfl
  | attach t c iht ihc => simp [cacheM, cacheBranch, readWord, addWord, Resources.bind, Tree.cache, iht, ihc]

theorem cacheM_cost (t : Tree) : (cacheM t).2 ≤ 6 * t.cache.calls := by
  induction t with
  | singleton => decide
  | attach t c iht ihc =>
    simp only [cacheM, Resources.bind, readWord, addWord, cacheBranch, Tree.cache, Tree.Cached.calls]
    omega

/-- Measured execution of the difference-list emitter. Its output is produced
    by pair writes, and offsets/depths flow through measured word arithmetic. -/
def emitM : Tree.Cached → Nat → Nat → List (Nat × Nat) → Measured (List (Nat × Nat)) Nat
  | .singleton, base, d, tail =>
      Resources.bind (emitPair base d) fun p => pure (p :: tail)
  | .attach _ t c, base, d, tail =>
      Resources.bind (readWord t.count) fun count =>
      Resources.bind (addWord base count) fun next =>
      Resources.bind (increment d) fun deeper =>
      Resources.bind (emitPair base d) fun back =>
      Resources.bind (emitM c next deeper (back :: tail)) fun rest =>
      emitM t base d rest

theorem emitM_value (t : Tree.Cached) (base d : Nat) (tail : List (Nat × Nat)) :
    (emitM t base d tail).1 = t.emit base d tail := by
  induction t generalizing base d tail with
  | singleton => rfl
  | attach n t c iht ihc =>
    simp [emitM, emitPair, readWord, addWord, increment, Resources.bind, Tree.Cached.emit, iht, ihc]

theorem emitM_cost (t : Tree.Cached) (base d : Nat) (tail : List (Nat × Nat)) :
    (emitM t base d tail).2 ≤ 5 * t.calls := by
  induction t generalizing base d tail with
  | singleton => simp [emitM, emitPair, Resources.bind, Resources.pure, Tree.Cached.calls]
  | attach n t c iht ihc =>
    simp only [emitM, emitPair, readWord, addWord, increment, Resources.bind, Tree.Cached.calls]
    have ht := iht base d (emitM c (base + t.count) (d+1) ((base,d)::tail)).1
    have hc := ihc (base + t.count) (d+1) ((base,d)::tail)
    omega

/-- Both passes are sequenced before any query is available. -/
def prepareEmissionM (t : Tree) : Measured (List (Nat × Nat)) Nat :=
  Resources.bind (cacheM t) fun ct => emitM ct 0 0 []

theorem prepareEmissionM_value (t : Tree) :
    (prepareEmissionM t).1 = t.tour.map (fun a => (Tree.code a, Tree.depth a)) := by
  simp [prepareEmissionM, Resources.bind, cacheM_value, emitM_value, Tree.emit_spec]

theorem prepareEmissionM_cost (t : Tree) : (prepareEmissionM t).2 ≤ 11 * t.cache.calls := by
  simp only [prepareEmissionM, Resources.bind, cacheM_value]
  have hc := cacheM_cost t
  have he := emitM_cost t.cache 0 0 []
  omega

/-- Separate control-flow accounting: there are two recursive passes, each with
    one constructor dispatch per cached node. This is not a wall-clock claim. -/
theorem preparation_dispatches (t : Tree) : 2 * t.cache.calls + 2 = 4 * t.size := by
  have := Tree.cache_calls t
  omega

end Sequences.LCA.TreeBackend
