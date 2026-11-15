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
  | .singleton => dispatch cacheLeaf
  | .attach t c =>
      dispatch <| Resources.bind (cacheM t) fun ct =>
      Resources.bind (cacheM c) fun cc =>
      Resources.bind (readWord ct.count) fun nt =>
      Resources.bind (readWord cc.count) fun nc =>
      Resources.bind (addWord nt nc) fun n => cacheBranch n ct cc

theorem cacheM_value (t : Tree) : (cacheM t).1 = t.cache := by
  induction t with
  | singleton => rfl
  | attach t c iht ihc => simp [cacheM, dispatch, cacheBranch, readWord, addWord, Resources.bind, Tree.cache, iht, ihc]

theorem cacheM_cost (t : Tree) : (cacheM t).2 ≤ 7 * t.cache.calls := by
  induction t with
  | singleton => decide
  | attach t c iht ihc =>
    simp only [cacheM, dispatch, Resources.bind, readWord, addWord, cacheBranch, Tree.cache, Tree.Cached.calls]
    omega

/-- Measured execution of the difference-list emitter. Its output is produced
    by pair writes, and offsets/depths flow through measured word arithmetic. -/
def emitM : Tree.Cached → Nat → Nat → List (Nat × Nat) → Measured (List (Nat × Nat)) Nat
  | .singleton, base, d, tail =>
      dispatch <| Resources.bind (emitPair base d) fun p => pure (p :: tail)
  | .attach _ t c, base, d, tail =>
      dispatch <| Resources.bind (readWord t.count) fun count =>
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
    simp [emitM, dispatch, emitPair, readWord, addWord, increment, Resources.bind, Tree.Cached.emit, iht, ihc]

theorem emitM_cost (t : Tree.Cached) (base d : Nat) (tail : List (Nat × Nat)) :
    (emitM t base d tail).2 ≤ 6 * t.calls := by
  induction t generalizing base d tail with
  | singleton => simp [emitM, dispatch, emitPair, Resources.bind, Resources.pure, Tree.Cached.calls]
  | attach n t c iht ihc =>
    simp only [emitM, dispatch, emitPair, readWord, addWord, increment, Resources.bind, Tree.Cached.calls]
    have ht := iht base d (emitM c (base + t.count) (d+1) ((base,d)::tail)).1
    have hc := ihc (base + t.count) (d+1) ((base,d)::tail)
    omega

/-- Both passes are sequenced before any query is available. -/
def prepareEmissionM (t : Tree) : Measured (List (Nat × Nat)) Nat :=
  Resources.bind (cacheM t) fun ct => emitM ct 0 0 []

theorem prepareEmissionM_value (t : Tree) :
    (prepareEmissionM t).1 = t.tour.map (fun a => (Tree.code a, Tree.depth a)) := by
  simp [prepareEmissionM, Resources.bind, cacheM_value, emitM_value, Tree.emit_spec]

theorem prepareEmissionM_cost (t : Tree) : (prepareEmissionM t).2 ≤ 13 * t.cache.calls := by
  simp only [prepareEmissionM, Resources.bind, cacheM_value]
  have hc := cacheM_cost t
  have he := emitM_cost t.cache 0 0 []
  omega


/-- Metadata is produced from the stored cached count, with arithmetic charged.
    No semantic tree traversal is used to obtain runtime arena dimensions. -/
def emissionDataM (t : Tree) : Measured (Nat × Nat × List (Nat × Nat)) Nat :=
  Resources.bind (cacheM t) fun ct =>
  Resources.bind (readWord ct.count) fun n =>
  Resources.bind (addWord n n) fun twice =>
  Resources.bind ((twice-1,1) : Measured Nat Nat) fun m =>
  Resources.bind (emitM ct 0 0 []) fun raw => pure (n,m,raw)

theorem emissionDataM_value (t : Tree) :
    (emissionDataM t).1 = (t.size,t.tour.length,t.cache.emit 0 0 []) := by
  simp only [emissionDataM, Resources.bind, cacheM_value, readWord, Tree.cache_count,
    addWord, emitM_value, Resources.pure]
  congr 2
  have := Tree.tour_length t
  have := Tree.size_pos t
  omega

theorem emissionDataM_cost (t : Tree) : (emissionDataM t).2 ≤ 13*t.cache.calls + 3 := by
  simp only [emissionDataM, Resources.bind, cacheM_value, readWord, addWord,
    Resources.pure]
  have hc := cacheM_cost t
  have he := emitM_cost t.cache 0 0 []
  omega

structure EmissionInfo (t : Tree) where
  nodes : Nat
  entries : Nat
  raw : List (Nat × Nat)
  nodes_eq : nodes = t.size
  entries_eq : entries = t.tour.length
  raw_eq : raw = t.cache.emit 0 0 []

def emissionInfoM (t : Tree) : Measured (EmissionInfo t) Nat :=
  let r := emissionDataM t
  (⟨r.1.1,r.1.2.1,r.1.2.2,
    congrArg Prod.fst (emissionDataM_value t),
    congrArg (fun p => p.2.1) (emissionDataM_value t),
    congrArg (fun p => p.2.2) (emissionDataM_value t)⟩,r.2)

theorem emissionInfoM_value (t : Tree) : (emissionInfoM t).1 =
    ⟨t.size,t.tour.length,t.cache.emit 0 0 [],rfl,rfl,rfl⟩ := by
  generalize (emissionInfoM t).1 = info
  rcases info with ⟨nodes, entries, raw, rfl, rfl, rfl⟩
  rfl


theorem emissionInfoM_eq (t : Tree) : emissionInfoM t =
    (⟨t.size,t.tour.length,t.cache.emit 0 0 [],rfl,rfl,rfl⟩,(emissionDataM t).2) :=
  Prod.ext (emissionInfoM_value t) rfl

/-- Both recursive passes charge one constructor dispatch per cached node.
    This count is already included in `cacheM` and `emitM`. -/
theorem preparation_dispatches (t : Tree) : 2 * t.cache.calls + 2 = 4 * t.size := by
  have := Tree.cache_calls t
  omega

end Sequences.LCA.TreeBackend
