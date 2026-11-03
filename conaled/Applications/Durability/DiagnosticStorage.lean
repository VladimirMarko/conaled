import Applications.Durability.DiagnosticProjection

namespace Durability.Diagnostic
open Interaction.Events

/-- These annotations are attached to actual read constructors. Boundary and
finish are explicit transitions with no structural read charge. -/
inductive ReadTrace (disk : Heap (Cell P)) : Cursor P → Cursor P → List StorageEvent → Prop
  | nil {c} : ReadTrace disk c c []
  | flat {a as seen tip e d events} : disk a = some (.flat e) →
      ReadTrace disk (.prefixCells as (seen ++ [e]) tip) d events →
      ReadTrace disk (.prefixCells (a::as) seen tip) d (.readRecord :: events)
  | node {a prev e pre suffix d events} : disk a = some (.node prev e) →
      ReadTrace disk (.tailCells prev pre (e::suffix)) d events →
      ReadTrace disk (.tailCells (some a) pre suffix) d (.readRecord :: .followLink :: events)
  | boundary {seen tip d events} : ReadTrace disk (.tailCells tip seen []) d events →
      ReadTrace disk (.prefixCells [] seen tip) d events
  | finish {pre suffix} : ReadTrace disk (.tailCells none pre suffix) (.done (pre ++ suffix)) []

theorem ReadTrace.sound {disk : Heap (Cell P)} {c d events}
    (run : ReadTrace disk c d events) : Relation.ReflTransGen (Read disk) c d := by
  induction run with
  | nil => exact .refl
  | flat lookup run ih => exact .head (.flat lookup) ih
  | node lookup run ih => exact .head (.node lookup) ih
  | boundary run ih => exact .head .boundary ih
  | finish => exact .single .finish

theorem read_machine {s : Machine P} {c d} (offline : s.cache = none)
    (cursor : s.cursor = some c) (run : Relation.ReflTransGen (Read s.disk) c d) :
    ∃ events, interpret Step events s {s with cursor := some d} := by
  have aux : ∀ {c d}, Relation.ReflTransGen (Read s.disk) c d →
      ∃ events, interpret Step events {s with cursor := some c} {s with cursor := some d} := by
    intro c d run
    induction run using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[],rfl⟩
    | @head a b read rest ih =>
      obtain ⟨events, tail⟩ := ih
      exact ⟨.internal :: events, {s with cursor := some b}, .read offline rfl read, tail⟩
  have eq : {s with cursor := some c} = s := by cases s; simp_all
  simpa only [eq] using aux run

theorem chain_read_count {disk : Heap (Cell P)} {tip h} (chain : Chain disk tip h)
    (pre suffix : List (Record P)) (w : StorageEvent → Nat) :
    ∃ events, ReadTrace disk (.tailCells tip pre suffix) (.done (pre ++ h ++ suffix)) events ∧
      weighted w events = h.length * (w .readRecord + w .followLink) := by
  induction chain generalizing suffix with
  | nil => exact ⟨[], by simpa using ReadTrace.finish (pre := pre) (suffix := suffix), by simp [weighted]⟩
  | @snoc a prev h e lookup chain ih =>
    obtain ⟨events, run, cost⟩ := ih (e::suffix)
    refine ⟨.readRecord :: .followLink :: events, ?_, ?_⟩
    · simpa [List.append_assoc] using ReadTrace.node lookup run
    · simp only [weighted, List.map_cons, List.sum_cons] at *
      simp only [List.length_append,List.length_singleton]
      rw [cost]; ring

theorem checkpoint_read_count {disk : Heap (Cell P)} {as pre tip tail}
    (array : Array disk as pre) (chain : Chain disk tip tail) (seen : List (Record P))
    (w : StorageEvent → Nat) :
    ∃ events, ReadTrace disk (.prefixCells as seen tip) (.done (seen ++ pre ++ tail)) events ∧
      weighted w events = pre.length * w .readRecord +
        tail.length * (w .readRecord + w .followLink) := by
  induction array generalizing seen with
  | nil =>
    obtain ⟨events, run, cost⟩ := chain_read_count chain seen [] w
    exact ⟨events, .boundary (by simpa using run), by simpa using cost⟩
  | @cons a as e es lookup array ih =>
    obtain ⟨events, run, cost⟩ := ih (seen ++ [e])
    refine ⟨.readRecord :: events, ?_, ?_⟩
    · apply ReadTrace.flat lookup
      simpa [List.append_assoc] using run
    · simp only [weighted,List.map_cons,List.sum_cons] at *
      rw [cost]
      simp only [List.length_cons]
      ring

def writePersist (s : Machine P) (entry : Nat × Cell P) : Machine P :=
  persistState (writeState s entry.1 entry.2) entry.1 entry.2
def persistCells (s : Machine P) (cells : List (Nat × Cell P)) : Machine P :=
  cells.foldl writePersist s

/-- A logical batch is an actual sequence of buffered writes and per-cell
persistence transitions. One batch completion is a separate declared tariff;
it makes no claim of one physical flush. -/
theorem persist_cells_execution (s : Machine P) (p : Plan P)
    (pending : s.pending = some p) (cells : List (Nat × Cell P))
    (planned : ∀ x ∈ cells, p.writes x.1 = some x.2)
    (compatible : ∀ x ∈ cells, s.disk x.1 = none ∨ s.disk x.1 = some x.2) :
    interpret Step (List.replicate (2*cells.length) .internal) s (persistCells s cells) := by
  induction cells generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have plan := planned x (by simp)
    have compat : ∀ y ∈ xs, (writePersist s x).disk y.1 = none ∨
        (writePersist s x).disk y.1 = some y.2 := by
      intro y hy
      by_cases eq : y.1 = x.1
      · right
        have same : x.2 = y.2 := Option.some.inj (plan.symm.trans (eq ▸ planned y (by simp [hy])))
        simp [writePersist,put,eq,same]
      · simpa [writePersist,put,eq] using compatible y (by simp [hy])
    have rest := ih (writePersist s x) pending (fun y hy => planned y (by simp [hy])) compat
    have run : interpret Step (.internal :: .internal :: List.replicate (2*xs.length) .internal)
        s (persistCells s (x::xs)) :=
      ⟨writeState s x.1 x.2, .write pending plan, writePersist s x,
        .persist pending plan (by simp [put]) (compatible x (by simp)), rest⟩
    rw [show 2*(x::xs).length = 2 + 2*xs.length by simp; omega, List.replicate_add]
    exact run

theorem persist_cells_pending (s : Machine P) (cells : List (Nat × Cell P)) :
    (persistCells s cells).pending = s.pending := by
  induction cells generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (writePersist s x)

theorem persist_cells_retains (s : Machine P) (p : Plan P) (cells : List (Nat × Cell P))
    (planned : ∀ x ∈ cells, p.writes x.1 = some x.2)
    {i c} (pc : p.writes i = some c) (already : s.disk i = some c) :
    (persistCells s cells).disk i = some c := by
  induction cells generalizing s with
  | nil => exact already
  | cons x xs ih =>
    apply ih (writePersist s x) (fun y hy => planned y (by simp [hy]))
    by_cases eq : i = x.1
    · have same : x.2 = c := Option.some.inj ((planned x (by simp)).symm.trans (eq ▸ pc))
      simp [writePersist,put,eq,same]
    · simpa [writePersist,put,eq] using already

theorem persist_cells_stored (s : Machine P) (p : Plan P) (cells : List (Nat × Cell P))
    (planned : ∀ x ∈ cells, p.writes x.1 = some x.2) {i c} (mem : (i,c) ∈ cells) :
    (persistCells s cells).disk i = some c := by
  induction cells generalizing s with
  | nil => simp at mem
  | cons x xs ih =>
    rcases List.mem_cons.mp mem with eq | mem
    · subst x
      exact persist_cells_retains (writePersist s (i,c)) p xs
        (fun y hy => planned y (by simp [hy])) (planned (i,c) (by simp)) (by simp [writePersist,put])
    · exact ih (writePersist s x) (fun y hy => planned y (by simp [hy])) mem

theorem replacement_execution (s : Machine P) (h : List (Record P)) (p : Plan P)
    (ready : s.cache = some h) (idle : s.active = none) (noplan : s.pending = none)
    (source : p.source = s.disk) (before : p.before = h) (noappend : p.appended = none)
    (cells : List (Nat × Cell P))
    (enumerates : ∀ i c, p.writes i = some c ↔ (i,c) ∈ cells)
    (unused : ∀ x ∈ cells, x.1 ∉ s.used)
    (fresh : ∀ x ∈ cells, s.disk x.1 = none) :
    let prepared := prepareState s p
    let persisted := persistCells prepared cells
    interpret Step (.internal :: List.replicate (2*cells.length) .internal ++ [.internal])
      s (publishState persisted p) := by
  dsimp only
  have planned : ∀ x ∈ cells, p.writes x.1 = some x.2 :=
    fun x hx => (enumerates x.1 x.2).mpr hx
  have prep : Step .internal s (prepareState s p) := by
    apply Step.prepare ready noplan source before (noappend.trans idle.symm)
    · simp [noappend]
    · intro i c found
      exact unused (i,c) ((enumerates i c).mp found)
  have run := persist_cells_execution (prepareState s p) p rfl cells planned
    (fun x hx => Or.inl (fresh x hx))
  have per : Extends p.writes (persistCells (prepareState s p) cells).disk := by
    intro i c found
    exact persist_cells_stored _ p cells planned ((enumerates i c).mp found)
  have pub : Step .internal (persistCells (prepareState s p) cells)
      (publishState (persistCells (prepareState s p) cells) p) := by
    simpa [noappend] using Step.publish
      (persist_cells_pending (prepareState s p) cells) per
  refine ⟨prepareState s p, prep, ?_⟩
  change interpret Step ((List.replicate (2*cells.length) .internal) ++ [.internal]) _ _
  rw [interpret_append]
  exact ⟨persistCells (prepareState s p) cells,run,_,pub,rfl⟩

/-- Counts of the actual list-driven write/persist loop. Publication and batch
completion are counted separately from these per-cell actions. -/
def persistenceEvents (cells : List (Nat × Cell P)) : List StorageEvent :=
  cells.flatMap fun _ => [.write,.persist]

inductive PersistenceTrace : List (Nat × Cell P) → Machine P → Machine P → Prop
  | nil {s} : PersistenceTrace [] s s
  | cons {x xs s v} : StorageStep [.write] s (writeState s x.1 x.2) →
      StorageStep [.persist] (writeState s x.1 x.2) (writePersist s x) →
      PersistenceTrace xs (writePersist s x) v → PersistenceTrace (x::xs) s v

theorem persist_cells_annotated (s : Machine P) (p : Plan P)
    (pending : s.pending = some p) (cells : List (Nat × Cell P))
    (planned : ∀ x ∈ cells, p.writes x.1 = some x.2)
    (compatible : ∀ x ∈ cells, s.disk x.1 = none ∨ s.disk x.1 = some x.2) :
    PersistenceTrace cells s (persistCells s cells) := by
  induction cells generalizing s with
  | nil => exact .nil
  | cons x xs ih =>
    have plan := planned x (by simp)
    apply PersistenceTrace.cons (StorageStep.write pending plan)
      (StorageStep.persist pending plan (by simp [put]) (compatible x (by simp)))
    apply ih (writePersist s x) pending (fun y hy => planned y (by simp [hy]))
    intro y hy
    by_cases eq : y.1 = x.1
    · right
      have same : x.2 = y.2 := Option.some.inj (plan.symm.trans (eq ▸ planned y (by simp [hy])))
      simp [writePersist,put,eq,same]
    · simpa [writePersist,put,eq] using compatible y (by simp [hy])

theorem PersistenceTrace.sound {cells} {s t : Machine P} (run : PersistenceTrace cells s t) :
    ∃ events, interpret Step events s t := by
  induction run with
  | nil => exact ⟨[],rfl⟩
  | cons write persist run ih =>
    obtain ⟨e,write⟩ := write.sound
    obtain ⟨f,persist⟩ := persist.sound
    obtain ⟨events,rest⟩ := ih
    exact ⟨e::f::events,_,write,_,persist,rest⟩

/-- A logical completion observation is available only after the entire plan
is retained. It is distinct from each primitive cell persistence operation. -/
structure BatchComplete (p : Plan P) (cells : List (Nat × Cell P)) (s t : Machine P) : Prop where
  pending : s.pending = some p
  trace : PersistenceTrace cells s t
  persisted : Extends p.writes t.disk

inductive ChargeEvent where
  | primitive (event : StorageEvent)
  | batchComplete
  deriving DecidableEq

def batchEvents (cells : List (Nat × Cell P)) : List ChargeEvent :=
  (persistenceEvents cells).map ChargeEvent.primitive ++ [.batchComplete]

theorem persistence_count (w : StorageEvent → Nat) (cells : List (Nat × Cell P)) :
    weighted w (persistenceEvents cells) = cells.length * (w .write + w .persist) := by
  induction cells with
  | nil => simp [weighted,persistenceEvents]
  | cons x xs ih =>
    simp only [persistenceEvents,List.flatMap_cons,weighted_append] at *
    rw [ih]
    simp [weighted]
    ring

def eraseCell (s : Machine P) (i : Nat) : Machine P :=
  {s with disk := fun a => if a = i then none else s.disk a}

theorem link_needs_back {s t : Heap (Cell P)} (sub : Extends t s) {tip i}
    (need : LinkNeeds t tip i) : LinkNeeds s tip i := by
  induction need with
  | here => exact .here
  | next lookup need ih => exact .next (sub _ _ lookup) ih

theorem root_needs_back {s t : Heap (Cell P)} (sub : Extends t s) {root i}
    (need : RootNeeds t root i) : RootNeeds s root i := by
  rcases need with ⟨a,ptr,eq | ⟨as,lookup,mem⟩⟩ | link
  · exact Or.inl ⟨a,ptr,Or.inl eq⟩
  · exact Or.inl ⟨a,ptr,Or.inr ⟨as,sub _ _ lookup,mem⟩⟩
  · exact Or.inr (link_needs_back sub link)

theorem erase_subset (s : Machine P) (i : Nat) : Extends (eraseCell s i).disk s.disk := by
  intro a c found
  by_cases eq : a = i
  · simp [eraseCell,eq] at found
  · simpa [eraseCell,eq] using found

inductive ReclaimTrace : Nat → Machine P → Machine P → Prop
  | nil {s} : ReclaimTrace 0 s s
  | cons {n s t u} : StorageStep [.reclaimCell] s t → ReclaimTrace n t u → ReclaimTrace (n+1) s u

theorem reclaim_cells (s : Machine P) (ids : List Nat) (h : List (Record P))
    (ready : s.cache = some h) (idle : s.active = none) (noplan : s.pending = none)
    (unique : ids.Nodup) (allocated : ∀ i ∈ ids, ∃ c, s.disk i = some c)
    (unreachable : ∀ i ∈ ids, ¬ RootNeeds s.disk s.root i) :
    ReclaimTrace ids.length s (ids.foldl eraseCell s) := by
  induction ids generalizing s with
  | nil => exact .nil
  | cons i ids ih =>
    obtain ⟨absent,unique⟩ := List.nodup_cons.mp unique
    apply ReclaimTrace.cons (StorageStep.reclaim ready idle noplan
      (allocated i (by simp)) (unreachable i (by simp)))
    apply ih (eraseCell s i) ready idle noplan unique
    · intro j mem
      obtain ⟨c,found⟩ := allocated j (by simp [mem])
      have ne : j ≠ i := by intro eq; subst j; exact absent mem
      exact ⟨c,by simpa [eraseCell,ne] using found⟩
    · intro j mem need
      exact unreachable j (by simp [mem]) (root_needs_back (erase_subset s i) need)

theorem ReclaimTrace.sound {n} {s t : Machine P} (run : ReclaimTrace n s t) :
    ∃ events, interpret Step events s t := by
  induction run with
  | nil => exact ⟨[],rfl⟩
  | cons step run ih =>
    obtain ⟨ev,step⟩ := step.sound
    obtain ⟨events,run⟩ := ih
    exact ⟨ev::events,_,step,run⟩

theorem reclamation_count (w : StorageEvent → Nat) (n : Nat) :
    weighted w (List.replicate n .reclaimCell) = n*w .reclaimCell := by
  simp [weighted]

structure Tariff where
  recordRead : Nat
  linkFollow : Nat
  cellWrite : Nat
  cellPersist : Nat
  batchComplete : Nat
  rootInstall : Nat
  descriptorRead : Nat
  reclaim : Nat

def storageWeight (w : Tariff) : StorageEvent → Nat
  | .readRecord => w.recordRead
  | .followLink => w.linkFollow
  | .write => w.cellWrite
  | .persist => w.cellPersist
  | .installRoot => w.rootInstall
  | .readDescriptor => w.descriptorRead
  | .reclaimCell => w.reclaim
  | _ => 0

def chargeWeight (w : Tariff) : ChargeEvent → Nat
  | .primitive e => storageWeight w e
  | .batchComplete => w.batchComplete

theorem completed_batch_cost (w : Tariff) (cells : List (Nat × Cell P)) :
    ((batchEvents cells).map (chargeWeight w)).sum =
      cells.length*(w.cellWrite+w.cellPersist)+w.batchComplete := by
  simp only [batchEvents,List.map_append,List.sum_append,List.map_map,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  change weighted (storageWeight w) (persistenceEvents cells) + w.batchComplete = _
  rw [persistence_count]
  rfl

/-- Structural counts retain per-cell persistence in addition to #227's
logical completion count. Root reads and volatile/view work are separate. -/
def appendCost (w : Tariff) (n : Nat) :=
  n * (w.cellWrite + w.cellPersist + w.batchComplete + w.rootInstall)
def checkpointCost (w : Tariff) (n : Nat) :=
  n*w.recordRead + n*w.linkFollow + (n+1)*(w.cellWrite+w.cellPersist) +
    w.batchComplete + w.rootInstall + n*w.reclaim
def logRecovery (w : Tariff) (n : Nat) := n*(w.recordRead+w.linkFollow)
def checkpointRecovery (w : Tariff) (n k : Nat) :=
  n*w.recordRead + (n-k)*w.linkFollow + w.descriptorRead
def logTotal (w : Tariff) (n r : Nat) := appendCost w n + r*logRecovery w n
def checkpointTotal (w : Tariff) (n k r : Nat) :=
  appendCost w n + checkpointCost w n + r*checkpointRecovery w n k

theorem checkpoint_recovery_split (w : Tariff) (n k : Nat) (bound : k ≤ n) :
    k*w.recordRead + (n-k)*(w.recordRead+w.linkFollow) + w.descriptorRead =
      checkpointRecovery w n k := by
  unfold checkpointRecovery
  have eq : n = k + (n-k) := by omega
  conv_rhs => rw [eq]
  simp only [Nat.add_sub_cancel_left]
  ring

def assessmentTariff : Tariff := ⟨1,1,1,0,1,1,1,1⟩
theorem assessment_numbers :
    logTotal assessmentTariff 10 1 = 50 ∧ checkpointTotal assessmentTariff 10 8 1 = 86 ∧
    logTotal assessmentTariff 10 7 = 170 ∧ checkpointTotal assessmentTariff 10 8 7 = 164 := by decide

theorem common_work (w : Tariff) (n k r admission rebuild queries : Nat) :
    logTotal w n r + admission + r*rebuild + queries ≤
      checkpointTotal w n k r + admission + r*rebuild + queries ↔
    logTotal w n r ≤ checkpointTotal w n k r := by omega

theorem zero_link_no_payoff (w : Tariff) (n k r : Nat) (zero : w.linkFollow = 0) :
    logTotal w n r ≤ checkpointTotal w n k r := by
  simp only [logTotal,checkpointTotal,logRecovery,checkpointRecovery,zero,Nat.add_zero,Nat.mul_zero]
  nlinarith

/-- Old and copied cells coexist before publication; incomplete attempts keep
their allocated cells until explicitly reclaimed. No address reuse is assumed. -/
def retainedAfterCopy (n copied priorGarbage : Nat) := n + copied + priorGarbage
def steadyCheckpoint (n : Nat) := n+1
theorem copy_peak (n : Nat) : retainedAfterCopy n (n+1) 0 = 2*n+1 := by
  simp [retainedAfterCopy]; omega
theorem interrupted_space (n copied garbage : Nat) :
    retainedAfterCopy n copied garbage = n + copied + garbage := rfl
theorem interrupted_work (w : StorageEvent → Nat) (attempts : List (List StorageEvent)) :
    weighted w attempts.flatten = (attempts.map (weighted w)).sum := by
  induction attempts with
  | nil => rfl
  | cons xs xss ih => simp [List.flatten_cons,weighted_append,ih]

end Durability.Diagnostic
