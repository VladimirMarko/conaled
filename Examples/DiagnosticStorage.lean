import Examples.DiagnosticProjection

namespace Examples.DiagnosticStorage
open Durability Durability.Diagnostic Interaction.Events

def record (i : Nat) : Record (Edge 2) := ⟨9,i,(0,1)⟩
def history : History 2 :=
  [record 0,record 1,record 2,record 3,record 4,record 5,record 6,record 7,record 8,record 9]
def oldDisk : Heap (Cell (Edge 2)) := fun i =>
  if i < 10 then some (.node (if i = 0 then none else some (i-1)) (record i)) else none
def oldRoot : Root := ⟨none,some 9⟩
theorem old_chain : Chain oldDisk (some 9) history := by
  exact .snoc rfl (.snoc rfl (.snoc rfl (.snoc rfl (.snoc rfl
    (.snoc rfl (.snoc rfl (.snoc rfl (.snoc rfl (.snoc rfl .nil)))))))))
theorem old_rep : Represents oldDisk oldRoot history := ⟨[],history,.nil,old_chain,rfl⟩
def oldMachine : Machine (Edge 2) :=
  ⟨oldDisk,oldRoot,some history,none,none,fun _ => none,none,{i | i < 10}⟩

def logTip (n : Nat) : Option Nat := if n = 0 then none else some (n-1)
def logDisk (n : Nat) : Heap (Cell (Edge 2)) := fun i =>
  if i < n then some (.node (logTip i) (record i)) else none
def logHistory (n : Nat) := (List.range n).map record
def logMachine (n : Nat) : Machine (Edge 2) :=
  ⟨logDisk n,⟨none,logTip n⟩,some (logHistory n),none,none,fun _ => none,none,{i | i < n}⟩

theorem log_disk_succ (n : Nat) :
    put (logDisk n) n (Cell.node (logTip n) (record n)) = logDisk (n+1) := by
  funext i
  by_cases eq : i = n
  · subst i; simp [put,logDisk]
  by_cases lower : i < n
  · simp [put,logDisk,eq,lower,show i < n+1 by omega]
  · simp [put,logDisk,eq,lower,show ¬ i < n+1 by omega]

theorem log_history_succ (n : Nat) : logHistory (n+1) = logHistory n ++ [record n] := by
  simp [logHistory,List.range_succ]

theorem log_rep (n : Nat) : Represents (logDisk n) ⟨none,logTip n⟩ (logHistory n) := by
  induction n with
  | zero => exact empty_rep _
  | succ n ih =>
    have rep := append_rep ih n (record n) (by simp [logDisk])
    rw [log_disk_succ,← log_history_succ] at rep
    simpa [logTip] using rep

theorem log_append_execution (n : Nat) :
    interpret Step (DiagnosticProjection.appendEvents (record n)) (logMachine n) (logMachine (n+1)) := by
  have unused : n ∉ (logMachine n).used := by simp [logMachine]
  have fresh : Fresh (logHistory n) (record n) := by
    intro e mem eq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
    have key : i = n := congrArg Prod.snd eq
    have bound := List.mem_range.mp hi
    omega
  have run := append_execution (logMachine n) (logHistory n) rfl rfl rfl (log_rep n)
    n (record n) (by simp [logMachine,logDisk]) unused fresh
  have used : {i : Nat | i < n} ∪ {i | ∃ c, put (fun _ => none) n
      (Cell.node (logTip n) (record n)) i = some c} = {i | i < n+1} := by
    ext i
    simp only [Set.mem_union,Set.mem_ofPred_eq,put]
    by_cases eq : i = n
    · simp [eq]
    · simp [eq]; omega
  change interpret Step (DiagnosticProjection.appendEvents (record n)) (logMachine n)
    ⟨put (logDisk n) n (Cell.node (logTip n) (record n)),⟨none,some n⟩,
      some (logHistory n ++ [record n]),none,none,fun _ => none,none,
      {i | i < n} ∪ {i | ∃ c, put (fun _ => none) n (Cell.node (logTip n) (record n)) i = some c}⟩ at run
  rw [log_disk_succ,used,← log_history_succ] at run
  simpa [logMachine,logTip] using run

def logWords (n : Nat) := (List.range n).flatMap fun i => DiagnosticProjection.appendEvents (record i)
theorem log_initial : logMachine 0 = (initial : Machine (Edge 2)) := by
  simp [logMachine,logHistory,logTip,initial,emptyRoot]
  rfl

theorem log_construction (n : Nat) : interpret Step (logWords n) initial (logMachine n) := by
  induction n with
  | zero => exact log_initial.symm
  | succ n ih =>
    simp only [logWords,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [interpret_append]
    exact ⟨logMachine n,ih,log_append_execution n⟩

theorem actual_ten_appends : interpret Step (logWords 10) initial oldMachine := log_construction 10

def logAppendPlan (n : Nat) := appendPlan (logMachine n).disk (logMachine n).root
  (logHistory n) (log_rep n) n (record n) (by simp [logMachine,logDisk])
abbrev logPrepared (n : Nat) := prepareState (invokeState (logMachine n) (record n)) (logAppendPlan n)
abbrev logWritten (n : Nat) := writeState (logPrepared n) n (.node (logTip n) (record n))
abbrev logPersisted (n : Nat) := persistState (logWritten n) n (.node (logTip n) (record n))

theorem log_append_annotations (n : Nat) :
    StorageStep [.write] (logPrepared n) (logWritten n) ∧
    StorageStep [.persist] (logWritten n) (logPersisted n) ∧
    StorageStep [.installRoot] (logPersisted n) (publishState (logPersisted n) (logAppendPlan n)) := by
  have cell : (logAppendPlan n).writes n = some (.node (logTip n) (record n)) := by
    simp [logAppendPlan,appendPlan,put,logMachine]
  refine ⟨.write rfl cell,.persist rfl cell (by simp [put])
    (Or.inl (by simp [logMachine,logDisk])),.publish rfl ?_⟩
  intro i c found
  by_cases eq : i = n
  · subst i
    have same : Cell.node (logTip n) (record n) = c := Option.some.inj (cell.symm.trans found)
    subst c
    simp [put]
  · simp [logAppendPlan,appendPlan,put,eq] at found

/-- Copy all ten records after the original log is complete. Eight become flat
cells; the two tail nodes link only into the new tail, never into the old log. -/
def cells : List (Nat × Cell (Edge 2)) :=
  [(20,.flat (record 0)),(21,.flat (record 1)),(22,.flat (record 2)),(23,.flat (record 3)),
   (24,.flat (record 4)),(25,.flat (record 5)),(26,.flat (record 6)),(27,.flat (record 7)),
   (28,.node none (record 8)),(29,.node (some 28) (record 9)),
   (30,.index [20,21,22,23,24,25,26,27])]
def writes : Heap (Cell (Edge 2)) := fun i =>
  if i = 30 then some (.index [20,21,22,23,24,25,26,27]) else
  if 20 ≤ i ∧ i < 28 then some (.flat (record (i-20))) else
  if i = 28 then some (.node none (record 8)) else
  if i = 29 then some (.node (some 28) (record 9)) else none
def root : Root := ⟨some 30,some 29⟩

theorem writes_enumerates (i : Nat) (c : Cell (Edge 2)) : writes i = some c ↔ (i,c) ∈ cells := by
  by_cases inrange : 20 ≤ i ∧ i ≤ 30
  · have cases : i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [writes,cells,eq_comm]
  · have h20 : i ≠ 20 := by omega
    have h21 : i ≠ 21 := by omega
    have h22 : i ≠ 22 := by omega
    have h23 : i ≠ 23 := by omega
    have h24 : i ≠ 24 := by omega
    have h25 : i ≠ 25 := by omega
    have h26 : i ≠ 26 := by omega
    have h27 : i ≠ 27 := by omega
    have h28 : i ≠ 28 := by omega
    have h29 : i ≠ 29 := by omega
    have h30 : i ≠ 30 := by omega
    have hout : ¬ (20 ≤ i ∧ i < 28) := by omega
    simp [writes,cells,hout,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30]

theorem new_rep : Represents (overlay writes oldDisk) root history := by
  refine ⟨[record 0,record 1,record 2,record 3,record 4,record 5,record 6,record 7],
    [record 8,record 9],?_,?_,rfl⟩
  · exact .block (as := [20,21,22,23,24,25,26,27]) rfl
      (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl .nil))))))))
  · exact .snoc rfl (.snoc rfl .nil)

def plan : Plan (Edge 2) := ⟨oldDisk,writes,root,history,none,history,by simp,new_rep⟩
abbrev prepared := prepareState oldMachine plan
abbrev persisted := persistCells prepared cells
abbrev published := publishState persisted plan

theorem cell_range {x : Nat × Cell (Edge 2)} (mem : x ∈ cells) : 20 ≤ x.1 ∧ x.1 ≤ 30 := by
  simp only [cells,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem copy_execution :
    interpret Step (.internal :: List.replicate 22 .internal ++ [.internal]) oldMachine published := by
  apply replacement_execution oldMachine history plan rfl rfl rfl rfl rfl rfl cells writes_enumerates
  · intro x mem
    have bound := cell_range mem
    change ¬ x.1 < 10
    omega
  · intro x mem
    have bound := cell_range mem
    simp [oldMachine,oldDisk,show ¬ x.1 < 10 by omega]

theorem copy_annotations : PersistenceTrace cells prepared persisted := by
  apply persist_cells_annotated prepared plan rfl cells
  · intro x mem
    exact (writes_enumerates _ _).mpr mem
  · intro x mem
    have bound := cell_range mem
    left
    simp [oldMachine,oldDisk,show ¬ x.1 < 10 by omega]

theorem publication_annotation : StorageStep [.installRoot] persisted published := by
  apply StorageStep.publish (persist_cells_pending prepared cells)
  intro i c found
  exact persist_cells_stored prepared plan cells
    (fun x mem => (writes_enumerates _ _).mpr mem) ((writes_enumerates _ _).mp found)

theorem completed_batch : BatchComplete plan cells prepared persisted := by
  refine ⟨rfl,copy_annotations,?_⟩
  intro i c found
  exact persist_cells_stored prepared plan cells
    (fun x mem => (writes_enumerates _ _).mpr mem) ((writes_enumerates _ _).mp found)

theorem published_rep : Represents published.disk root history := by
  refine ⟨[record 0,record 1,record 2,record 3,record 4,record 5,record 6,record 7],
    [record 8,record 9],?_,?_,rfl⟩
  · exact .block (as := [20,21,22,23,24,25,26,27]) rfl
      (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl .nil))))))))
  · exact .snoc rfl (.snoc rfl .nil)

theorem published_tail : Chain published.disk (some 29) [record 8,record 9] :=
  .snoc rfl (.snoc rfl .nil)
theorem published_array : Array published.disk [20,21,22,23,24,25,26,27]
    [record 0,record 1,record 2,record 3,record 4,record 5,record 6,record 7] :=
  .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl .nil)))))))

/-- Every current pointer lies in the new allocation. This is the premise for
actual old-cell reclamation, not an assumption of history preservation. -/
theorem current_needs {i : Nat} (need : RootNeeds published.disk published.root i) : 20 ≤ i := by
  rcases need with ⟨a,ptr,eq | ⟨as,lookup,mem⟩⟩ | link
  · have ae : a = 30 := Option.some.inj ptr.symm
    omega
  · have ae : a = 30 := Option.some.inj ptr.symm
    subst a
    have arr : as = [20,21,22,23,24,25,26,27] := by
      have same : some (Cell.index [20,21,22,23,24,25,26,27]) = some (Cell.index as) := lookup
      cases same; rfl
    rw [arr] at mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    omega
  · change LinkNeeds published.disk (some 29) i at link
    cases link with
    | here => omega
    | next lookup rest =>
      have same : some (Cell.node (some 28) (record 9)) = _ := lookup
      cases same
      cases rest with
      | here => omega
      | next lookup rest =>
        have same : some (Cell.node none (record 8)) = _ := lookup
        cases same
        cases rest

theorem old_cells_retained (i : Nat) (bound : i < 10) :
    ∃ c, published.disk i = some c := by
  have ne20 : i ≠ 20 := by omega
  have ne21 : i ≠ 21 := by omega
  have ne22 : i ≠ 22 := by omega
  have ne23 : i ≠ 23 := by omega
  have ne24 : i ≠ 24 := by omega
  have ne25 : i ≠ 25 := by omega
  have ne26 : i ≠ 26 := by omega
  have ne27 : i ≠ 27 := by omega
  have ne28 : i ≠ 28 := by omega
  have ne29 : i ≠ 29 := by omega
  have ne30 : i ≠ 30 := by omega
  simp [persistCells,cells,writePersist,put,oldMachine,oldDisk,bound,
    ne20,ne21,ne22,ne23,ne24,ne25,ne26,ne27,ne28,ne29,ne30]

theorem reclaim_execution :
    ReclaimTrace 10 published ((List.range 10).foldl eraseCell published) := by
  apply reclaim_cells published (List.range 10) history rfl rfl rfl (List.nodup_range)
  · intro i mem
    exact old_cells_retained i (List.mem_range.mp mem)
  · intro i mem needed
    have lower := current_needs needed
    have upper := List.mem_range.mp mem
    omega

theorem construction_reads (w : StorageEvent → Nat) : ∃ events,
    ReadTrace oldDisk (.tailCells (some 9) [] []) (.done history) events ∧
    weighted w events = 10*(w .readRecord+w .followLink) := by
  simpa [history] using chain_read_count old_chain [] [] w

theorem recovery_reads (w : StorageEvent → Nat) : ∃ events,
    ReadTrace published.disk (.prefixCells [20,21,22,23,24,25,26,27] [] (some 29))
      (.done history) events ∧ weighted w events = 10*w .readRecord + 2*w .followLink := by
  obtain ⟨events,run,cost⟩ := checkpoint_read_count published_array published_tail [] w
  refine ⟨events,run,?_⟩
  rw [cost]
  simp only [List.length_cons,List.length_nil]
  ring

theorem copy_writes (w : StorageEvent → Nat) :
    weighted w (persistenceEvents cells) = 11*(w .write+w .persist) := persistence_count w cells

def appendStorageEvents (n : Nat) : List StorageEvent :=
  (List.range n).flatMap fun _ => [.write,.persist,.installRoot]
theorem append_count (w : Tariff) (n : Nat) :
    weighted (storageWeight w) (appendStorageEvents n) + n*w.batchComplete = appendCost w n := by
  induction n with
  | zero => simp [appendStorageEvents,weighted,appendCost]
  | succ n ih =>
    simp only [appendStorageEvents,List.range_succ,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,weighted_append] at *
    simp only [weighted,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,storageWeight] at *
    unfold appendCost at *
    nlinarith

theorem actual_copy_space : (List.range 10).toFinset.card = 10 ∧
    (cells.map Prod.fst).toFinset.card = 11 ∧
    ((List.range 10).toFinset ∪ (cells.map Prod.fst).toFinset).card = 21 ∧
    Disjoint (List.range 10).toFinset (cells.map Prod.fst).toFinset := by decide

/-- An interrupted copy persists only its first two flat cells. Publication
has not happened and the original root still represents all ten records. -/
abbrev partialCopy := persistCells prepared (cells.take 2)
theorem interrupted_copy :
    interpret Step (List.replicate 4 .internal) prepared partialCopy ∧
    Represents (crashState partialCopy).disk (crashState partialCopy).root history := by
  constructor
  · apply persist_cells_execution prepared plan rfl (cells.take 2)
    · intro x mem
      exact (writes_enumerates _ _).mpr (List.mem_of_mem_take mem)
    · intro x mem
      have bound := cell_range (List.mem_of_mem_take mem)
      left
      simp [oldMachine,oldDisk,show ¬ x.1 < 10 by omega]
  · apply old_rep.mono
    intro i c found
    have bound : i < 10 := by
      by_contra no
      simp [oldDisk,no] at found
    simpa [partialCopy,persistCells,cells,writePersist,oldMachine,put,show i ≠ 20 by omega,
      show i ≠ 21 by omega] using found

theorem interrupted_no_completion : ¬ BatchComplete plan (cells.take 2) prepared partialCopy := by
  intro complete
  have impossible := complete.persisted 30 (.index [20,21,22,23,24,25,26,27]) rfl
  cases impossible

example : retainedAfterCopy 10 2 0 = 12 ∧ retainedAfterCopy 10 11 2 = 23 := by decide
example := assessment_numbers

/-- Root/descriptor reads are tied to the concrete published split layout. -/
theorem descriptor_read : StorageStep [.readRoot,.readDescriptor] (crashState published)
    {crashState published with cursor := some (.prefixCells [20,21,22,23,24,25,26,27] [] (some 29))} :=
  .readCheckpointRoot rfl rfl rfl rfl

/-- Summing the witnessed construction traversal, eleven actual cell pairs,
root installation and ten actual reclamations gives the proposed copy cost.
The batch-completion tariff is declared separately from per-cell persistence. -/
theorem connected_checkpoint_cost (w : Tariff) : ∃ reads,
    ReadTrace oldDisk (.tailCells (some 9) [] []) (.done history) reads ∧
    weighted (storageWeight w) (reads ++ persistenceEvents cells ++ [.installRoot] ++
      List.replicate 10 .reclaimCell) + w.batchComplete = checkpointCost w 10 := by
  obtain ⟨reads,run,cost⟩ := construction_reads (storageWeight w)
  refine ⟨reads,run,?_⟩
  simp only [weighted_append]
  rw [cost,copy_writes,reclamation_count]
  simp [weighted,storageWeight,checkpointCost]
  ring

theorem connected_recovery_cost (w : Tariff) : ∃ reads,
    ReadTrace published.disk (.prefixCells [20,21,22,23,24,25,26,27] [] (some 29))
      (.done history) reads ∧
    weighted (storageWeight w) ([.readRoot,.readDescriptor] ++ reads) = checkpointRecovery w 10 8 := by
  obtain ⟨reads,run,cost⟩ := recovery_reads (storageWeight w)
  refine ⟨reads,run,?_⟩
  rw [weighted_append,cost]
  simp [weighted,storageWeight,checkpointRecovery]
  ring

theorem partial_copy_cost (w : StorageEvent → Nat) :
    weighted w (persistenceEvents (cells.take 2)) = 2*(w .write+w .persist) :=
  persistence_count w (cells.take 2)

theorem interrupted_read : ReadTrace oldDisk (.tailCells (some 9) [] [])
    (.tailCells (some 8) [] [record 9]) [.readRecord,.followLink] := .node rfl .nil

theorem repeated_interrupted_read_cost (attempts : Nat) :
    weighted (fun _ => 1) (List.replicate attempts [.readRecord,.followLink]).flatten = 2*attempts := by
  rw [interrupted_work]
  simp [weighted]
  omega

theorem no_completed_count_bound (bound : Nat) : ∃ attempts,
    bound < weighted (fun _ => 1) (List.replicate attempts [.readRecord,.followLink]).flatten := by
  refine ⟨bound+1,?_⟩
  rw [repeated_interrupted_read_cost]
  omega

end Examples.DiagnosticStorage
