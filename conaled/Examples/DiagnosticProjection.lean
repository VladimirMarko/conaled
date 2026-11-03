import Applications.Durability.DiagnosticRelational
import Applications.Interaction.Snapshot

namespace Examples.DiagnosticProjection
open Durability Durability.Diagnostic Interaction.Events

def ab : Record (Edge 2) := ⟨1,0,(0,1)⟩
def abAgain : Record (Edge 2) := ⟨1,1,(0,1)⟩
def ba : Record (Edge 2) := ⟨1,2,(1,0)⟩
def conflict : Record (Edge 2) := ⟨1,0,(1,0)⟩

example : allows [] ab = true := by decide
example : allows [ab] abAgain = true := by decide
example : allows [ab] ba = false := by decide
example : allows [] ba = true := by decide
example : (recompute [ab]).count = (recompute [ba]).count ∧
    (0,1) ∈ (recompute [ab]).paths ∧ (0,1) ∉ (recompute [ba]).paths := by decide
example : (recompute [ab,abAgain]).paths = (recompute [ab]).paths ∧
    (recompute [ab,abAgain]).count ≠ (recompute [ab]).count := by decide

/-- Replaying one already accepted record would leave set reachability
unchanged but incorrectly increase the accepted-record count. -/
example : (recompute [ab,ab]).paths = (recompute [ab]).paths ∧
    (recompute [ab,ab]).count = 2 ∧ (recompute [ab]).count = 1 := by decide

def abc : History 3 := [⟨4,0,(0,1)⟩,⟨4,1,(1,2)⟩]
theorem two_edge_path : (0,2) ∈ (recompute abc).paths := by
  apply (closure_correct abc 0 2).mpr
  exact (Relation.TransGen.single (by decide : Edges abc 0 1)).tail (by decide)

def appendEvents (e : Record (Edge 2)) : List (Event (Edge 2)) :=
  [.invoke e,.internal,.internal,.internal,.commit e,.acknowledge e]
def onePlan := appendPlan (fun _ => none) emptyRoot [] (empty_rep _) 0 ab rfl
abbrev accepted : Machine (Edge 2) := acknowledgeState (publishState
  (writePersist (prepareState (invokeState initial ab) onePlan) (0,.node none ab)) onePlan)

theorem one_execution : interpret Step (appendEvents ab) initial accepted :=
  append_execution initial [] rfl rfl rfl (empty_rep _) 0 ab rfl
    (by simp [initial]) (by simp [Fresh])
theorem accepted_rep : Represents accepted.disk accepted.root [ab] :=
  append_rep (empty_rep _) 0 ab rfl

def cp := checkpointPlan accepted.disk [ab] 10
def cpCells : List (Nat × Cell (Edge 2)) := [(10,.flat ab),(11,.index [10])]
abbrev checkpointed := publishState (persistCells (prepareState accepted cp) cpCells) cp

theorem cp_enumerates (i : Nat) (c : Cell (Edge 2)) :
    cp.writes i = some c ↔ (i,c) ∈ cpCells := by
  by_cases h10 : i = 10
  · subst i; simp [cp,checkpointPlan,checkpointWrites,copy,addresses,put,cpCells,eq_comm]
  by_cases h11 : i = 11
  · subst i; simp [cp,checkpointPlan,checkpointWrites,copy,addresses,put,cpCells,eq_comm]
  simp [cp,checkpointPlan,checkpointWrites,copy,addresses,put,cpCells,h10,h11]

def cpEvents : List (Event (Edge 2)) := .internal :: List.replicate 4 .internal ++ [.internal]
theorem checkpoint_execution : interpret Step cpEvents accepted checkpointed := by
  apply replacement_execution accepted [ab] cp rfl rfl rfl rfl rfl rfl cpCells cp_enumerates
  · intro x hx
    simp only [cpCells,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> simp [writePersist,initial,onePlan,appendPlan,put]
  · intro x hx
    simp only [cpCells,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> rfl

theorem checkpointed_rep : Represents checkpointed.disk checkpointed.root [ab] := by
  exact ⟨[ab],[],.block (as := [10]) rfl (.cons rfl .nil),.nil,rfl⟩

theorem all_checkpoint_execution :
    interpret Step (appendEvents ab ++ cpEvents) initial checkpointed := by
  rw [interpret_append]
  exact ⟨accepted,one_execution,checkpoint_execution⟩

def twoPlan (s : Machine (Edge 2)) (rep : Represents s.disk s.root [ab])
    (space : s.disk 20 = none) := appendPlan s.disk s.root [ab] rep 20 abAgain space
abbrev afterTwo (s : Machine (Edge 2)) (rep : Represents s.disk s.root [ab])
    (space : s.disk 20 = none) := acknowledgeState (publishState
  (writePersist (prepareState (invokeState s abAgain) (twoPlan s rep space))
    (20,.node s.root.tail abAgain)) (twoPlan s rep space))

theorem append_again (s : Machine (Edge 2)) (rep : Represents s.disk s.root [ab])
    (ready : s.cache = some [ab]) (idle : s.active = none) (noplan : s.pending = none)
    (space : s.disk 20 = none) (unused : 20 ∉ s.used) :
    interpret Step (appendEvents abAgain) s (afterTwo s rep space) :=
  append_execution s [ab] ready idle noplan rep 20 abAgain space unused
    (by intro e mem; simp only [List.mem_singleton] at mem; subst e; decide)

abbrev logTwo := afterTwo accepted accepted_rep rfl
abbrev checkpointTwo := afterTwo checkpointed checkpointed_rep rfl
def logEvents := appendEvents ab ++ appendEvents abAgain
def checkpointEvents := appendEvents ab ++ cpEvents ++ appendEvents abAgain

theorem log_execution : interpret Step logEvents initial logTwo := by
  rw [logEvents,interpret_append]
  exact ⟨accepted,one_execution,append_again accepted accepted_rep rfl rfl rfl rfl
    (by simp [writePersist,initial,onePlan,appendPlan,put])⟩
theorem checkpoint_tail_execution : interpret Step checkpointEvents initial checkpointTwo := by
  rw [checkpointEvents,interpret_append]
  refine ⟨checkpointed,all_checkpoint_execution,
    append_again checkpointed checkpointed_rep rfl rfl rfl rfl ?_⟩
  simp [persistCells,cpCells,writePersist,initial,onePlan,appendPlan,put,cp,checkpointPlan,checkpointWrites,copy]

/-- One client statement for both histories and both storage boundaries. -/
theorem expected_projection (events : List (Event (Edge 2)))
    (commits : committedRecords events = [ab,abAgain]) :
    (∀ s ∈ targetBehaviors events, ∀ v, synchronous recompute s = some v →
      v = ⟨2,recompute [ab,abAgain]⟩) ∧
    (∀ s ∈ encodedBehaviors (edgeCodec 2) events, ∀ v,
      synchronous recompute (Durability.observe (edgeCodec 2) s) = some v →
      v = ⟨2,recompute [ab,abAgain]⟩) := by
  have source : ∀ a ∈ sourceBehaviors events,
      (⟨a.history.length,recompute a.history⟩ : Published (View 2)) = ⟨2,recompute [ab,abAgain]⟩ := by
    intro a run
    rw [source_history run,commits]
    rfl
  exact ⟨projection_client events recompute _ source,
    encoded_projection_client (edgeCodec 2) events recompute _ source⟩

theorem both_layout_clients :
    synchronous recompute logTwo = some ⟨2,recompute [ab,abAgain]⟩ ∧
    synchronous recompute checkpointTwo = some ⟨2,recompute [ab,abAgain]⟩ := by
  have l := (expected_projection logEvents rfl).1 logTwo log_execution
    ⟨2,recompute [ab,abAgain]⟩ rfl
  have c := (expected_projection checkpointEvents rfl).1 checkpointTwo checkpoint_tail_execution
    ⟨2,recompute [ab,abAgain]⟩ rfl
  exact ⟨congrArg some l,congrArg some c⟩

theorem both_encoded_clients :
    synchronous recompute (Durability.observe (edgeCodec 2) (encodeState (edgeCodec 2) logTwo)) =
      some ⟨2,recompute [ab,abAgain]⟩ ∧
    synchronous recompute (Durability.observe (edgeCodec 2) (encodeState (edgeCodec 2) checkpointTwo)) =
      some ⟨2,recompute [ab,abAgain]⟩ := by
  have l := (expected_projection logEvents rfl).2 (encodeState (edgeCodec 2) logTwo)
    (encode_script (edgeCodec 2) log_execution) ⟨2,recompute [ab,abAgain]⟩
    (by rw [observe_encode]; rfl)
  have c := (expected_projection checkpointEvents rfl).2 (encodeState (edgeCodec 2) checkpointTwo)
    (encode_script (edgeCodec 2) checkpoint_tail_execution) ⟨2,recompute [ab,abAgain]⟩
    (by rw [observe_encode]; rfl)
  rw [observe_encode,observe_encode]
  exact ⟨congrArg some l,congrArg some c⟩

def logRecoveryEvents : List (Event (Edge 2)) :=
  [.crash,.internal,.internal,.internal,.internal,.recover [ab,abAgain]]
theorem log_recovery : interpret Step logRecoveryEvents logTwo logTwo := by
  let crashed := crashState logTwo
  let started := {crashed with cursor := some (.tailCells (some 20) [] [])}
  let one := {started with cursor := some (.tailCells (some 0) [] [abAgain])}
  let two := {one with cursor := some (.tailCells none [] [ab,abAgain])}
  let done := {two with cursor := some (.done [ab,abAgain])}
  exact ⟨crashed,.crash,started,.startRead rfl rfl (.log rfl),
    one,.read rfl rfl (.node rfl),two,.read rfl rfl (.node rfl),
    done,.read rfl rfl .finish,logTwo,.recover rfl rfl,rfl⟩

def cpRecoveryEvents : List (Event (Edge 2)) :=
  [.crash,.internal,.internal,.internal,.internal,.internal,.recover [ab,abAgain]]
theorem cp_recovery : interpret Step cpRecoveryEvents checkpointTwo checkpointTwo := by
  let crashed := crashState checkpointTwo
  let started := {crashed with cursor := some (.prefixCells [10] [] (some 20))}
  let one := {started with cursor := some (.prefixCells [] [ab] (some 20))}
  let boundary := {one with cursor := some (.tailCells (some 20) [ab] [])}
  let two := {boundary with cursor := some (.tailCells none [ab] [abAgain])}
  let done := {two with cursor := some (.done [ab,abAgain])}
  exact ⟨crashed,.crash,started,.startRead rfl rfl (.checkpoint rfl rfl),
    one,.read rfl rfl (.flat rfl),boundary,.read rfl rfl .boundary,
    two,.read rfl rfl (.node rfl),done,.read rfl rfl .finish,checkpointTwo,.recover rfl rfl,rfl⟩

theorem recovered_layouts :
    interpret Step (logEvents ++ logRecoveryEvents) initial logTwo ∧
    interpret Step (checkpointEvents ++ cpRecoveryEvents) initial checkpointTwo := by
  constructor <;> rw [interpret_append]
  · exact ⟨logTwo,log_execution,log_recovery⟩
  · exact ⟨checkpointTwo,checkpoint_tail_execution,cp_recovery⟩

/-- The same projection theorem consumes both full crash/recovery executions,
and their primitive encoded realizations, without a layout-specific client. -/
theorem recovered_projection_clients :
    (∀ s ∈ targetBehaviors (logEvents ++ logRecoveryEvents), ∀ v,
      synchronous recompute s = some v → v = ⟨2,recompute [ab,abAgain]⟩) ∧
    (∀ s ∈ targetBehaviors (checkpointEvents ++ cpRecoveryEvents), ∀ v,
      synchronous recompute s = some v → v = ⟨2,recompute [ab,abAgain]⟩) ∧
    (∀ s ∈ encodedBehaviors (edgeCodec 2) (logEvents ++ logRecoveryEvents), ∀ v,
      synchronous recompute (Durability.observe (edgeCodec 2) s) = some v → v = ⟨2,recompute [ab,abAgain]⟩) ∧
    (∀ s ∈ encodedBehaviors (edgeCodec 2) (checkpointEvents ++ cpRecoveryEvents), ∀ v,
      synchronous recompute (Durability.observe (edgeCodec 2) s) = some v → v = ⟨2,recompute [ab,abAgain]⟩) :=
  ⟨(expected_projection _ rfl).1,(expected_projection _ rfl).1,
    (expected_projection _ rfl).2,(expected_projection _ rfl).2⟩

theorem recovered_encoded_executions :
    interpret (EncodedStep (edgeCodec 2)) (logEvents ++ logRecoveryEvents) encodedInitial
      (encodeState (edgeCodec 2) logTwo) ∧
    interpret (EncodedStep (edgeCodec 2)) (checkpointEvents ++ cpRecoveryEvents) encodedInitial
      (encodeState (edgeCodec 2) checkpointTwo) :=
  ⟨encode_script _ recovered_layouts.1,encode_script _ recovered_layouts.2⟩

theorem admitted_layouts :
    interpret AdmittedStep (logEvents ++ logRecoveryEvents) initial logTwo ∧
    interpret AdmittedStep (checkpointEvents ++ cpRecoveryEvents) initial checkpointTwo := by
  have safe : Acyclic [ab,abAgain] := (acyclic_correct _).mp (by decide)
  have logRep : Represents logTwo.disk logTwo.root [ab,abAgain] := append_rep accepted_rep 20 abAgain rfl
  have cpRep : Represents checkpointTwo.disk checkpointTwo.root [ab,abAgain] :=
    append_rep checkpointed_rep 20 abAgain rfl
  exact ⟨admit_execution _ related_initial recovered_layouts.1
      (fun h rep => (rep.unique logRep).symm ▸ safe),
    admit_execution _ related_initial recovered_layouts.2 (fun h rep => (rep.unique cpRep).symm ▸ safe)⟩

theorem durable_graph_receipt : abAgain ∈ [ab,abAgain] :=
  acknowledged_client
    (appendEvents ab ++ cpEvents ++ [.invoke abAgain,.internal,.internal,.internal,.commit abAgain])
    cpRecoveryEvents abAgain checkpointTwo
    (by simpa [targetBehaviors,checkpointEvents,appendEvents,List.append_assoc] using recovered_layouts.2) _ rfl

theorem encoded_durable_graph_receipt : abAgain ∈ [ab,abAgain] :=
  encoded_acknowledged_client (edgeCodec 2)
    (appendEvents ab ++ cpEvents ++ [.invoke abAgain,.internal,.internal,.internal,.commit abAgain])
    cpRecoveryEvents abAgain (encodeState (edgeCodec 2) checkpointTwo)
    (by simpa [encodedBehaviors,checkpointEvents,appendEvents,List.append_assoc] using recovered_encoded_executions.2) _ rfl

theorem retry_and_conflict :
    Step (.acknowledge ab) (invokeState accepted ab) accepted ∧
    Step (.reject conflict) (invokeState accepted conflict) accepted := by
  exact ⟨.acknowledge (h := [ab]) rfl rfl rfl (List.mem_singleton_self ab),
    .reject (h := [ab]) (r := ab) rfl rfl rfl (List.mem_singleton_self ab) rfl (by decide)⟩

theorem stale_admission_blocked {s t : Machine (Edge 2)}
    (ready : s.cache = some [ab]) : ¬ AdmittedStep (.commit ba) s t := by
  rintro ⟨step,h,cache,ok⟩
  have eq : h = [ab] := Option.some.inj (cache.symm.trans ready)
  subst h
  have bad : allows [ab] ba = false := by decide
  rw [bad] at ok
  cases ok

theorem cycle_rejection : AdmissionStep (.cycleRejected ba) accepted accepted :=
  .cycle (h := [ab]) rfl rfl rfl
    (by intro e mem; simp only [List.mem_singleton] at mem; subst e; decide) (by decide)

example : AdmissionStep (.protocol (.reject conflict)) (invokeState accepted conflict) accepted :=
  .protocol ⟨retry_and_conflict.2,trivial⟩

abbrev projector : Projector (Edge 2) (View 2) := ⟨accepted,none,none⟩
abbrev building := {projector with rebuilding := some ⟨[],[ab]⟩}
abbrev scanned := {building with rebuilding := some ⟨[ab],[]⟩}
abbrev published := {scanned with published := some ⟨1,recompute [ab]⟩,rebuilding := none}
abbrev interrupted : Projector (Edge 2) (View 2) := ⟨crashState accepted,none,none⟩

theorem projection_start : ProjectionStep recompute projector building := .start rfl
theorem projection_scan : ProjectionStep recompute building scanned := .scan (seen := []) (e := ab) (todo := []) rfl
theorem projection_publish : ProjectionStep recompute scanned published := .publish (h := [ab]) rfl
theorem crash_around_publication :
    ProjectionStep recompute scanned interrupted ∧
    ProjectionStep recompute published interrupted ∧ interrupted.published = none :=
  ⟨.crash,.crash,rfl⟩

theorem projector_invariant : ProjectionInv recompute projector ⟨[ab],none,true⟩ := by
  refine ⟨?_,by simp,by simp⟩
  refine ⟨accepted_rep,rfl,rfl,?_,?_,?_,?_,?_⟩ <;>
    simp [writePersist,initial]

theorem published_prefix : ∃ a, ProjectionInv recompute published a := by
  obtain ⟨a,h⟩ := projection_preserves projector_invariant projection_start
  obtain ⟨b,h⟩ := projection_preserves h projection_scan
  exact projection_preserves h projection_publish

abbrev readStarted := {interrupted with machine :=
  {interrupted.machine with cursor := some (.tailCells (some 0) [] [])}}
abbrev readOne := {readStarted with machine :=
  {readStarted.machine with cursor := some (.tailCells none [] [ab])}}
abbrev readDone := {readOne with machine :=
  {readOne.machine with cursor := some (.done [ab])}}

/-- A rebuild can lose its progress, recover its authoritative input, and
restart. Repeating this same allowed cycle has no bounded completion claim. -/
theorem rebuild_interruption_cycle :
    Relation.ReflTransGen (ProjectionStep recompute) projector projector := by
  apply Relation.ReflTransGen.head projection_start
  apply Relation.ReflTransGen.head projection_scan
  apply Relation.ReflTransGen.head (show ProjectionStep recompute scanned interrupted from .crash)
  apply Relation.ReflTransGen.head (show ProjectionStep recompute interrupted readStarted from
    .storage (.startRead rfl rfl (.log rfl)) (by decide))
  apply Relation.ReflTransGen.head (show ProjectionStep recompute readStarted readOne from
    .storage (.read rfl rfl (.node rfl)) (by decide))
  apply Relation.ReflTransGen.head (show ProjectionStep recompute readOne readDone from
    .storage (.read rfl rfl .finish) (by decide))
  exact Relation.ReflTransGen.single
    (ProjectionStep.storage (show Step (.recover [ab]) readDone.machine accepted from .recover rfl rfl)
      (by decide))

example : Relation.ReflTransGen (ProjectionStep recompute) projector projector :=
  rebuild_interruption_cycle.trans rebuild_interruption_cycle

theorem stale_but_labeled : Agrees recompute [ab] ⟨0,recompute ([] : History 2)⟩ ∧
    synchronous recompute accepted = some ⟨1,recompute [ab]⟩ := by
  exact ⟨⟨[],⟨[ab],rfl⟩,rfl,rfl⟩,rfl⟩

theorem synchronous_after_ack :
    (synchronous recompute accepted).map Published.position = some 1 := by
  obtain ⟨a,run,rel⟩ := script_simulation _ related_initial one_execution
  have hist : a.history = [ab] := by rw [source_history run]; rfl
  rw [synchronous_correct rel (show accepted.cache = some [ab] from rfl),hist]
  rfl

example : edgeDecode 2 [2,1,0,2,0] = none := by decide
example : RelationalEdges [ab,abAgain] 0 1 := (relational_edges _ _ _).mpr (by decide)
example : List.ofFn (orderedRows [ab,abAgain]) = [ab,abAgain] := ordered_rows _

/-- A graph/metadata pair read at different times can fail to be any snapshot. -/
example :
    (∃ s ∈ Interaction.Snapshot.history, s.1 = Interaction.Snapshot.mixed.1) ∧
    (∃ s ∈ Interaction.Snapshot.history, s.2 = Interaction.Snapshot.mixed.2) ∧
    Interaction.Snapshot.mixed ∉ Interaction.Snapshot.history :=
  ⟨Interaction.Snapshot.individually_observed.1,
    Interaction.Snapshot.individually_observed.2,Interaction.Snapshot.never_coexisted⟩

def graphSnapshots : List (History 2 × Bool) := [([],false),([ab],false),([ab],true)]
def mixedGraph : History 2 × Bool := ([],true)
theorem mixed_graph_snapshot :
    (∃ s ∈ graphSnapshots, s.1 = mixedGraph.1) ∧
    (∃ s ∈ graphSnapshots, s.2 = mixedGraph.2) ∧ mixedGraph ∉ graphSnapshots := by
  exact ⟨⟨([],false),by simp [graphSnapshots],rfl⟩,
    ⟨([ab],true),by simp [graphSnapshots],rfl⟩,by decide⟩

end Examples.DiagnosticProjection
