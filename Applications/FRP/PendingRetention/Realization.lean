import Applications.FRP.PendingRetention.Safety

/-! Native backend ownership agrees with the selected durable frame. Evaluation
uses the frame transition; migration installs the actual prepared backend. -/
set_option autoImplicit false
namespace FRPSpec.PendingRetention
open PendingCrash

/-- Canonical native realization owned by the awake endpoint. Prepared state
belongs to the single migration cause until its selector publication. -/
structure Realized (s : System) : Prop where
  active : s.active = if s.localDown then none else some (reconstruct s.localBank.selected.frame)
  prepared : s.prepared = match s.localCause with
    | some (.frame (.migrate kind)) => some (Migration.realize kind s.localBank.selected.frame.logical)
    | _ => none
  former : ∀ backend ∈ s.former, backend.logical = s.localBank.selected.frame.logical
  former_idle : s.former.isSome = true →
    s.localCause = none ∧ s.peerCause = none ∧ s.retirementScan = none

theorem realized_initial : Realized initial := by
  constructor
  · rfl
  · rfl
  · intro b impossible; cases impossible
  · simp [initial]

theorem realized_active {s : System} (realized : Realized s) (awake : s.localDown = false) :
    ∃ backend, s.active = some backend ∧ backend.kind = s.localBank.selected.frame.kind ∧
      backend.logical = s.localBank.selected.frame.logical := by
  refine ⟨reconstruct s.localBank.selected.frame,?_,?_,?_⟩
  · simpa only [awake,Bool.false_eq_true,ite_false] using realized.active
  · exact Migration.realize_kind _ _
  · exact Migration.realize_logical _ _

theorem localChange_migrate_frame {cfg : Config} {before after : LocalSnapshot}
    {kind : Migration.Kind} (changed : localChange cfg before (.migrate kind) = .ok after) :
    after.frame = {before.frame with kind := kind} := by
  have proposed := localChange_proposed changed
  exact (Decision.changed.inj proposed).symm

theorem Realized.congr {s t : System} (realized : Realized s)
    (selected : t.localBank.selected = s.localBank.selected)
    (down : t.localDown = s.localDown) (active : t.active = s.active)
    (prepared : t.prepared = s.prepared) (former : t.former = s.former)
    (localCause : t.localCause = s.localCause) (peerCause : t.peerCause = s.peerCause)
    (scan : t.retirementScan = s.retirementScan) : Realized t := by
  constructor
  · simpa only [selected,down,active] using realized.active
  · simpa only [selected,localCause,prepared] using realized.prepared
  · simpa only [selected,former] using realized.former
  · simpa only [former,localCause,peerCause,scan] using realized.former_idle

theorem realized_iff (s : System) : Realized s ↔
    (s.active = if s.localDown then none else some (reconstruct s.localBank.selected.frame)) ∧
    (s.prepared = match s.localCause with
      | some (.frame (.migrate k)) => some (Migration.realize k s.localBank.selected.frame.logical)
      | _ => none) ∧
    (∀ backend ∈ s.former, backend.logical = s.localBank.selected.frame.logical) ∧
    (s.former.isSome = true → s.localCause = none ∧ s.peerCause = none ∧ s.retirementScan = none) :=
  ⟨fun h => ⟨h.active,h.prepared,h.former,h.former_idle⟩,
   fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩⟩

set_option maxHeartbeats 400000 in
theorem realized_localStep {cfg : Config} {s : System}
    (realized : Realized s) (command : LocalCommand) : Realized (localStep cfg s command).system := by
  rcases realized with ⟨active,prepared,former,formerIdle⟩
  cases command <;> simp only [localStep,beginLocal,reject,LocalCommand.frameCommand] at *
  all_goals repeat' first
    | simp_all [realized_iff,controllerIdle,reconstruct]
    | split

theorem realized_duplicate {cfg : Config} {s : System}
    (realized : Realized s) (queue : Queue) (index : Nat) :
    Realized (duplicateQueue cfg s queue index).system := by
  cases queue <;> simp only [duplicateQueue]
  all_goals split
  all_goals first
    | exact realized
    | (rename_i t eq
       obtain ⟨items,_,rfl⟩ := Option.map_eq_some_iff.mp eq
       exact realized.congr rfl rfl rfl rfl rfl rfl rfl rfl)

set_option maxHeartbeats 1000000 in
theorem realized_nonprogress {cfg : Config} {s : System}
    (realized : Realized s) (command : Command) (ordinary : command ≠ .progress) :
    Realized (step cfg s command).system := by
  cases command
  case «local» c => exact realized_localStep realized c
  case duplicate q i => exact realized_duplicate realized q i
  all_goals rcases realized with ⟨active,prepared,former,formerIdle⟩
  all_goals
    simp only [step,startRetirement,requestStep,replyStep,beginLocal,beginPeer,
      pushRequest,pushReply,reject] at *
  all_goals repeat' first
    | contradiction
    | simp_all [realized_iff,controllerIdle,reconstruct]
    | split

theorem Realized.former_none_of_local {s : System} (realized : Realized s)
    {cause : LocalCause} (pending : s.localCause = some cause) : s.former = none := by
  cases former : s.former with
  | none => rfl
  | some backend =>
    have impossible := (realized.former_idle (by simp [former])).1
    simp [pending] at impossible

theorem Realized.localPublished {cfg : Config} {s : System} (realized : Realized s)
    (owners : Serialized s) (bank : LocalBanks) (cause : LocalCause)
    (pending : s.localCause = some cause) (awake : s.localDown = false)
    (edit : LocalEdit cfg s.localBank.selected bank.selected cause) :
    Realized (FRPSpec.PendingRetention.localPublished {s with localBank := bank} cause).system := by
  have formerNone := realized.former_none_of_local pending
  have peerNone : s.peerCause = none := owners.1.resolve_left (by simp [pending])
  have scanNone : s.retirementScan = none := owners.2.1.resolve_left (by simp [pending])
  have active := realized.active
  have prepared := realized.prepared
  cases cause with
  | frame command =>
    cases command with
    | migrate kind =>
      have changed := localChange_migrate_frame edit.frame_changed
      constructor <;> simp_all [FRPSpec.PendingRetention.localPublished,reconstruct]
    | _ => constructor <;> simp [FRPSpec.PendingRetention.localPublished,awake,formerNone]
  | relinquish => constructor <;> simp [FRPSpec.PendingRetention.localPublished,awake,formerNone]
  | finish => constructor <;> simp [FRPSpec.PendingRetention.localPublished,awake,formerNone]

theorem Realized.peerPublished {cfg : Config} {s : System} (realized : Realized s)
    (cause : PeerCause) : Realized (FRPSpec.PendingRetention.peerPublished cfg s cause).system := by
  rcases realized with ⟨active,prepared,former,formerIdle⟩
  cases cause <;> simp only [FRPSpec.PendingRetention.peerPublished, pushReply]
  all_goals repeat' first
    | assumption
    | apply Realized.mk
    | simp_all
    | intro introduced
    | split

theorem Realized.scan {s : System} (realized : Realized s) (owners : Serialized s)
    (target cursor : Nat) (scan : s.retirementScan = some (target,cursor)) :
    Realized (scanRetirement s target cursor).system := by
  have localNone : s.localCause = none := owners.2.1.resolve_right (by simp [scan])
  have formerNone : s.former = none := by
    cases former : s.former with
    | none => rfl
    | some backend =>
      have impossible := (realized.former_idle (by simp [former])).2.2
      simp [scan] at impossible
  have preparedNone : s.prepared = none := by simpa [localNone] using realized.prepared
  unfold scanRetirement
  repeat' first
    | apply Realized.mk
    | simp_all [beginLocal,reject,realized.active,realized.prepared]
    | intro introduced
    | split

set_option maxHeartbeats 800000 in
theorem realized_progress {cfg : Config} {s : System}
    (realized : Realized s) (staged : Staging cfg s) (owners : Serialized s) :
    Realized (progress cfg s).system := by
  unfold progress
  split
  · exact realized
  · cases scan : s.retirementScan with
    | some pair =>
      rcases pair with ⟨target,cursor⟩
      dsimp only
      split
      · exact realized
      · exact realized.scan owners target cursor scan
    | none =>
      dsimp only
      cases localCause : s.localCause with
      | some cause =>
        dsimp only
        split
        · exact realized
        · split
          · rename_i published
            simpa only [scan,localCause] using realized.localPublished owners _ cause localCause
              (by simpa using (show s.localDown ≠ true by assumption))
              ((localCause ▸ staged.1).publication published)
          · rename_i silent
            simpa only [scan,localCause] using realized.congr
              (t := {s with localBank := s.localBank.progress.1})
              (s.localBank.progress_stutters (Bool.eq_false_iff.mpr silent))
              rfl rfl rfl rfl rfl rfl rfl
      | none =>
        dsimp only
        cases peerCause : s.peerCause with
        | none => exact realized
        | some cause =>
          dsimp only
          split
          · exact realized
          · split
            · have next : Realized {s with peer := s.peer.progress.1} :=
                realized.congr rfl rfl rfl rfl rfl rfl rfl rfl
              simpa only [scan,localCause,peerCause] using next.peerPublished (cfg := cfg) cause
            · simpa only [scan,localCause,peerCause] using realized.congr
                (t := {s with peer := s.peer.progress.1}) rfl rfl rfl rfl rfl rfl rfl rfl

theorem realized_step {cfg : Config} {s : System}
    (realized : Realized s) (staged : Staging cfg s) (owners : Serialized s) (command : Command) :
    Realized (step cfg s command).system := by
  by_cases advancing : command = .progress
  · subst command; exact realized_progress realized staged owners
  · exact realized_nonprogress realized command advancing

/-- Actual prepared and active backend ownership survives arbitrary copy cuts,
crashes, recovery, and cleanup in the same bounded controller. -/
theorem realized_reachable {cfg : Config} {s : System} (reachable : Reachable cfg s) : Realized s := by
  induction reachable with
  | initial => exact realized_initial
  | next reached command ih =>
    exact realized_step ih (staging_reachable reached) (serialized_reachable reached) command

theorem initial_execution_realized (cfg : Config) (commands : List Command) :
    Realized (execute cfg initial commands).system :=
  realized_reachable (execute_reachable cfg initial commands .initial)

private def migrationCommands : List Command :=
  [.local (.migrate .redundant true true)] ++ List.replicate 4 .progress

/-- A successful migration installs the prepared representation and retains
its former owner until explicit cleanup. -/
example :
    let state := (execute ⟨1,1,1⟩ initial migrationCommands).system
    state.active.map Migration.Backend.kind = some .redundant ∧
      state.former.map Migration.Backend.kind = some .delay := by decide

example : Realized (execute ⟨1,1,1⟩ initial migrationCommands).system :=
  initial_execution_realized _ _

example :
    (execute ⟨1,1,1⟩ initial (migrationCommands ++ [.cleanup])).system.former.isNone = true := by decide

end FRPSpec.PendingRetention
