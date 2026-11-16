import Applications.FRP.PendingRetention.Safety

/-! The executor's emitted effects are exactly the lifetime peer's effects.
The lifetime command list is proof evidence and occupies no runtime storage. -/
set_option autoImplicit false
namespace FRPSpec.PendingRetention
open PendingCrash

def labelEffect : SourceLabel → Option (Nat × Bool)
  | .output identity value => some (identity,value)
  | _ => none

def emittedEffects (labels : List SourceLabel) : List (Nat × Bool) :=
  labels.filterMap labelEffect

theorem PeerEdit.effect {cfg : Config} {before after : PeerSnapshot} {history : Peer}
    {identity : Nat} {command : PeerCommand} {reply : ReplyPacket} {effect prevented : Option Bool}
    (edit : PeerEdit cfg before after (.business identity command reply effect prevented))
    (extension : PeerExtension before.floor before.entries history) :
    effect = (peerStep history identity command).effect := by
  have above := edit.business_above
  cases edit with
  | business changed different =>
    rcases peerDecision_cases changed with expired | performed
    · omega
    · exact performed.2.2.2.1.trans (extension.effect _ _ above)

theorem localPublished_no_effect (s : System) (cause : LocalCause) :
    labelEffect (localPublished s cause).label = none := by
  cases cause with
  | frame c => cases c <;> rfl
  | relinquish => rfl
  | finish => rfl

theorem peerPublished_effect (cfg : Config) (s : System) (cause : PeerCause) :
    labelEffect (peerPublished cfg s cause).label =
      match cause with
      | .business i _ _ effect _ => effect.map (fun y => (i,y))
      | _ => none := by
  cases cause with
  | business i c r e p => cases e <;> cases p <;> rfl
  | floor => rfl
  | deletion => simp only [peerPublished]; unfold pushReply; split <;> rfl

theorem scanRetirement_no_effect (s : System) (target cursor : Nat) :
    labelEffect (scanRetirement s target cursor).label = none := by
  unfold scanRetirement
  repeat' first | rfl | dsimp only | split

set_option maxHeartbeats 800000 in
theorem progress_effect {cfg : Config} {s : System} {history : Peer}
    (safe : Safe cfg s history) :
    (labelEffect (progress cfg s).label).toList =
      (peerExecute history (peerAction s .progress).toList).effects := by
  unfold progress
  split
  · rename_i down
    have peerDown := (Bool.and_eq_true_iff.mp down).2
    simp [peerAction,peerDown,reject,labelEffect,peerExecute]
  · cases scan : s.retirementScan with
    | some pair =>
      rcases pair with ⟨target,cursor⟩
      simp only [peerAction,scan,Option.isSome_some,Bool.or_true,ite_true,Option.toList_none,peerExecute]
      split
      · rfl
      · rw [scanRetirement_no_effect]; rfl
    | none =>
      dsimp only
      cases localCause : s.localCause with
      | some cause =>
        simp only [peerAction,localCause,Option.isSome_some,Bool.or_true]
        split
        · rfl
        · split
          · rw [localPublished_no_effect]; rfl
          · rfl
      | none =>
        dsimp only
        cases peerCause : s.peerCause with
        | none => simp [peerAction,scan,localCause,peerCause,labelEffect,peerExecute]
        | some cause =>
          dsimp only
          split
          · rename_i down
            simp [peerAction,down,reject,labelEffect,peerExecute]
          · rename_i awake
            split
            · rename_i published
              have edit := (peerCause ▸ safe.staging.2).publication published
              rw [peerPublished_effect]
              cases cause with
              | business i c r e p =>
                rw [edit.effect safe.semantic.relation.extension]
                simp [peerAction,scan,localCause,peerCause,awake,published,peerExecute,
                  Option.toList_map]
              | floor t => simp [peerAction,scan,localCause,peerCause,awake,peerExecute]
              | deletion t => simp [peerAction,scan,localCause,peerCause,awake,peerExecute]
            · rename_i silent
              cases cause <;> simp [peerAction,scan,localCause,peerCause,awake,silent,labelEffect,peerExecute]

theorem step_effect {cfg : Config} {s : System} {history : Peer}
    (safe : Safe cfg s history) (command : Command) :
    (labelEffect (step cfg s command).label).toList =
      (peerExecute history (peerAction s command).toList).effects := by
  by_cases advancing : command = .progress
  · subst command; exact progress_effect safe
  · rw [(step_nonprogress_selected cfg s command advancing).2.2]
    cases command <;> simp_all [labelEffect,peerAction,peerExecute]

theorem emittedEffects_cons (label : SourceLabel) (labels : List SourceLabel) :
    emittedEffects (label :: labels) = (labelEffect label).toList ++ emittedEffects labels := by
  simp only [emittedEffects,List.filterMap_cons]
  cases labelEffect label <;> rfl

/-- Queue retries, loss, crashes, and reclamation do not add effects beyond the
same atomic peer execution used by the established at-most-once theorem. -/
theorem Safe.effects {cfg : Config} {s : System} {history : Peer}
    (safe : Safe cfg s history) (commands : List Command) :
    emittedEffects (FRPSpec.PendingRetention.execute cfg s commands).labels =
      (peerExecute history (peerActions cfg s commands)).effects := by
  induction commands generalizing s history with
  | nil => rfl
  | cons command commands ih =>
    have tail := ih (safe.step command)
    have head := step_effect safe command
    simp only [FRPSpec.PendingRetention.execute,emittedEffects_cons]
    rw [head,tail]
    cases action : peerAction s command with
    | none => simp [peerActions,historyAfter,action,peerExecute]
    | some pair =>
      rcases pair with ⟨identity,operation⟩
      simp [peerActions,historyAfter,action,peerExecute]

/-- No lifetime identity is externally executed twice by the actual bounded
controller, including commands replayed after deletion or independent crashes. -/
theorem initial_effects_unique (cfg : Config) (commands : List Command) :
    ((emittedEffects (FRPSpec.PendingRetention.execute cfg initial commands).labels).map Prod.fst).Nodup := by
  rw [(Safe.initial cfg).effects commands]
  exact peer_effects_unique _ _

end FRPSpec.PendingRetention
