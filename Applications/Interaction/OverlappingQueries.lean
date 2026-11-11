import Mathlib.Data.List.Basic

/-! Independent operational specification for a client with two outstanding
Boolean requests. This module does not import a strategy representation. -/
namespace Interaction.OverlappingQueries

inductive Status where
  | idle | pending | answered (value : Bool)
  deriving DecidableEq, Repr
inductive Move where
  | ask (slot : Bool) | reply (slot value : Bool)
  deriving DecidableEq, Repr
abbrev State := Bool → Status

def initial : State := fun _ => .idle

def update (s : State) (i : Bool) (v : Status) : State := fun j => if j = i then v else s j

def step (s : State) : Move → Option State
  | .ask i => match s i with
    | .pending => none
    | _ => some (update s i .pending)
  | .reply i b => match s i with
    | .pending => some (update s i (.answered b))
    | _ => none

def execute : State → List Move → Option State
  | s, [] => some s
  | s, m :: ms => (step s m).bind (fun t => execute t ms)

def Legal (xs : List Move) : Prop := ∃ s, execute initial xs = some s

structure Observation where
  result : Option Bool
  left : Status
  right : Status
  history : List Move
  deriving DecidableEq, Repr

def observe (s : State) (xs : List Move) : Observation where
  result := match s false, s true with
    | .answered a, .answered b => some (a && b)
    | _, _ => none
  left := s false
  right := s true
  history := xs

def requests : List Move := [.ask false, .ask true]
def trace (schedule : List (Bool × Bool)) : List Move :=
  requests ++ schedule.map (fun (i,b) => .reply i b)

/-- `none` rejects an illegal schedule; `some` may still contain a pending result. -/
def native (schedule : List (Bool × Bool)) : Option Observation :=
  (execute initial (trace schedule)).map (fun s => observe s (trace schedule))

theorem both_pending : native [] = some ⟨none, .pending, .pending, requests⟩ := rfl
theorem right_only : native [(true,true)] =
    some ⟨none, .pending, .answered true, requests ++ [.reply true true]⟩ := rfl
theorem right_first : native [(true,true),(false,false)] =
    some ⟨some false, .answered false, .answered true,
      requests ++ [.reply true true, .reply false false]⟩ := rfl
theorem left_first : native [(false,false),(true,true)] =
    some ⟨some false, .answered false, .answered true,
      requests ++ [.reply false false, .reply true true]⟩ := rfl

theorem equal_results :
    (native [(true,true),(false,false)]).map Observation.result =
      (native [(false,false),(true,true)]).map Observation.result := rfl

theorem different_interactions : native [(true,true),(false,false)] ≠
    native [(false,false),(true,true)] := by decide

theorem duplicate_reply_rejected : native [(true,true),(true,false)] = none := rfl
theorem unmatched_reply_rejected : execute initial [.reply false true] = none := rfl
theorem pending_reissue_rejected : execute initial [.ask false,.ask false] = none := rfl

theorem native_legal (h : native schedule = some out) : Legal (trace schedule) := by
  unfold native at h
  cases hs : execute initial (trace schedule) with
  | none => simp [hs] at h
  | some s => exact ⟨s, hs⟩

end Interaction.OverlappingQueries
