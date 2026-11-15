import SquareKit.OwnedHandleBackend
import SquareKit.OwnedHandleSeparation

namespace Examples.OwnedHandle
open SquareKit.OwnedHandle SquareKit.AdjointModes

def initial : State :=
  ⟨fun h => if h then some ⟨2,99,true⟩ else some ⟨0,37,true⟩, [], false⟩

def client : List Command := [.transfer false 0 1, .consume false 1, .consume true 2]
def final : State :=
  ⟨fun h => if h then some ⟨2,99,false⟩ else some ⟨1,37,false⟩, [37,99], false⟩

theorem client_run : run client initial = some final := by
  simp [run, step, client, initial, replace, final]
  funext h
  cases h <;> rfl

theorem client_spec : Runs client initial final := (run_spec _ _ _).mp client_run

theorem client_finished : Finished final := by
  constructor
  · rfl
  · intro h; cases h <;> rfl

/-- The selected return sequence follows through the generic mode compiler. -/
theorem client_selected : (((program client).compile atoms meanings).run initial).returned = [37,99] := by
  rw [compiled_protocol client_spec]
  rfl

def swapped : Bool ≃ Bool := ⟨Bool.not, Bool.not, by intro b; cases b <;> rfl,
  by intro b; cases b <;> rfl⟩

theorem changed_backend :
    ((program (client.map (lower swapped))).compile atoms meanings).run (encode swapped initial) =
      encode swapped final := two_stage client_spec swapped

theorem changed_selected :
    (((program (client.map (lower swapped))).compile atoms meanings).run (encode swapped initial)).returned =
      [37,99] := by rw [changed_backend]; rfl

theorem changed_live_absent (h : Bool) :
    liveHeap (((program (client.map (lower swapped))).compile atoms meanings).run
      (encode swapped initial)) (swapped h) = none := by
  rw [changed_backend, encode_live]
  exact client_finished.2 h

theorem double_use_rejected :
    run [.consume false 0, .consume false 0] initial = none := rfl

theorem stale_owner_rejected :
    run [.transfer false 0 1, .consume false 0] initial = none := rfl

theorem invalid_discard : ¬ Finished initial := by
  intro h
  have hf := h.2 false
  contradiction

/-- Two independent ownership assertions cannot claim the same slot. -/
theorem duplicate_permission_rejected (heap : Heap) :
    ¬ Sep (pointsTo false 0 37) (pointsTo false 0 37) heap :=
  no_separating_alias false 0 0 37 37 heap

/-- The other slot's selected contents survive transfer of the first. -/
theorem native_frame :
    liveHeap (replace initial false ⟨1,37,true⟩) true = some (2,99) := by
  have ha : Acts (.transfer false 0 1) initial (replace initial false ⟨1,37,true⟩) :=
    .transfer initial false 0 1 ⟨0,37,true⟩ rfl rfl rfl rfl
  exact frame_live ha true (by change true ≠ false; decide)

/-- Grade preservation alone permits resurrection, which violates the protocol. -/
def resurrect (s : State) : State :=
  {s with slots := fun h => (s.slots h).map (fun c => {c with live := true})}

theorem resurrect_weight (c : Option Cell) :
    weight (c.map (fun c => {c with live := true})) = weight c := by cases c <;> rfl

def badGradeMap : Map ledger ledger :=
  ⟨resurrect, fun s => congrArg₂ (· + ·) (resurrect_weight (s.slots false))
    (resurrect_weight (s.slots true))⟩

theorem resurrection_observable : liveHeap (badGradeMap.run final) false = some (1,37) := rfl

theorem resurrection_not_finished : ¬ Finished (badGradeMap.run final) := by
  intro h
  have hh := h.2 false
  rw [resurrection_observable] at hh
  contradiction

/-- Generic structural discard still cannot erase this nonzero ledger. -/
theorem ledger_no_discard : ¬ Nonempty (Map ledger one) := by
  rintro ⟨f⟩
  have h := f.preserves initial
  change 0 = 2 at h
  contradiction

/-- Actual transposition on command data retains its literal through both shifts. -/
theorem command_roundtrip :
    ((commandShift (.consume false 1)).transpose.untranspose).compile atoms meanings =
      (commandShift (.consume false 1)).compile atoms meanings :=
  commandShift_roundtrip _

/-- The concrete initial heap admits two disjoint ownership assertions. -/
theorem initial_separated : Sep (pointsTo false 0 37) (pointsTo true 2 99) (liveHeap initial) := by
  refine ⟨singleton false 0 37, singleton true 2 99, ?_, ?_, rfl, rfl⟩
  · intro h; cases h <;> simp [SquareKit.OwnedHandle.singleton]
  · funext h; cases h <;> rfl

theorem changed_double_use_rejected :
    run (([.consume false 0, .consume false 0] : List Command).map (lower swapped))
      (encode swapped initial) = none := rfl

/-- The actual duplication function fails the resource-map contract. -/
theorem ledger_duplication_fails :
    ¬ ∀ s, (tensor ledger ledger).degree (s,s) = ledger.degree s := by
  intro h
  have hh := h initial
  change 2 + 2 = 2 at hh
  contradiction

/-- Mode typing permits sequential commands, so protocol rejection is separate. -/
theorem double_use_mode_failed :
    (((program [.consume false 0, .consume false 0]).compile atoms meanings).run initial).failed = true := by
  rw [program_compile]
  rfl

end Examples.OwnedHandle
