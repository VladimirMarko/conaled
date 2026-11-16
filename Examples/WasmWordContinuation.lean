import Applications.Wasm.WordContinuation

/-! Noninitial, asymmetric continuation cases use the public transport laws. -/
namespace Examples.WasmWordContinuation
open Applications.Wasm Applications.Wasm.WordContinuation Applications.Circuits
open Progress Progress.Feedback

def processed : List Word := [1,0xaaaaaaaa]
def suffix : List Word := [0xffffffff,0x55555555,7]

theorem source_prefix : run source.mealy source.initial processed =
    ([0,0xbcdf0122],(0xaaaaaaaa,1)) := by decide

theorem source_suffix : run source.mealy (0xaaaaaaaa,1) suffix =
    ([0,0xffffffff,6],(7,0x55555555)) := by decide

/-- Compiled Boolean execution reaches the independent noninitial state. -/
theorem boolean_prefix :
    (run booleanMachine.mealy booleanMachine.initial processed).1 = [0,0xbcdf0122] ∧
    packState (run booleanMachine.mealy booleanMachine.initial processed).2 = (0xaaaaaaaa,1) := by
  have h := finite_suffix booleanMachine.initial processed
  rw [initial_recovers,source_prefix] at h
  exact h

/-- Actual transfer after the processed prefix preserves every suffix, not just the fixture. -/
theorem live_suffix (xs : List Word) :
    (run booleanMachine.mealy (run booleanMachine.mealy booleanMachine.initial processed).2 xs).1 =
      (run source.mealy (0xaaaaaaaa,1) xs).1 ∧
    packState (run booleanMachine.mealy (run booleanMachine.mealy booleanMachine.initial processed).2 xs).2 =
      (run source.mealy (0xaaaaaaaa,1) xs).2 := by
  have h := finite_suffix (run booleanMachine.mealy booleanMachine.initial processed).2 xs
  rw [boolean_prefix.2] at h
  exact h

example : (run booleanMachine.mealy (run booleanMachine.mealy booleanMachine.initial processed).2 suffix).1 =
    [0,0xffffffff,6] := by
  have h := (live_suffix suffix).1
  rw [source_suffix] at h
  exact h

example : packState (run booleanMachine.mealy
    (run booleanMachine.mealy booleanMachine.initial processed).2 []).2 = (0xaaaaaaaa,1) :=
  (live_suffix []).2

example (pre xs : List Word) :
    run source.mealy (packState (unpackState (run source.mealy source.initial pre).2)) xs =
      run source.mealy (run source.mealy source.initial pre).2 xs := reverse_round_trip _ _ _

example (pre xs : List Word) :
    run booleanMachine.mealy (unpackState (packState (run booleanMachine.mealy booleanMachine.initial pre).2)) xs =
      run booleanMachine.mealy (run booleanMachine.mealy booleanMachine.initial pre).2 xs := round_trip _ _ _

/-- Resetting or swapping the live registers changes the immediate future. -/
theorem reset_changes_future :
    (run source.mealy (0xaaaaaaaa,1) [0xffffffff]).1 = [0] ∧
    (run source.mealy source.initial [0xffffffff]).1 = [0xfffffffe] ∧
    (run source.mealy (1,0xaaaaaaaa) [0xffffffff]).1 = [0xaaaaaaa9] := by decide

example : decodeState .packed [.i32 1] = none := rfl
example : decodeState .packed [.i32 1,.i64 2] = none := rfl
example : decodeState .packed [.i32 1,.i32 2,.i32 3] = none := rfl
example : decodeState .boolean (.i32 2 :: List.replicate 63 (.i32 0)) = none := by decide
example : decodeState .boolean (List.replicate 63 (.i32 0)) = none := by decide
example : decodeState .boolean (List.replicate 65 (.i32 0)) = none := by decide
example (r t : Representation) (s : State) :
    convertState r t (encodeState r s) = some (encodeState t s) := convert_encoded r t s

/-- Each actual artifact's next result includes both continuation words. -/
example (store : Store F O) :
    Steps (I := String) (packedModule.instantiate store).1 dummyFrame
      (values (packedInput 0xffffffff (0xaaaaaaaa,1)) ++ [.invoke store.funcs.length]) dummyFrame
      (values [.i32 0,.i32 0xffffffff,.i32 0xaaaaaaaa]) := packed_invoke store _ _

example (store : Store F O) (x : Word) (s : State) :
    Steps (I := String) (booleanModule.instantiate store).1 dummyFrame
      (values (ABI.encode (a := FirstOrderCompiler.Ty.prod (Words.shape 32)
        (.prod (Words.shape 32) (Words.shape 32))) (Words.encode x,unpackState s)) ++
        [.invoke store.funcs.length]) dummyFrame
      (values (ABI.encode (a := FirstOrderCompiler.Ty.prod (Words.shape 32)
        (.prod (Words.shape 32) (Words.shape 32)))
        (Words.encode (source.step (x,s)).1,unpackState (source.step (x,s)).2))) :=
  boolean_invoke store x s

example : ownedStatePeak .boolean .packed = 198 := by decide
example : ownedStatePeak .boolean .boolean = 384 := by decide
example : eventTotal copyWeight (migrationTrace .boolean .packed 48 true true true) = 68 := by decide
example : eventTotal copyWeight (migrationTrace .packed .boolean 6216 true true false) = 130 := by decide
example : eventTotal conversionWeight (migrationTrace .packed .boolean 6216 true true true) = 64 := by decide
example : migrationTrace .boolean .packed 48 false true true = [] := by decide
example : eventTotal installationWeight (migrationTrace .packed .boolean 6216 true false true) = 0 := by decide
example : eventTotal copyWeight (migrationTrace .boolean .packed 48 true false true) = 66 := by decide
example : adapterByteBudget 6216 48 = 6312 := by decide
example : adapterByteBudget 48 6216 = 12480 := by decide

end Examples.WasmWordContinuation
