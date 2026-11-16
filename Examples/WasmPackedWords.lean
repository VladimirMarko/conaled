import Applications.Wasm.PackedWords
import Examples.CircuitWords

/-! Complete word observations through the actual packed module. -/
namespace Examples.WasmPackedWords
open Applications.Wasm Applications.Wasm.PackedWords Applications.Circuits

/-- Arbitrary source words retain the selected result and both operands. -/
example (s : Store F O) (tag : Bool) (x y : BitVec 32) :
    Steps (I := String) (selectorModule.instantiate s).1 dummyFrame
      (values (input tag x y) ++ [.invoke s.funcs.length]) dummyFrame
      (values (output (if tag then x+y else x ^^^ y,(x,y)))) := invoke s tag x y

/-- Every carry length, including no carry and overflow, uses the public invocation. -/
theorem carry_chain (s : Store F O) (k : Fin 33) :
    Steps (I := String) (selectorModule.instantiate s).1 dummyFrame
      (values (input true (BitVec.ofNat 32 (2^k.val-1)) 1) ++ [.invoke s.funcs.length]) dummyFrame
      (values (output (BitVec.ofNat 32 (2^k.val),(BitVec.ofNat 32 (2^k.val-1),1)))) := by
  have h := invoke (I := String) s true (BitVec.ofNat 32 (2^k.val-1)) 1
  rw [Examples.CircuitWords.carry_expected] at h
  exact h

/-- The independently calculated result is connected to execution, not only arithmetic. -/
theorem overflow (s : Store F O) :
    Steps (I := String) (selectorModule.instantiate s).1 dummyFrame
      (values (input true 0xffffffff 1) ++ [.invoke s.funcs.length]) dummyFrame
      (values (output (0,(0xffffffff,1)))) := by
  have h := invoke (I := String) s true 0xffffffff 1
  exact h

example (s : Store F O) :
    Steps (I := String) (selectorModule.instantiate s).1 dummyFrame
      (values (input false 0xaaaaaaaa 0x33333333) ++ [.invoke s.funcs.length]) dummyFrame
      (values (output (0x99999999,(0xaaaaaaaa,0x33333333)))) := invoke s false _ _

example (s : Store F O) :
    Steps (I := String) (selectorModule.instantiate s).1 dummyFrame
      (values (input true 0xaaaaaaaa 0x33333333) ++ [.invoke s.funcs.length]) dummyFrame
      (values (output (0xdddddddd,(0xaaaaaaaa,0x33333333)))) := invoke s true _ _

example (s : Store F O) :
    Steps (I := String) (selectorModule.instantiate s).1 dummyFrame
      (values (input true 0x7fffffff 1) ++ [.invoke s.funcs.length]) dummyFrame
      (values (output (0x80000000,(0x7fffffff,1)))) := invoke s true _ _

example (s : Store F O) (tag : Bool) :
    Steps (I := String) (selectorModule.instantiate s).1 dummyFrame
      (values (input tag 0 0) ++ [.invoke s.funcs.length]) dummyFrame
      (values (output (0,(0,0)))) := by
  cases tag <;> exact invoke s _ _ _

example : decodeInput [.i32 2,.i32 0xffffffff,.i32 1] = none := by decide
example : Applications.Wasm.select (11#32) 22 2 = 11 := by decide
example : decodeInput [.i32 1,.i32 2] = none := rfl
example : decodeInput [.i32 1,.i64 2,.i32 3] = none := rfl
example : decodeInput [.i32 1,.i32 2,.i32 3,.i32 4] = none := rfl
example (r : Output) : packOutput (unpackOutput r) = r := pack_unpack_output r
example (bits : Words.Bits 32 × (Words.Bits 32 × Words.Bits 32)) :
    unpackOutput (packOutput bits) = bits := unpack_pack_output bits

/-- Same operation with a foreign typed prefix and arbitrary pending suffix. -/
example (s : ExtendedStore F O) (fr : Frame) (x y tag : BitVec 32) (suffix : List (Admin String)) :
    Step s fr (values [.i64 17] ++ [.value (.i32 x),.value (.i32 y),.value (.i32 tag),.instr .select] ++ suffix)
      fr (values [.i64 17] ++ [.value (.i32 (Applications.Wasm.select x y tag))] ++ suffix) :=
  (Step.select fr x y tag).context (.seq [.i64 17] .hole suffix)

example : selectorModule.withinLimits ⟨3,3,6,16⟩ = true := by decide
example : admitWithinLimits .packed ⟨3,3,6,16⟩ = some selectorBytes.toByteArray := by decide
example : admitWithinLimits .packed ⟨2,3,6,16⟩ = none := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : admitWithinLimits .boolean ⟨3,3,6,16⟩ = none := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (admitWithinLimits .boolean Limits.default).isSome = true := by decide +kernel

example : Binary.ModuleBytes selectorModule selectorBytes :=
  selectorModule.serialize_correct selector_serialized
example : (Binary.instruction (.binary .add)).map Subtype.val = some [0x6a] := by decide
example : (Binary.instruction .select).map Subtype.val = some [0x1b] := by decide

end Examples.WasmPackedWords
