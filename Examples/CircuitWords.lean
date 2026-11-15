import Applications.Circuits.Words

/-! Checked uses of the canonical word bridge and the two bounded lowering routes.
All source observations use the public correctness theorem. Counts refer to the
named circuit/plan models; no serialized module or external run is claimed. -/
namespace Examples.CircuitWords
open Applications.Circuits
open Applications.Circuits.Words

/-- Native word observations of the composed Boolean circuit. -/
def run (tag : Bool) (x y : BitVec 32) : BitVec 32 × (BitVec 32 × BitVec 32) :=
  let out := (selector 32).execute (tag,(encode x,encode y))
  (decode out.1,(decode out.2.1,decode out.2.2))

theorem run_correct (tag : Bool) (x y : BitVec 32) : run tag x y = meaning tag x y := by
  simpa [run] using selector_correct tag (encode x) (encode y)

/-- Both alternatives agree for all words and canonical selector values. -/
theorem routes_agree (tag : Bool) (x y : BitVec 32) :
    run tag x y = NativeI32.selector (NativeI32.encodeTag tag) x y := by
  rw [run_correct, NativeI32.selector_correct]

example : encode (0#0) = () := rfl
example : decode (n := 0) () = 0#0 := rfl
example : (ripple 0).execute (((),()),true) = ((),true) := rfl

/-- Width zero retains incoming carry even though the modular word is empty. -/
example : (decode ((ripple 0).execute (((),()),true)).1).toNat +
    2^0 * (((ripple 0).execute (((),()),true)).2).toNat = 1 := by
  simpa [decode] using ripple_value (n := 0) () () true

/-- The LSB-first encoding is observable, including its terminating unit. -/
example : encode (5#3) = (true,(false,(true,()))) := rfl
example : decode (n := 3) (true,(false,(true,()))) = 5#3 := by decide

example (x : BitVec 32) : decode (encode x) = x := decode_encode x
example (x : Bits 32) : encode (decode x) = x := encode_decode x

example (tag : Bool) : run tag 0 0 = (0,(0,0)) := by
  rw [run_correct]; cases tag <;> decide

example : run true 0xffffffff 1 = (0,(0xffffffff,1)) := by
  rw [run_correct]; decide
example : run false 0xffffffff 1 = (0xfffffffe,(0xffffffff,1)) := by
  rw [run_correct]; decide
example : run true 0x7fffffff 1 = (0x80000000,(0x7fffffff,1)) := by
  rw [run_correct]; decide
example : run true 0xaaaaaaaa 0x33333333 = (0xdddddddd,(0xaaaaaaaa,0x33333333)) := by
  rw [run_correct]; decide
example : run false 0xaaaaaaaa 0x33333333 = (0x99999999,(0xaaaaaaaa,0x33333333)) := by
  rw [run_correct]; decide

/-- Independent expected carry-chain values, including zero length and final overflow. -/
theorem carry_expected : ∀ k : Fin 33,
    meaning true (BitVec.ofNat 32 (2^k.val-1)) 1 =
      (BitVec.ofNat 32 (2^k.val), (BitVec.ofNat 32 (2^k.val-1),1)) := by
  decide

/-- Every carry-chain case is connected to the compiled circuit's public theorem. -/
theorem all_carry_chains (k : Fin 33) :
    run true (BitVec.ofNat 32 (2^k.val-1)) 1 =
      (BitVec.ofNat 32 (2^k.val), (BitVec.ofNat 32 (2^k.val-1),1)) := by
  rw [run_correct]
  exact carry_expected k

/-- All 96 source bits remain in the result; no host-width packing is used. -/
example : cells (.prod (shape 32) (.prod (shape 32) (shape 32))) = 96 := by decide

example : (selector 32).work = 6235 := by rw [selector_work]
example (n : Nat) : (ripple n).work = 122*n+3 := ripple_work n

/- Calculated plan counts include 65 parameter slots and 96 final result loads. -/
set_option maxRecDepth 10000 in
example : invocationPlan (selector 32) = ⟨3266,866,96⟩ := by decide
example : NativeI32.planCounts NativeI32.selectorPlan = (16,6,some (3,3)) :=
  NativeI32.selector_plan_counts

/-- Standard numeric truthiness is strictly broader than canonical tag admission. -/
example : NativeI32.decodeTag (2#32) = none := by decide
example : NativeI32.select (11#32) (22#32) (2#32) = 11 := by decide
example : NativeI32.decodeWord (2^32) = none := by decide
example : NativeI32.decodeWord (2^32-1) = some (0xffffffff#32) := by decide
example (b : Bool) : NativeI32.decodeTag (NativeI32.encodeTag b) = some b :=
  (NativeI32.decodeTag_iff _ _).2 rfl

end Examples.CircuitWords
