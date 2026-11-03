import Applications.Resources.ByteBuffer

namespace Examples.ByteBuffer
open Sequences.BoundedSummary Sequences.ByteBuffer

def seed : Machine 255 2 := Sequences.ByteBuffer.empty (by decide)
def commands : List Command := [.observe,.append true,.append false,.append true,.query,.observe]

/-- Empty observation, exact capacity, overflow, parity and ordered history.
Both modes use the same existing trace-client theorem through the new simulation. -/
theorem replies (cached : Bool) :
    ((trace (step cached) commands seed).1.decode,(trace (step cached) commands seed).2) =
      ([true,false],[.sequence [],.appended true,.appended true,.appended false,
        .summary ⟨true⟩,.sequence [true,false]]) := by
  rw [trace_simulation cached commands seed (empty_valid _ _)]
  rfl

def full : Machine 1 1 := push true (Sequences.ByteBuffer.empty (by decide)) true (by decide)

theorem exact_word_no_wrap : full.counter.val = 1 :=
  (increment_no_wrap true (Sequences.ByteBuffer.empty (by decide : 1 ≤ 1)) true (by decide)).1

theorem full_rejects : step true (.append false) full = (full,.appended false) :=
  overflow_preserves true full false rfl

theorem converted_client :
    ((trace (step true) [.query,.observe] (convert full)).1.decode,
      (trace (step true) [.query,.observe] (convert full)).2) =
      ([true],[.summary ⟨true⟩,.sequence [true]]) := by
  rw [trace_simulation true _ _ (convert_valid full
    (push_valid true _ _ _ (empty_valid _ _)).1)]
  rw [convert_decode]
  have hd : full.decode = [true] := by rw [full,Sequences.ByteBuffer.decode_push,empty_decode]; rfl
  rw [hd]
  rfl

def badCache : Machine 255 2 := { seed with parity := ⟨true⟩ }

theorem invalid_cache : ¬ Sequences.ByteBuffer.Valid true badCache := by
  intro h
  have bad := h.2 rfl
  change (⟨true⟩ : Parity) = ⟨false⟩ at bad
  cases bad

theorem invalid_reply : (step true .query badCache).2 ≠ (spec 2 .query []).2 := by decide

/-- Allocation and output refusal are distinct, and rejected append does not
enter the later snapshot. -/
theorem failed_trace :
    ((attemptTrace true [(false,true,.append true),(true,true,.append false),
        (true,false,.observe),(true,true,.observe)] seed).1.decode,
      (attemptTrace true [(false,true,.append true),(true,true,.append false),
        (true,false,.observe),(true,true,.observe)] seed).2) =
      ([false],[.error .allocation,.ok (.appended true),.error .output,.ok (.sequence [false])]) := by
  rw [attempt_trace_simulation true _ seed (empty_valid _ _)]
  rfl

theorem pure_client_retained :
    (attemptTrace false (commands.map (fun c => (true,true,c))) seed).2 =
      [.ok (.sequence []),.ok (.appended true),.ok (.appended true),.ok (.appended false),
       .ok (.summary ⟨true⟩),.ok (.sequence [true,false])] := by
  rw [successful_trace]
  have h := congrArg Prod.snd (replies false)
  exact congrArg (List.map Except.ok) h

/-- 2 retained source bytes plus a 2-byte slice and 2-byte owned snapshot.
The primitive tariff remains five units; consumption is separately counted. -/
theorem snapshot_accounting :
    (Resources.ByteBuffer.events false 2 .observe 2).ownedPayloadPeak = 6 ∧
    (Resources.ByteBuffer.events false 2 .observe 2).consumeBytes = 2 ∧
    (Resources.ByteBuffer.events false 2 .observe 2).primitive.project {} = 5 := by
  refine ⟨rfl,rfl,?_⟩
  change (Resources.ByteBuffer.primitives false 2 .observe 2).project {} = 5
  rw [Resources.ByteBuffer.primitive_projection]
  rfl

theorem conversion_accounting :
    (Resources.ByteBuffer.conversion 2 1).ownedPayloadPeak = 4 ∧
    (Resources.ByteBuffer.conversion 2 1).primitive.project {} = 8 := by
  refine ⟨rfl,?_⟩
  rw [Resources.ByteBuffer.conversion_projection]
  rfl

theorem zero_capacity :
    ((trace (step false) [.append true,.observe] (Sequences.ByteBuffer.empty (by decide : 0 ≤ 0))).1.decode,
      (trace (step false) [.append true,.observe] (Sequences.ByteBuffer.empty (by decide : 0 ≤ 0))).2) =
      ([],[.appended false,.sequence []]) := by
  rw [trace_simulation false _ _ (empty_valid _ _)]
  rfl

end Examples.ByteBuffer
