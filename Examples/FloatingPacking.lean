import Applications.Floating.Packing
import Applications.Floating.Intervals

/-!
# Actual packing followed by the existing interval consumer

Canonicality and the overflow bound belong to the input relation. Packing still
executes on ordinary unpacked data. Its result is observed by the actual unpacker
and partial rational decoder before the existing interval consumer runs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FloatingPacking

open Float.Model Float.Model.UnpackedFloat
open Floating.Packing

def packedRead (format : Format) (bits : BitVec format.numBits) : Option Rat :=
  Floating.Observation.unpack (UnpackedFloat.unpack format bits)

@[reducible] def representation (format : Format) : Relational.RelRep :=
  ⟨UnpackedFloat, Rat, fun value q =>
    Canonical format value ∧ NoOverflow format value ∧ Floating.Observation.unpack value = some q⟩

def packingSquare (format : Format) :
    Relational.RelSquare (representation format) (Floating.Intervals.observed (packedRead format)) where
  impl := pack format
  spec := id
  preserves := by
    intro value q ⟨canonical, noOverflow, decoded⟩
    change Floating.Observation.unpack (UnpackedFloat.unpack format (pack format value)) = some q
    rw [pack_numeric format value canonical noOverflow, decoded]

def consume (format : Format)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation) :=
  Relational.compose (Floating.Intervals.adapt (packedRead format) consumer) (packingSquare format)

theorem consume_sound (format : Format)
    (consumer : Relational.RelSquare IntervalAnalysis.representation IntervalAnalysis.representation)
    (value : UnpackedFloat) (q : Rat) (canonical : Canonical format value)
    (noOverflow : NoOverflow format value) (decoded : Floating.Observation.unpack value = some q) :
    ∃ interval, (consume format consumer).impl value = some interval ∧
      IntervalAnalysis.Contains interval (consumer.spec q) := by
  have decodedPack : packedRead format (pack format value) = some q :=
    (pack_numeric format value canonical noOverflow).trans decoded
  simpa only [consume, Relational.compose, Function.comp, packingSquare] using
    Floating.Intervals.adapt_sound (packedRead format) consumer (pack format value) q decodedPack

def square (format : Format) := consume format Floating.Intervals.squareConsumer

theorem square_value (format : Format) (value : UnpackedFloat) (q : Rat)
    (canonical : Canonical format value) (noOverflow : NoOverflow format value)
    (decoded : Floating.Observation.unpack value = some q) :
    (square format).impl value = some (IntervalAnalysis.singleton (q * q)) := by
  change (packedRead format (pack format value)).map _ = _
  have decodedPack : packedRead format (pack format value) = some q :=
    (pack_numeric format value canonical noOverflow).trans decoded
  rw [decodedPack]
  exact congrArg some (Floating.Intervals.squareConsumer_singleton q)

theorem square_contains (format : Format) (value : UnpackedFloat) (q : Rat)
    (canonical : Canonical format value) (noOverflow : NoOverflow format value)
    (decoded : Floating.Observation.unpack value = some q) :
    ∃ interval, (square format).impl value = some interval ∧ IntervalAnalysis.Contains interval (q * q) := by
  simpa only [square, Floating.Intervals.squareConsumer, Relational.compose, Function.comp,
    Relational.pair, Relational.identity, IntervalAnalysis.mulSquare, id_eq] using
    consume_sound format Floating.Intervals.squareConsumer value q canonical noOverflow decoded

theorem negative_zero_roundtrip :
    UnpackedFloat.unpack Format.binary64 (pack Format.binary64 (.zero .negative)) = .zero .negative :=
  unpack_zero_pack _ _

def subnormal64 : UnpackedFloat := .finite .positive 1 (-1074) (by decide)
def subnormal32 : UnpackedFloat := .finite .positive 1 (-149) (by decide)
def negativeOne64 : UnpackedFloat := .finite .negative (2 ^ 52) (-52) (by decide)

theorem subnormal64_canonical : Canonical Format.binary64 subnormal64 := by
  unfold Canonical subnormal64
  decide +kernel

theorem subnormal64_noOverflow : NoOverflow Format.binary64 subnormal64 := by
  unfold NoOverflow subnormal64
  decide +kernel

theorem subnormal32_canonical : Canonical Format.binary32 subnormal32 := by
  unfold Canonical subnormal32
  decide +kernel

theorem subnormal32_noOverflow : NoOverflow Format.binary32 subnormal32 := by
  unfold NoOverflow subnormal32
  decide +kernel

theorem negativeOne64_canonical : Canonical Format.binary64 negativeOne64 := by
  unfold Canonical negativeOne64
  decide +kernel

theorem negativeOne64_noOverflow : NoOverflow Format.binary64 negativeOne64 := by
  unfold NoOverflow negativeOne64
  decide +kernel

theorem subnormal64_roundtrip :
    UnpackedFloat.unpack Format.binary64 (pack Format.binary64 subnormal64) = subnormal64 :=
  unpack_pack _ _ subnormal64_canonical subnormal64_noOverflow

theorem subnormal32_roundtrip :
    UnpackedFloat.unpack Format.binary32 (pack Format.binary32 subnormal32) = subnormal32 :=
  unpack_pack _ _ subnormal32_canonical subnormal32_noOverflow

theorem negativeOne64_roundtrip :
    UnpackedFloat.unpack Format.binary64 (pack Format.binary64 negativeOne64) = negativeOne64 :=
  unpack_pack _ _ negativeOne64_canonical negativeOne64_noOverflow

theorem subnormal64_observation :
    Floating.Observation.unpack subnormal64 = some (1 / (2 : Rat) ^ (1074 : Nat)) := by
  decide +kernel

theorem subnormal32_observation :
    Floating.Observation.unpack subnormal32 = some (1 / (2 : Rat) ^ (149 : Nat)) := by
  decide +kernel

theorem negativeOne64_observation : Floating.Observation.unpack negativeOne64 = some (-1) := by
  decide +kernel

theorem packed_subnormal64_observation :
    packedRead Format.binary64 (pack Format.binary64 subnormal64) =
      some (1 / (2 : Rat) ^ (1074 : Nat)) := by
  change Floating.Observation.unpack (UnpackedFloat.unpack _ _) = _
  rw [pack_numeric _ _ subnormal64_canonical subnormal64_noOverflow, subnormal64_observation]

theorem packed_subnormal32_observation :
    packedRead Format.binary32 (pack Format.binary32 subnormal32) =
      some (1 / (2 : Rat) ^ (149 : Nat)) := by
  change Floating.Observation.unpack (UnpackedFloat.unpack _ _) = _
  rw [pack_numeric _ _ subnormal32_canonical subnormal32_noOverflow, subnormal32_observation]

theorem negativeOne64_square_value :
    (square Format.binary64).impl negativeOne64 = some (IntervalAnalysis.singleton 1) := by
  have h := square_value _ _ _ negativeOne64_canonical negativeOne64_noOverflow negativeOne64_observation
  norm_num at h ⊢
  exact h

theorem negativeOne64_square_contains :
    ∃ interval, (square Format.binary64).impl negativeOne64 = some interval ∧
      IntervalAnalysis.Contains interval 1 := by
  have h := square_contains _ _ _ negativeOne64_canonical negativeOne64_noOverflow negativeOne64_observation
  norm_num at h ⊢
  exact h

theorem negative_zero_square :
    (square Format.binary64).impl (.zero .negative) = some (IntervalAnalysis.singleton 0) := by
  simpa only [mul_zero] using square_value Format.binary64 (.zero .negative) 0
    True.intro True.intro rfl

def noncanonical32 : UnpackedFloat := .finite .positive 1 0 (by decide)

theorem noncanonical32_conditions :
    NoOverflow Format.binary32 noncanonical32 ∧ ¬ Canonical Format.binary32 noncanonical32 := by
  unfold NoOverflow Canonical noncanonical32
  decide +kernel

theorem noncanonical32_loses_value :
    Floating.Observation.unpack noncanonical32 = some 1 ∧
    packedRead Format.binary32 (pack Format.binary32 noncanonical32) =
      some (1 / (2 : Rat) ^ (149 : Nat)) ∧
    packedRead Format.binary32 (pack Format.binary32 noncanonical32) ≠
      Floating.Observation.unpack noncanonical32 := by
  decide +kernel

def overflowing32 : UnpackedFloat := .finite .positive (2 ^ 23) 105 (by decide)

theorem canonical_overflows32 :
    Canonical Format.binary32 overflowing32 ∧ ¬ NoOverflow Format.binary32 overflowing32 ∧
      packedRead Format.binary32 (pack Format.binary32 overflowing32) = none := by
  unfold Canonical NoOverflow overflowing32
  decide +kernel

end Examples.FloatingPacking
