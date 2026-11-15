import Applications.Wasm.Core
import Applications.FRP.FiniteSumLowering

/-! Canonical raw-value admission for Boolean products. Source sum admission
additionally uses the existing exact finite-sum decoder. -/
namespace Applications.Wasm.ABI
open FirstOrderCompiler

def slots : Ty → Nat
  | .base => 1
  | .unit => 0
  | .prod a b => slots a + slots b

def bit (b : Bool) : Value := .i32 (if b then 1 else 0)

def encode : {a : Ty} → Val Bool a → List Value
  | .base, b => [bit b]
  | .unit, _ => []
  | .prod _ _, (x, y) => encode x ++ encode y

@[simp] theorem encode_length {a : Ty} (x : Val Bool a) : (encode x).length = slots a := by
  induction a with
  | base => rfl
  | unit => rfl
  | prod a b ia ib => simp [encode, slots, ia, ib]

/-- Prefix parsing is internal; public admission also requires no remainder. -/
def parse : (a : Ty) → List Value → Option (Val Bool a × List Value)
  | .base, .i32 n :: rest =>
      if n = 0 then some (false, rest)
      else if n = 1 then some (true, rest) else none
  | .base, _ => none
  | .unit, raw => some ((), raw)
  | .prod a b, raw => do
      let (x, rest) ← parse a raw
      let (y, tail) ← parse b rest
      pure ((x, y), tail)

theorem parse_iff {a : Ty} (raw : List Value) (x : Val Bool a) (rest : List Value) :
    parse a raw = some (x, rest) ↔ raw = encode x ++ rest := by
  induction a generalizing raw rest with
  | base =>
    cases raw with
    | nil => simp [parse, encode]
    | cons v vs =>
      cases v with
      | i32 n =>
        cases x <;> simp [parse, encode, bit]
        all_goals split <;> simp_all
      | _ => simp [parse, encode, bit]
  | unit => cases x; simp [parse, encode]
  | prod a b ia ib =>
    rcases x with ⟨x, y⟩
    simp only [parse, bind, pure, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨⟨x', mid⟩, hx, ⟨⟨y', tail⟩, hy, heq⟩⟩
      cases heq
      dsimp only at *
      rw [ia _ _ _] at hx
      rw [ib _ _ _] at hy
      simp [encode, hx, hy, List.append_assoc]
    · intro h
      refine ⟨(x, encode y ++ rest), ?_, (y, rest), ?_, rfl⟩
      · apply (ia _ _ _).2
        simpa [encode, List.append_assoc] using h
      · exact (ib _ _ _).2 rfl

def decode (a : Ty) (raw : List Value) : Option (Val Bool a) := do
  let (x, rest) ← parse a raw
  if rest = [] then some x else none

theorem decode_iff {a : Ty} (raw : List Value) (x : Val Bool a) :
    decode a raw = some x ↔ raw = encode x := by
  simp only [decode, bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨⟨y, rest⟩, hp, h⟩
    split at h
    · rename_i hr
      cases h
      dsimp only at *
      subst rest
      simpa using (parse_iff raw y []).1 hp
    · contradiction
  · intro h
    refine ⟨(x, []), ?_, by simp⟩
    apply (parse_iff raw x []).2
    simpa using h

@[simp] theorem decode_encode {a : Ty} (x : Val Bool a) : decode a (encode x) = some x :=
  (decode_iff _ _).2 rfl

theorem encode_injective {a : Ty} : Function.Injective (encode (a := a)) := by
  intro x y h
  have : some x = some y := by rw [← decode_encode x, h, decode_encode y]
  exact Option.some.inj this

def encodeSum {a : FRPSpec.FiniteSum.Ty} (x : FRPSpec.FiniteSum.Value a) : List Value :=
  encode (FRPSpec.FiniteSum.encode x)

def decodeSum (a : FRPSpec.FiniteSum.Ty) (raw : List Value) :
    Option (FRPSpec.FiniteSum.Value a) := do
  let bits ← decode a.storage raw
  FRPSpec.FiniteSum.decode a bits

theorem decodeSum_iff (a : FRPSpec.FiniteSum.Ty) (raw : List Value)
    (x : FRPSpec.FiniteSum.Value a) :
    decodeSum a raw = some x ↔ raw = encodeSum x := by
  simp only [decodeSum, bind, Option.bind_eq_some_iff, decode_iff,
    FRPSpec.FiniteSum.decode_iff, encodeSum]
  constructor
  · rintro ⟨bits, h, rfl⟩
    exact h
  · intro h
    exact ⟨FRPSpec.FiniteSum.encode x, h, rfl⟩

@[simp] theorem decodeSum_encode (a : FRPSpec.FiniteSum.Ty) (x : FRPSpec.FiniteSum.Value a) :
    decodeSum a (encodeSum x) = some x := (decodeSum_iff _ _ _).2 rfl

end Applications.Wasm.ABI
