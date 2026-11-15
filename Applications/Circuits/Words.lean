import Applications.Timing.Adders
import Applications.FRP.FiniteSumLowering
import Mathlib.Tactic.Linarith

/-! Canonical least-significant-bit-first words and compositional Boolean circuits.
The arithmetic specification is `BitVec`; no Wasm module or runtime is asserted. -/
namespace Applications.Circuits.Words
open FirstOrderCompiler

/-- A word stores the least significant bit first and ends in unit. -/
def shape : Nat → Ty
  | 0 => .unit
  | n + 1 => .prod .base (shape n)

abbrev Bits (n : Nat) := Val Bool (shape n)

def encode : {n : Nat} → BitVec n → Bits n
  | 0, _ => ()
  | n + 1, x => (x.getLsbD 0, encode (x.extractLsb' 1 n))

def decode : {n : Nat} → Bits n → BitVec n
  | 0, _ => 0#0
  | _ + 1, (b, bs) => (decode bs).concat b

private theorem tail_concat (x : BitVec n) (b : Bool) :
    (x.concat b).extractLsb' 1 n = x := by
  ext i hi
  simp [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_extractLsb', hi,
    Nat.add_comm]

@[simp] theorem encode_concat (x : BitVec n) (b : Bool) :
    encode (x.concat b) = (b, encode x) := by
  simp [encode, tail_concat]
  rfl

@[simp] theorem decode_encode (x : BitVec n) : decode (encode x) = x := by
  induction x using BitVec.concat_induction with
  | nil => rfl
  | concat x b ih => simp [decode, ih]

@[simp] theorem encode_decode (bits : Bits n) : encode (decode bits) = bits := by
  induction n with
  | zero => cases bits; rfl
  | succ n ih => cases bits with | mk b bs => simp [decode, ih]; rfl

theorem encode_injective : Function.Injective (@encode n) := by
  intro x y h
  simpa using congrArg decode h

theorem decode_injective : Function.Injective (@decode n) := by
  intro x y h
  simpa using congrArg encode h

@[simp] theorem cells_shape (n : Nat) : cells (shape n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [shape, cells, ih, Nat.add_comm]

/-- Componentwise xor uses the existing gate vocabulary. -/
def xor : (n : Nat) → Circuit (.prod (shape n) (shape n)) (shape n)
  | 0 => .terminate
  | n + 1 => .pair
      (.compose Circuit.xor (.pair (.compose .first .first) (.compose .first .second)))
      (.compose (xor n) (.pair (.compose .second .first) (.compose .second .second)))

@[simp] theorem xor_correct (x y : Bits n) :
    decode ((xor n).execute (x,y)) = decode x ^^^ decode y := by
  induction n with
  | zero => cases x; cases y; rfl
  | succ n ih =>
    rcases x with ⟨a,x⟩; rcases y with ⟨b,y⟩
    simp [xor, Circuit.execute, Circuit.xor, Gate.meaning, decode, ih,
      BitVec.concat_xor_concat]

/-- False chooses the left word, as in the existing finite-sum lowering. -/
def select (n : Nat) : Circuit (.prod .base (.prod (shape n) (shape n))) (shape n) :=
  FRPSpec.FiniteSum.mux (shape n)

@[simp] theorem select_correct (tag : Bool) (x y : Bits n) :
    decode ((select n).execute (tag,(x,y))) = if tag then decode y else decode x := by
  rw [select, FRPSpec.FiniteSum.mux_execute]
  cases tag <;> rfl

abbrev AddInput (n : Nat) := Ty.prod (.prod (shape n) (shape n)) .base
abbrev AddOutput (n : Nat) := Ty.prod (shape n) .base

/-- Calculate one full adder once, retaining both tails. -/
def prepare (n : Nat) : Circuit (AddInput (n+1)) (.prod .base (AddInput n)) :=
  .compose
    (.pair (.compose .first .first)
      (.pair .second (.compose .second .first)))
    (.pair
      (.compose Applications.Timing.Adders.fullAdder
        (.pair (.pair (.compose .first (.compose .first .first))
                     (.compose .first (.compose .second .first))) .second))
      (.pair (.compose .second (.compose .first .first))
             (.compose .second (.compose .second .first))))

def finish (n : Nat) : Circuit (.prod .base (AddOutput n)) (AddOutput (n+1)) :=
  .pair (.pair .first (.compose .first .second)) (.compose .second .second)

/-- The recursive circuit occurs once, after the low-bit carry is computed. -/
def ripple : (n : Nat) → Circuit (AddInput n) (AddOutput n)
  | 0 => .pair .terminate .second
  | n+1 => .compose (finish n)
      (.compose (Circuit.productMap .identity (ripple n)) (prepare n))

theorem ripple_step (a b carry : Bool) (x y : Bits n) :
    (ripple (n+1)).execute (((a,x),(b,y)),carry) =
      let low := Applications.Timing.Adders.fullAdder.execute ((a,b),carry)
      let high := (ripple n).execute ((x,y),low.2)
      ((low.1,high.1),high.2) := by
  rfl

/-- Exact arithmetic retains the carry beyond the word width, including width zero. -/
theorem ripple_value (x y : Bits n) (carry : Bool) :
    let result := (ripple n).execute ((x,y),carry)
    (decode result.1).toNat + 2^n * result.2.toNat =
      (decode x).toNat + (decode y).toNat + carry.toNat := by
  induction n generalizing carry with
  | zero => cases x; cases y; simp [ripple, Circuit.execute, decode]
  | succ n ih =>
    rcases x with ⟨a,x⟩; rcases y with ⟨b,y⟩
    have low := Applications.Timing.Adders.fullAdder_addition a b carry
    rw [← Circuit.execute_correct] at low
    have high := ih x y (Applications.Timing.Adders.fullAdder.execute ((a,b),carry)).2
    dsimp only
    rw [ripple_step a b carry x y]
    simp only [decode, BitVec.toNat_concat, Nat.pow_succ] at *
    nlinarith

/-- Modular addition discards only the final carry, after calculating it. -/
def add (n : Nat) : Circuit (.prod (shape n) (shape n)) (shape n) :=
  .compose .first (.compose (ripple n)
    (.pair .identity (.compose (.gate (.constant false)) .terminate)))

@[simp] theorem add_correct (x y : Bits n) :
    decode ((add n).execute (x,y)) = decode x + decode y := by
  apply BitVec.eq_of_toNat_eq
  have h := congrArg (fun k => k % 2^n) (ripple_value x y false)
  simpa [add, Circuit.execute, Gate.meaning, BitVec.toNat_add, Nat.add_mod,
    Nat.mod_eq_of_lt (decode ((ripple n).execute ((x,y),false)).1).isLt] using h

/-- Compute both total arms, select their result, and retain both original words. -/
def selector (n : Nat) : Circuit (.prod .base (.prod (shape n) (shape n)))
    (.prod (shape n) (.prod (shape n) (shape n))) :=
  .compose (.pair (.compose (select n) .first) .second)
    (.pair
      (.pair .first (.pair (.compose (xor n) .second) (.compose (add n) .second)))
      .second)

/-- Independent word-level meaning; addition is modular BitVec addition. -/
def meaning (tag : Bool) (x y : BitVec n) := (if tag then x+y else x ^^^ y, (x,y))

@[simp] theorem selector_correct (tag : Bool) (x y : Bits n) :
    let out := (selector n).execute (tag,(x,y))
    (decode out.1, (decode out.2.1, decode out.2.2)) = meaning tag (decode x) (decode y) := by
  simp only [selector, Circuit.execute]
  rw [select_correct, add_correct, xor_correct]
  rfl

/-- Circuit work counts syntax-node visits, not Wasm instructions. -/
@[simp] theorem prepare_work (n : Nat) : (prepare n).work = (prepare 0).work := rfl
@[simp] theorem finish_work (n : Nat) : (finish n).work = (finish 0).work := rfl

def rippleStageWork := (prepare 0).work + (finish 0).work + 8

theorem ripple_work (n : Nat) : (ripple n).work = rippleStageWork*n + 3 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ripple, Circuit.productMap, Circuit.work, prepare_work, finish_work, ih]
    simp only [rippleStageWork, Nat.mul_add, Nat.mul_one] at *
    omega

/-- A proposed fresh-local lowering count: routing aliases wires; each gate
stores one result. These counts describe a lowering plan, not emitted code. -/
structure Plan where
  instructions : Nat
  locals : Nat
  stack : Nat
  deriving DecidableEq, Repr

def gatePlan : Gate a b → Plan
  | .constant _ => ⟨2,1,1⟩
  | .not _ => ⟨3,1,1⟩
  | .nand _ _ => ⟨5,1,2⟩
  | .nor _ _ => ⟨5,1,2⟩
  | .xor _ _ => ⟨4,1,2⟩

def Plan.then (p q : Plan) : Plan :=
  ⟨p.instructions+q.instructions, p.locals+q.locals, max p.stack q.stack⟩

def plan : Circuit a b → Plan
  | .compose g f => (plan f).then (plan g)
  | .pair f g => (plan f).then (plan g)
  | .gate p => gatePlan p
  | _ => ⟨0,0,0⟩

/-- Include parameter locals and the final ordered result loads. -/
def invocationPlan (c : Circuit a b) : Plan :=
  ⟨(plan c).instructions + cells b, cells a + (plan c).locals,
    max (plan c).stack (cells b)⟩

@[simp] theorem plan_routing_prepare (n : Nat) : plan (prepare n) = plan (prepare 0) := rfl
@[simp] theorem plan_routing_finish (n : Nat) : plan (finish n) = ⟨0,0,0⟩ := rfl

theorem ripple_plan_instructions (n : Nat) :
    (plan (ripple n)).instructions = (plan (prepare 0)).instructions * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [ripple, plan, Circuit.productMap, Plan.then, ih, Nat.mul_add, Nat.add_comm]

theorem ripple_plan_locals (n : Nat) :
    (plan (ripple n)).locals = (plan (prepare 0)).locals * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [ripple, plan, Circuit.productMap, Plan.then, ih, Nat.mul_add, Nat.add_comm]

/-- The complete composed client also grows linearly in width. -/
theorem xor_work (n : Nat) : (xor n).work = 18*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [xor, Circuit.work, Circuit.xor, ih]; omega

theorem select_work (n : Nat) : (select n).work = 54*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [select] at *
    simp [shape, FRPSpec.FiniteSum.mux, FRPSpec.FiniteSum.boolMux, Circuit.work,
      Circuit.or, Circuit.and, Circuit.not, Circuit.nand, Circuit.nor, ih]
    omega

theorem selector_work (n : Nat) : (selector n).work = 194*n+27 := by
  have stage : rippleStageWork = 122 := rfl
  simp [selector, Circuit.work, xor_work, select_work, add, ripple_work, stage]
  omega


namespace NativeI32
/-- Unsigned i32 patterns, with the pinned Core 2 numerical equations below.
These local laws do not assert module validation or execution. -/
abbrev Word := BitVec 32

def add (x y : Word) : Word := BitVec.ofNat 32 ((x.toNat+y.toNat) % 2^32)
def xor (x y : Word) : Word := BitVec.ofNat 32 (x.toNat ^^^ y.toNat)
/-- Standard select returns its first operand for any nonzero condition. -/
def select (x y tag : Word) : Word := if tag = 0 then y else x

def encodeTag (b : Bool) : Word := BitVec.ofNat 32 b.toNat
def decodeTag (w : Word) : Option Bool :=
  if w = 0 then some false else if w = 1 then some true else none

theorem add_correct (x y : Word) : add x y = x+y := by
  apply BitVec.eq_of_toNat_eq
  simp [add, BitVec.toNat_add]

theorem xor_correct (x y : Word) : xor x y = x ^^^ y := by
  change BitVec.ofNat 32 (x.toNat ^^^ y.toNat) = _
  rw [BitVec.ofNat_xor]
  simp

@[simp] theorem decodeTag_iff (w : Word) (b : Bool) :
    decodeTag w = some b ↔ w = encodeTag b := by
  cases b with
  | false =>
    change (if w = 0 then some false else if w = 1 then some true else none) = some false ↔ w = 0
    by_cases h0 : w = 0 <;> simp [h0]
  | true =>
    change (if w = 0 then some false else if w = 1 then some true else none) = some true ↔ w = 1
    by_cases h0 : w = 0
    · subst w; decide
    · by_cases h1 : w = 1
      · subst w; decide
      · rw [ite_eq_right h0, ite_eq_right h1]
        simp only [reduceCtorEq, false_iff]
        exact h1

@[simp] theorem select_correct (x y : Word) (b : Bool) :
    select x y (encodeTag b) = if b then x else y := by
  cases b <;> simp [select, encodeTag]

/-- The alternative packed ABI has one i32 per word, without truncating host values. -/
def decodeWord (raw : Nat) : Option Word :=
  if raw < 2^32 then some (BitVec.ofNat 32 raw) else none

theorem decodeWord_iff (raw : Nat) (x : Word) :
    decodeWord raw = some x ↔ raw = x.toNat := by
  unfold decodeWord
  split
  next h =>
    simp only [Option.some.injEq]
    constructor
    · intro e
      have := congrArg BitVec.toNat e
      change raw % 2^32 = x.toNat at this
      rwa [Nat.mod_eq_of_lt h] at this
    · intro e; subst raw; simp
  next h =>
    simp only [reduceCtorEq, false_iff]
    intro e; subst raw; exact h x.isLt

/-- Adapter from the default 32-slot Boolean ABI to one packed i32, and back. -/
def pack (bits : Bits 32) : Word := decode bits
def unpack (word : Word) : Bits 32 := encode word
@[simp] theorem pack_unpack (word : Word) : pack (unpack word) = word := decode_encode word
@[simp] theorem unpack_pack (bits : Bits 32) : unpack (pack bits) = bits := encode_decode bits

def selector (tag : Word) (x y : Word) := (select (add x y) (xor x y) tag, (x,y))

theorem selector_correct (tag : Bool) (x y : Word) :
    selector (encodeTag tag) x y = meaning tag x y := by
  simp only [selector, select_correct, add_correct, xor_correct, meaning]

/-- A fixed numeric/local instruction plan, not a complete Wasm representation. -/
inductive Op where
  | get : Nat → Op
  | set : Nat → Op
  | add | xor | select
  deriving DecidableEq, Repr

def selectorPlan : List Op :=
  [.get 1,.get 2,.add,.set 3, .get 1,.get 2,.xor,.set 4,
   .get 3,.get 4,.get 0,.select,.set 5, .get 5,.get 1,.get 2]

def Op.localBound : Op → Nat
  | .get i | .set i => i+1
  | _ => 0

def Op.effect : Op → Nat × Nat
  | .get _ => (0,1)
  | .set _ => (1,0)
  | .add | .xor => (2,1)
  | .select => (3,1)

/-- Check every prefix for underflow while calculating final and peak stack sizes. -/
def stackProfile : List Op → Nat → Nat → Option (Nat × Nat)
  | [], height, peak => some (height,peak)
  | op::ops, height, peak =>
    let (pop,push) := op.effect
    if pop ≤ height then
      let next := height-pop+push
      stackProfile ops next (max peak next)
    else none

def planCounts (ops : List Op) : Nat × Nat × Option (Nat × Nat) :=
  (ops.length, (ops.map Op.localBound).foldl max 0, stackProfile ops 0 0)

theorem selector_plan_counts : planCounts selectorPlan = (16,6,some (3,3)) := by decide

end NativeI32
end Applications.Circuits.Words
