import Applications.Wasm.Module

/-! A declarative grammar for the emitted Core 2.0 fragment. Productions follow
WebAssembly/spec 05ca4182176763112561ae20153975c12bd689e4, document/core/binary.
This file does not import or refer to the serializer. -/
namespace Applications.Wasm.Binary

abbrev Bytes := List UInt8

/-- The width decreases at each continuation, including the final partial digit. -/
inductive Unsigned : Nat → Nat → Bytes → Prop where
  | last (w n : Nat) (digit : n < 128) (bound : n < 2^w) :
      Unsigned w n [UInt8.ofNat n]
  | more (w d n : Nat) (width : 7 < w) (digit : d < 128)
      (tail : Unsigned (w - 7) n bs) :
      Unsigned w (128*n+d) (UInt8.ofNat (128+d) :: bs)

/-- Signed LEB128, with the two terminal productions distinguished explicitly. -/
inductive Signed : Nat → Int → Bytes → Prop where
  | positive (w n : Nat) (digit : n < 64) (bound : n < 2^(w-1)) :
      Signed w n [UInt8.ofNat n]
  | negative (w d : Nat) (lo : 64 ≤ d) (hi : d < 128)
      (bound : (128 : Int) - 2^(w-1) ≤ d) :
      Signed w ((d : Int)-128) [UInt8.ofNat d]
  | more (w d : Nat) (n : Int) (width : 7 < w) (digit : d < 128)
      (tail : Signed (w-7) n bs) :
      Signed w (128*n+d) (UInt8.ofNat (128+d) :: bs)

inductive Sequence (R : α → Bytes → Prop) : List α → Bytes → Prop where
  | nil : Sequence R [] []
  | cons (head : R a p) (tail : Sequence R as q) : Sequence R (a::as) (p++q)

inductive Vector (R : α → Bytes → Prop) : List α → Bytes → Prop where
  | intro (count : Unsigned 32 xs.length p) (items : Sequence R xs q) :
      Vector R xs (p++q)

/-- Consuming exactly a production in any trailing byte context. -/
def Reads (R : α → Bytes → Prop) (a : α) (input rest : Bytes) : Prop :=
  ∃ consumed, R a consumed ∧ input = consumed ++ rest

theorem reads (h : R a bytes) (suffix : Bytes) : Reads R a (bytes++suffix) suffix :=
  ⟨bytes, h, rfl⟩

theorem sequence_cons_reads (head : R a p) (tail : Sequence R as q) (suffix : Bytes) :
    Reads (Sequence R) (a::as) (p++q++suffix) suffix :=
  reads (.cons head tail) suffix

theorem reads_complete : Reads R a bytes [] ↔ R a bytes := by
  constructor
  · rintro ⟨p, h, rfl⟩; simpa using h
  · intro h; simpa using reads h []

inductive ValType : ValueType → Bytes → Prop where
  | i32 : ValType .i32 [0x7f]
  | i64 : ValType .i64 [0x7e]
  | f32 : ValType .f32 [0x7d]
  | f64 : ValType .f64 [0x7c]
  | v128 : ValType .v128 [0x7b]
  | funcref : ValType .funcref [0x70]
  | externref : ValType .externref [0x6f]

inductive FunctionType : FuncType → Bytes → Prop where
  | intro (params : Vector ValType ps p) (results : Vector ValType rs r) :
      FunctionType ⟨ps,rs⟩ (0x60 :: (p++r))

inductive Instruction : Instr → Bytes → Prop where
  | const (value : Signed 32 n b) : Instruction (.const (BitVec.ofInt 32 n)) (0x41::b)
  | get (index : Unsigned 32 n b) : Instruction (.get n) (0x20::b)
  | set (index : Unsigned 32 n b) : Instruction (.set n) (0x21::b)
  | eqz : Instruction .eqz [0x45]
  | and : Instruction (.binary .and) [0x71]
  | or : Instruction (.binary .or) [0x72]
  | xor : Instruction (.binary .xor) [0x73]
  | add : Instruction (.binary .add) [0x6a]
  | select : Instruction .select [0x1b]

inductive Expression : List Instr → Bytes → Prop where
  | intro (code : Sequence Instruction is b) : Expression is (b++[0x0b])

inductive LocalGroup : Nat × ValueType → Bytes → Prop where
  | intro (count : Unsigned 32 n p) (type : ValType t q) : LocalGroup (n,t) (p++q)

inductive Locals : List ValueType → Bytes → Prop where
  | intro (groups : Vector LocalGroup gs bytes)
      (bound : (gs.flatMap fun g => List.replicate g.1 g.2).length < 2^32) :
      Locals (gs.flatMap fun g => List.replicate g.1 g.2) bytes

/-- Length-delimited payload; both the byte count and complete payload are retained. -/
inductive Sized (R : α → Bytes → Prop) : α → Bytes → Prop where
  | intro (size : Unsigned 32 body.length p) (payload : R a body) : Sized R a (p++body)

inductive FunctionBody : List ValueType × List Instr → Bytes → Prop where
  | intro (locals : Locals ls p) (expr : Expression is q) : FunctionBody (ls,is) (p++q)

/-- The selected ASCII export name is also its UTF-8 encoding. -/
inductive Name : String → Bytes → Prop where
  | run (size : Unsigned 32 3 p) : Name "run" (p++[0x72,0x75,0x6e])

inductive Export : String × Nat → Bytes → Prop where
  | func (name : Name s p) (index : Unsigned 32 n q) : Export (s,n) (p++(0x00::q))

inductive Section (id : UInt8) (R : α → Bytes → Prop) : α → Bytes → Prop where
  | intro (payload : Sized R a b) : Section id R a (id::b)

/-- Exact single-function module decoding. Function and code vectors have the
same length, the function refers to its sole type, and run exports index zero.
There are no unconsumed bytes or hidden custom/other sections. -/
inductive ModuleBytes : Module → Bytes → Prop where
  | intro (types : Section 1 (Vector FunctionType) [m.type] t)
      (functions : Section 3 (Vector (Unsigned 32)) [0] f)
      (exports : Section 7 (Vector Export) [("run",0)] e)
      (code : Section 10 (Vector (Sized FunctionBody)) [(m.locals,m.body)] c) :
      ModuleBytes m ([0,0x61,0x73,0x6d,1,0,0,0] ++ t ++ f ++ e ++ c)


theorem Sequence.append (left : Sequence R xs p) (right : Sequence R ys q) :
    Sequence R (xs++ys) (p++q) := by
  induction left with
  | nil => simpa using right
  | cons head tail ih => simpa [List.append_assoc] using Sequence.cons head ih

theorem reads_sequence_cons (head : Reads R a input middle)
    (tail : Reads (Sequence R) as middle rest) : Reads (Sequence R) (a::as) input rest := by
  obtain ⟨p, hp, rfl⟩ := head
  obtain ⟨q, hq, rfl⟩ := tail
  exact ⟨p++q, .cons hp hq, by simp [List.append_assoc]⟩

end Applications.Wasm.Binary
