import Compiler
import Applications.FRP.Indefinite

/-! A finite source subset with a structural embedding into the existing source
language. Canonical Boolean representations have fixed shape, including both
payload slots of every sum. No shared compiler target gains an operation. -/
namespace FRPSpec.FiniteSum
open Applications.Circuits

inductive Ty where
  | bool | unit
  | prod : Ty → Ty → Ty
  | sum : Ty → Ty → Ty
  deriving DecidableEq, Repr

@[reducible] def Ty.source : Ty → CategoricalCompiler.Ty
  | .bool => .base
  | .unit => .unit
  | .prod a b => .prod a.source b.source
  | .sum a b => .sum a.source b.source

abbrev Value (a : Ty) := CategoricalCompiler.Val Bool a.source

@[reducible] def Ty.storage : Ty → FirstOrderCompiler.Ty
  | .bool => .base
  | .unit => .unit
  | .prod a b => .prod a.storage b.storage
  | .sum a b => .prod .base (.prod a.storage b.storage)

abbrev Bits (a : Ty) := FirstOrderCompiler.Val Bool a.storage

def zero : (a : FirstOrderCompiler.Ty) → FirstOrderCompiler.Val Bool a
  | .base => false
  | .unit => ()
  | .prod a b => (zero a,zero b)

instance bitsDecidableEq : (a : FirstOrderCompiler.Ty) → DecidableEq (FirstOrderCompiler.Val Bool a)
  | .base => inferInstance
  | .unit => inferInstance
  | .prod a b => @instDecidableEqProd _ _ (bitsDecidableEq a) (bitsDecidableEq b)

def encode : {a : Ty} → Value a → Bits a
  | .bool, b => b
  | .unit, _ => ()
  | .prod _ _, (x,y) => (encode x,encode y)
  | .sum _ b, .inl x => (false,(encode x,zero b.storage))
  | .sum a _, .inr y => (true,(zero a.storage,encode y))

/-- Total internal observation. External admission additionally checks canonicality. -/
def observe : (a : Ty) → Bits a → Value a
  | .bool, b => b
  | .unit, _ => ()
  | .prod a b, (x,y) => (observe a x,observe b y)
  | .sum a b, (tag,(x,y)) => if tag then .inr (observe b y) else .inl (observe a x)

@[simp] theorem observe_encode (a : Ty) (x : Value a) : observe a (encode x) = x := by
  induction a with
  | bool => rfl
  | unit => cases x; rfl
  | prod a b ha hb => cases x; simp [encode, observe, ha, hb]
  | sum a b ha hb => cases x <;> simp [encode, observe, ha, hb]

/-- Exactly the canonical encodings; inactive slots cannot carry hidden state. -/
def Valid (a : Ty) (bits : Bits a) : Prop := encode (observe a bits) = bits
instance (a : Ty) (bits : Bits a) : Decidable (Valid a bits) :=
  inferInstanceAs (Decidable (encode (observe a bits) = bits))

def admit (a : Ty) (bits : Bits a) : Option (Value a) :=
  if Valid a bits then some (observe a bits) else none

@[simp] theorem valid_encode (a : Ty) (x : Value a) : Valid a (encode x) := by
  simp [Valid]
@[simp] theorem admit_encode (a : Ty) (x : Value a) : admit a (encode x) = some x := by
  simp [admit]

theorem admit_iff (a : Ty) (bits : Bits a) (x : Value a) :
    admit a bits = some x ↔ bits = encode x := by
  unfold admit
  split
  next h => simp only [Option.some.injEq]; constructor
            · intro e; rw [← e]; exact h.symm
            · intro e; rw [e, observe_encode]
  next h => simp only [reduceCtorEq, false_iff]; intro e
            apply h; rw [e]; exact valid_encode a x

theorem reject_iff (a : Ty) (bits : Bits a) : admit a bits = none ↔ ¬ Valid a bits := by
  simp [admit]

/-- Exact retained Boolean storage, including the tag and inactive payload. -/
@[simp] theorem sum_cells (a b : Ty) :
    cells (Ty.sum a b).storage = 1 + (cells a.storage + cells b.storage) := rfl

inductive Prim : CategoricalCompiler.Ty → CategoricalCompiler.Ty → Type where
  | constant : Bool → Prim .unit .base
  | test : Prim .base (.sum .unit .unit)
  | not : Prim .base .base
  | nand : Prim (.prod .base .base) .base

def meaning : {a b : CategoricalCompiler.Ty} → Prim a b → CategoricalCompiler.Val Bool a → CategoricalCompiler.Val Bool b
  | _, _, .constant b, _ => b
  | _, _, .test, b => if b then .inr () else .inl ()
  | _, _, .not, b => !b
  | _, _, .nand, (x,y) => !(x && y)

abbrev Context := List Ty
abbrev sourceContext (Γ : Context) := Γ.map Ty.source
abbrev storageContext (Γ : Context) := Γ.map Ty.storage

inductive Var : Context → Ty → Type where
  | here : Var (a :: Γ) a
  | there : Var Γ a → Var (b :: Γ) a

def Var.source : Var Γ a → CategoricalCompiler.Var (sourceContext Γ) a.source
  | .here => .here
  | .there v => .there v.source

/-- Only total finite primitives are admitted; arrows and recursion are absent. -/
inductive Term : Context → Ty → Type where
  | var : Var Γ a → Term Γ a
  | unit : Term Γ .unit
  | pair : Term Γ a → Term Γ b → Term Γ (.prod a b)
  | fst : Term Γ (.prod a b) → Term Γ a
  | snd : Term Γ (.prod a b) → Term Γ b
  | letE : Term Γ a → Term (a :: Γ) b → Term Γ b
  | inl : Term Γ a → Term Γ (.sum a b)
  | inr : Term Γ b → Term Γ (.sum a b)
  | caseE : Term Γ (.sum a b) → Term (a :: Γ) c → Term (b :: Γ) c → Term Γ c
  | constant : Bool → Term Γ .bool
  | test : Term Γ .bool → Term Γ (.sum .unit .unit)
  | not : Term Γ .bool → Term Γ .bool
  | nand : Term Γ (.prod .bool .bool) → Term Γ .bool

def Term.source : Term Γ a → CategoricalCompiler.Term Prim (sourceContext Γ) a.source
  | .var v => .var v.source
  | .unit => .unit
  | .pair t u => .pair t.source u.source
  | .fst t => .fst t.source
  | .snd t => .snd t.source
  | .letE t u => .letE t.source u.source
  | .inl t => .inl t.source
  | .inr t => .inr t.source
  | .caseE s l r => .caseE s.source l.source r.source
  | .constant b => .prim (.constant b) .unit
  | .test t => .prim .test t.source
  | .not t => .prim .not t.source
  | .nand t => .prim .nand t.source

abbrev Env (Γ : Context) := CategoricalCompiler.Val Bool (CategoricalCompiler.context (sourceContext Γ))
abbrev StoredEnv (Γ : Context) := FirstOrderCompiler.Val Bool (FirstOrderCompiler.context (storageContext Γ))
def encodeEnv : {Γ : Context} → Env Γ → StoredEnv Γ
  | [], _ => ()
  | _ :: _, (ρ,x) => (encodeEnv ρ,encode x)

/-- Source meaning is the existing evaluator, not circuit execution. -/
def eval (t : Term Γ a) (ρ : Env Γ) : Value a := CategoricalCompiler.eval meaning t.source ρ

end FRPSpec.FiniteSum
