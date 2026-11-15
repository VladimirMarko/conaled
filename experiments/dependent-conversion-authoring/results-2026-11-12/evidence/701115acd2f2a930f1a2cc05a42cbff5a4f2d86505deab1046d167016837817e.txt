import SquareKit.Internal.DependentFunctionLaws

/-! Public task data for a future trial, without task-specific equality solutions. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.ConversionTrial
open SquareKit.Internal.DependentFunctions
open SquareKit.Internal.DependentStructural (Base)

abbrev Γ : Ctx 1 := .function (.family (.base .nil) .zero) (.var 0)
abbrev parameter : Func Γ := .var .top
abbrev auxiliary : Dep Γ := .var (.function .top)

def widen : (k : Nat) → Ctx (k+1)
  | 0 => Γ
  | k+1 => .base (widen k)

def liftRen : (k : Nat) → Ren (widen k) Γ
  | 0 => Ren.id Γ
  | k+1 => Ren.comp (liftRen k) (Ren.weaken (widen k))

def negate : Sub Γ Γ where
  base i := .neg (.var i)
  dep
    | .function .top => auxiliary
    | .function (.family (.base v)) => nomatch v
  func
    | .top => parameter
    | .function (.family (.base v)) => nomatch v

theorem negate_typed : negate.Typed where
  dep
    | .function .top => rfl
    | .function (.family (.base v)) => nomatch v
  func
    | .top => rfl
    | .function (.family (.base v)) => nomatch v

theorem negate_nonidentity : negate ≠ Sub.id Γ := by
  intro h
  have he := congrArg (fun s : Sub Γ Γ => s.base 0) h
  cases he

def liftedNegate : (k : Nat) → Sub (widen k) (widen k)
  | 0 => negate
  | k+1 => (liftedNegate k).lift

theorem liftedNegate_typed (k : Nat) : (liftedNegate k).Typed := by
  induction k with
  | zero => exact negate_typed
  | succ k ih => exact ih.lift

def etaExpand {n : Nat} {Δ : Ctx n} (f : Func Δ) : Func Δ :=
  .lam (.app ((Ren.weaken Δ).funcMap f) (.var 0))

def expand {n : Nat} {Δ : Ctx n} : Nat → Func Δ → Func Δ
  | 0, f => f
  | k+1, f => etaExpand (expand k f)

def source (recipe : Nat) : Dep Γ := .app (expand recipe parameter) (.neg (.var 0))
def target : Dep Γ := .app parameter (.neg (.var 0))

def chain (k depth : Nat) : List (Sub (widen k) (widen k)) :=
  List.replicate depth (liftedNegate k)

def applyChain {n : Nat} {Δ : Ctx n} (ss : List (Sub Δ Δ)) (t : Dep Δ) : Dep Δ :=
  ss.foldl (fun t s => s.depSub t) t

def left (k recipe depth : Nat) : Dep (widen k) :=
  applyChain (chain k depth) ((liftRen k).depMap (source recipe))
def right (k depth : Nat) : Dep (widen k) :=
  applyChain (chain k depth) ((liftRen k).depMap target)

/-- Metric functions inspect the actual instantiated syntax, not recipe parameters. -/
def baseNodes {n : Nat} : Base n → Nat
  | .var _ => 1 | .zero => 1 | .neg a => baseNodes a + 1
mutual
  def depNodes {n : Nat} {Δ : Ctx n} : Dep Δ → Nat
    | .var _ => 1 | .point => 1 | .app f a => funcNodes f + baseNodes a + 1
  def funcNodes {n : Nat} {Δ : Ctx n} : Func Δ → Nat
    | .var _ => 1 | .lam t => depNodes t + 1
end
mutual
  def depRedexDepth {n : Nat} {Δ : Ctx n} : Dep Δ → Nat
    | .var _ => 0 | .point => 0
    | .app (.var _) _ => 0
    | .app (.lam t) _ => depRedexDepth t + 1
  def funcRedexDepth {n : Nat} {Δ : Ctx n} : Func Δ → Nat
    | .var _ => 0 | .lam t => depRedexDepth t
end

def contextWidth : {n : Nat} → Ctx n → Nat
  | _, .nil => 0
  | _, .base c => contextWidth c+1
  | _, .family c _ => contextWidth c
  | _, .function c _ => contextWidth c

def indexDepth {n : Nat} : Base n → Nat
  | .var _ => 0 | .zero => 0 | .neg a => indexDepth a+1

def metrics (k recipe depth : Nat) : List Nat :=
  [contextWidth (widen k), depNodes (left k recipe depth), depNodes (right k depth),
   depRedexDepth (left k recipe depth), (chain k depth).length,
   baseNodes (left k recipe depth).type, indexDepth (left k recipe depth).type]
end Examples.ConversionTrial
