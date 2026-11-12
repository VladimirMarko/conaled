import SquareKit.Internal.DependentFunctionLaws

/-! Beta-normal dependent terms and eta-long function bodies for the existing
base-domain grammar. Base expressions retain their literal source syntax. -/
namespace SquareKit.Internal.DependentFunctions
open DependentStructural (Base)

namespace Normal

inductive Dep : {n : Nat} → Ctx n → Type where
  | var {n} {Γ : Ctx n} : DVar Γ → Dep Γ
  | point {n} {Γ : Ctx n} : Dep Γ
  | app {n} {Γ : Ctx n} : FVar Γ → Base n → Dep Γ

/-- An eta-long function is its normal body under one fresh base binder. -/
abbrev Func {n} (Γ : Ctx n) := Dep (.base Γ)

def Dep.embed {n} {Γ : Ctx n} : Dep Γ → DependentFunctions.Dep Γ
  | .var v => .var v
  | .point => .point
  | .app f a => .app (.var f) a

def Func.embed {n} {Γ : Ctx n} (f : Func Γ) : DependentFunctions.Func Γ :=
  .lam (Dep.embed f)

def Dep.map {n m} {Γ : Ctx n} {Δ : Ctx m} (ρ : Ren Δ Γ) : Dep Γ → Dep Δ
  | .var v => .var (ρ.dep v)
  | .point => .point
  | .app f a => .app (ρ.func f) (a.sub ρ.base)

/-- Unlike an arbitrary substitution, base plugging keeps dependent/function
variables as variables, so it acts directly on normal forms. -/
def plugRen {n} (Γ : Ctx n) (a : Base n) : Ren Γ (.base Γ) where
  base := Fin.cases a Base.var
  dep | .base v => v
  func | .base v => v

def Dep.plug {n} {Γ : Ctx n} (t : Dep (.base Γ)) (a : Base n) : Dep Γ :=
  t.map (plugRen Γ a)

def reflect {n} {Γ : Ctx n} (f : FVar Γ) : Func Γ := .app (.base f) (.var 0)

end Normal
end SquareKit.Internal.DependentFunctions
