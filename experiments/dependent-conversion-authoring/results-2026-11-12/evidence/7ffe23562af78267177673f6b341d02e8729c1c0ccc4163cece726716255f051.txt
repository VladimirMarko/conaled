import SquareKit.Internal.DependentStructural
/-! Experimental first-order dependent function syntax. Function domains are the
primitive base sort; results are primitive family fibers with a bound base index.
The data contain only algebraic syntax and finite variable assignments. -/
namespace SquareKit.Internal.DependentFunctions
open DependentStructural (Base)

def up {n m} (ρ : Fin n → Base m) : Fin (n+1) → Base (m+1) :=
  Fin.cases (.var 0) (fun i => (ρ i).wk)

def instantiate {n} (b : Base (n+1)) (a : Base n) := b.sub (Fin.cases a Base.var)

inductive Ctx : Nat → Type where
  | nil : Ctx 0
  | base {n} : Ctx n → Ctx (n+1)
  | family {n} : Ctx n → Base n → Ctx n
  | function {n} : Ctx n → Base (n+1) → Ctx n

inductive DVar : {n : Nat} → Ctx n → Type where
  | top {n} {Γ : Ctx n} {b : Base n} : DVar (.family Γ b)
  | family {n} {Γ : Ctx n} {b : Base n} : DVar Γ → DVar (.family Γ b)
  | function {n} {Γ : Ctx n} {b : Base (n+1)} : DVar Γ → DVar (.function Γ b)
  | base {n} {Γ : Ctx n} : DVar Γ → DVar (.base Γ)

inductive FVar : {n : Nat} → Ctx n → Type where
  | top {n} {Γ : Ctx n} {b : Base (n+1)} : FVar (.function Γ b)
  | family {n} {Γ : Ctx n} {b : Base n} : FVar Γ → FVar (.family Γ b)
  | function {n} {Γ : Ctx n} {b : Base (n+1)} : FVar Γ → FVar (.function Γ b)
  | base {n} {Γ : Ctx n} : FVar Γ → FVar (.base Γ)

def DVar.type {n} {Γ : Ctx n} : DVar Γ → Base n
  | .top (b := b) => b
  | .family v => v.type
  | .function v => v.type
  | .base v => v.type.wk

def FVar.type {n} {Γ : Ctx n} : FVar Γ → Base (n+1)
  | .top (b := b) => b
  | .family v => v.type
  | .function v => v.type
  | .base v => v.type.sub (up (fun i => .var i.succ))

mutual
inductive Dep : {n : Nat} → Ctx n → Type where
  | var {n} {Γ : Ctx n} : DVar Γ → Dep Γ
  | point {n} {Γ : Ctx n} : Dep Γ
  | app {n} {Γ : Ctx n} : Func Γ → Base n → Dep Γ
inductive Func : {n : Nat} → Ctx n → Type where
  | var {n} {Γ : Ctx n} : FVar Γ → Func Γ
  | lam {n} {Γ : Ctx n} : Dep (.base Γ) → Func Γ
end
mutual
 def Dep.type {n} {Γ : Ctx n} : Dep Γ → Base n
   | .var v => v.type
   | .point => .zero
   | .app f a => instantiate f.type a
 def Func.type {n} {Γ : Ctx n} : Func Γ → Base (n+1)
   | .var v => v.type
   | .lam t => t.type
end


/-- Variable maps may substitute base expressions but preserve dependent and
function variables. They implement weakening without touching bound variables. -/
structure Ren {m n} (Δ : Ctx m) (Γ : Ctx n) where
  base : Fin n → Base m
  dep : DVar Γ → DVar Δ
  func : FVar Γ → FVar Δ

namespace Ren
variable {n m k} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx k}
def lift (ρ : Ren Δ Γ) : Ren (.base Δ) (.base Γ) where
  base := up ρ.base
  dep | .base v => .base (ρ.dep v)
  func | .base v => .base (ρ.func v)
def weaken (Γ : Ctx n) : Ren (.base Γ) Γ where
  base i := .var i.succ
  dep := .base
  func := .base
mutual
 def depMap {n m} {Γ : Ctx n} {Δ : Ctx m} (ρ : Ren Δ Γ) : Dep Γ → Dep Δ
   | .var v => .var (ρ.dep v)
   | .point => .point
   | .app f a => .app (funcMap ρ f) (a.sub ρ.base)
 def funcMap {n m} {Γ : Ctx n} {Δ : Ctx m} (ρ : Ren Δ Γ) : Func Γ → Func Δ
   | .var v => .var (ρ.func v)
   | .lam t => .lam (depMap ρ.lift t)
end
def id (Γ : Ctx n) : Ren Γ Γ where
  base := Base.var
  dep v := v
  func v := v
def comp (ρ : Ren Δ Γ) (τ : Ren Ξ Δ) : Ren Ξ Γ where
  base i := (ρ.base i).sub τ.base
  dep v := τ.dep (ρ.dep v)
  func v := τ.func (ρ.func v)
@[ext] theorem ext {ρ τ : Ren Δ Γ} (hb : ρ.base = τ.base) (hd : ρ.dep = τ.dep)
    (hf : ρ.func = τ.func) : ρ = τ := by
  cases ρ; cases τ; cases hb; cases hd; cases hf; rfl
end Ren

theorem up_id {n} : up (@Base.var n) = Base.var := by
  funext i; exact Fin.cases rfl (fun _ => rfl) i

theorem wk_up {n m} (b : Base n) (ρ : Fin n → Base m) :
    b.wk.sub (up ρ) = (b.sub ρ).wk := by
  simp only [Base.wk, Base.sub_comp]
  rfl

theorem up_comp {n m k} (ρ : Fin n → Base m) (τ : Fin m → Base k) :
    (fun i => (up ρ i).sub (up τ)) = up (fun i => (ρ i).sub τ) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact wk_up _ _

theorem instantiate_sub {n m} (b : Base (n+1)) (a : Base n) (ρ : Fin n → Base m) :
    (instantiate b a).sub ρ = instantiate (b.sub (up ρ)) (a.sub ρ) := by
  simp only [instantiate, Base.sub_comp]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact ((DependentStructural.Sub.wk_sub (ρ j) Base.var (a.sub ρ)).trans
    (Base.sub_id (ρ j))).symm

namespace Ren
variable {n m k} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx k}
theorem lift_id (Γ : Ctx n) : (id Γ).lift = id (.base Γ) := by
  apply ext up_id <;> funext v <;> cases v <;> rfl

theorem lift_comp (ρ : Ren Δ Γ) (τ : Ren Ξ Δ) :
    (comp ρ τ).lift = comp ρ.lift τ.lift := by
  apply ext (up_comp ρ.base τ.base).symm <;> funext v <;> cases v <;> rfl

mutual
 theorem depMap_id : {n : Nat} → {Γ : Ctx n} → (t : Dep Γ) → depMap (id Γ) t = t
   | _, _, .var _ => rfl
   | _, _, .point => rfl
   | _, _, .app f a =>
     (congrArg (fun g => Dep.app g _) (funcMap_id f)).trans (congrArg (Dep.app f) (Base.sub_id a))
 theorem funcMap_id : {n : Nat} → {Γ : Ctx n} → (t : Func Γ) → funcMap (id Γ) t = t
   | _, _, .var _ => rfl
   | _, Γ, .lam t => by
     change Func.lam (depMap (id Γ).lift t) = Func.lam t
     rw [lift_id, depMap_id t]
end

mutual
 theorem depMap_comp {n m k} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx k} (ρ : Ren Δ Γ) (τ : Ren Ξ Δ) (t : Dep Γ) :
     depMap τ (depMap ρ t) = depMap (comp ρ τ) t := by
   cases t with
   | var => rfl
   | point => rfl
   | app f a => simp only [depMap, funcMap_comp ρ τ f, Base.sub_comp]; rfl
 theorem funcMap_comp {n m k} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx k} (ρ : Ren Δ Γ) (τ : Ren Ξ Δ) (t : Func Γ) :
     funcMap τ (funcMap ρ t) = funcMap (comp ρ τ) t := by
   cases t with
   | var => rfl
   | lam t => simp only [funcMap, depMap_comp ρ.lift τ.lift t, lift_comp]
end
end Ren

structure Sub {m n} (Δ : Ctx m) (Γ : Ctx n) where
  base : Fin n → Base m
  dep : DVar Γ → Dep Δ
  func : FVar Γ → Func Δ

namespace Sub
variable {n m k} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx k}
def lift (σ : Sub Δ Γ) : Sub (.base Δ) (.base Γ) where
  base := up σ.base
  dep | .base v => (Ren.weaken Δ).depMap (σ.dep v)
  func | .base v => (Ren.weaken Δ).funcMap (σ.func v)
mutual
 def depSub {n m} {Γ : Ctx n} {Δ : Ctx m} (σ : Sub Δ Γ) : Dep Γ → Dep Δ
   | .var v => σ.dep v
   | .point => .point
   | .app f a => .app (funcSub σ f) (a.sub σ.base)
 def funcSub {n m} {Γ : Ctx n} {Δ : Ctx m} (σ : Sub Δ Γ) : Func Γ → Func Δ
   | .var v => σ.func v
   | .lam t => .lam (depSub σ.lift t)
end
def ofRen (ρ : Ren Δ Γ) : Sub Δ Γ where
  base := ρ.base
  dep v := .var (ρ.dep v)
  func v := .var (ρ.func v)
def id (Γ : Ctx n) := ofRen (Ren.id Γ)
def comp (σ : Sub Δ Γ) (τ : Sub Ξ Δ) : Sub Ξ Γ where
  base i := (σ.base i).sub τ.base
  dep v := τ.depSub (σ.dep v)
  func v := τ.funcSub (σ.func v)
@[ext] theorem ext {σ τ : Sub Δ Γ} (hb : σ.base = τ.base) (hd : σ.dep = τ.dep)
    (hf : σ.func = τ.func) : σ = τ := by
  cases σ; cases τ; cases hb; cases hd; cases hf; rfl

theorem lift_ofRen (ρ : Ren Δ Γ) : (ofRen ρ).lift = ofRen ρ.lift := by
  apply ext (σ := (ofRen ρ).lift) (τ := ofRen ρ.lift) rfl <;> funext v <;> cases v <;> rfl
mutual
 theorem depSub_ofRen {n m} {Γ : Ctx n} {Δ : Ctx m} (ρ : Ren Δ Γ) (t : Dep Γ) :
     depSub (ofRen ρ) t = ρ.depMap t := by
   cases t with
   | var => rfl
   | point => rfl
   | app f a => change Dep.app (funcSub (ofRen ρ) f) _ = _; rw [funcSub_ofRen ρ f]; rfl
 theorem funcSub_ofRen {n m} {Γ : Ctx n} {Δ : Ctx m} (ρ : Ren Δ Γ) (t : Func Γ) :
     funcSub (ofRen ρ) t = ρ.funcMap t := by
   cases t with
   | var => rfl
   | lam t => simp only [funcSub, Ren.funcMap, lift_ofRen, depSub_ofRen ρ.lift t]
end
@[simp] theorem depSub_id (t : Dep Γ) : depSub (id Γ) t = t :=
  (depSub_ofRen (Ren.id Γ) t).trans (Ren.depMap_id t)
@[simp] theorem funcSub_id (t : Func Γ) : funcSub (id Γ) t = t :=
  (funcSub_ofRen (Ren.id Γ) t).trans (Ren.funcMap_id t)

def pre (ρ : Ren Δ Γ) (σ : Sub Ξ Δ) : Sub Ξ Γ where
  base i := (ρ.base i).sub σ.base
  dep v := σ.dep (ρ.dep v)
  func v := σ.func (ρ.func v)
def post (σ : Sub Δ Γ) (ρ : Ren Ξ Δ) : Sub Ξ Γ where
  base i := (σ.base i).sub ρ.base
  dep v := ρ.depMap (σ.dep v)
  func v := ρ.funcMap (σ.func v)

theorem lift_pre (ρ : Ren Δ Γ) (σ : Sub Ξ Δ) : (pre ρ σ).lift = pre ρ.lift σ.lift := by
  apply ext (up_comp ρ.base σ.base).symm <;> funext v <;> cases v <;> rfl

theorem weaken_lift (ρ : Ren Δ Γ) :
    Ren.comp ρ (Ren.weaken Δ) = Ren.comp (Ren.weaken Γ) ρ.lift := by
  apply Ren.ext rfl <;> funext v <;> rfl

theorem lift_post (σ : Sub Δ Γ) (ρ : Ren Ξ Δ) : (post σ ρ).lift = post σ.lift ρ.lift := by
  apply ext (up_comp σ.base ρ.base).symm
  · funext v; cases v with
    | base v =>
      exact (Ren.depMap_comp ρ (Ren.weaken Ξ) (σ.dep v)).trans
          ((congrArg (fun r => r.depMap (σ.dep v)) (weaken_lift ρ)).trans
            (Ren.depMap_comp (Ren.weaken Δ) ρ.lift (σ.dep v)).symm)
  · funext v; cases v with
    | base v =>
      exact (Ren.funcMap_comp ρ (Ren.weaken Ξ) (σ.func v)).trans
          ((congrArg (fun r => r.funcMap (σ.func v)) (weaken_lift ρ)).trans
            (Ren.funcMap_comp (Ren.weaken Δ) ρ.lift (σ.func v)).symm)
mutual
 theorem depSub_pre {n m k} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx k}
     (ρ : Ren Δ Γ) (σ : Sub Ξ Δ) (t : Dep Γ) :
     σ.depSub (ρ.depMap t) = (pre ρ σ).depSub t := by
   cases t with
   | var => rfl
   | point => rfl
   | app f a => simp only [Ren.depMap, depSub, funcSub_pre ρ σ f, Base.sub_comp]; rfl
 theorem funcSub_pre {n m k} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx k}
     (ρ : Ren Δ Γ) (σ : Sub Ξ Δ) (t : Func Γ) :
     σ.funcSub (ρ.funcMap t) = (pre ρ σ).funcSub t := by
   cases t with
   | var => rfl
   | lam t => simp only [Ren.funcMap, funcSub, depSub_pre ρ.lift σ.lift t, lift_pre]
end
mutual
 theorem depSub_post {n m k} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx k}
     (σ : Sub Δ Γ) (ρ : Ren Ξ Δ) (t : Dep Γ) :
     ρ.depMap (σ.depSub t) = (post σ ρ).depSub t := by
   cases t with
   | var => rfl
   | point => rfl
   | app f a => simp only [Ren.depMap, depSub, funcSub_post σ ρ f, Base.sub_comp]; rfl
 theorem funcSub_post {n m k} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx k}
     (σ : Sub Δ Γ) (ρ : Ren Ξ Δ) (t : Func Γ) :
     ρ.funcMap (σ.funcSub t) = (post σ ρ).funcSub t := by
   cases t with
   | var => rfl
   | lam t => simp only [Ren.funcMap, funcSub, depSub_post σ.lift ρ.lift t, lift_post]
end

theorem pre_weaken_lift (σ : Sub Δ Γ) : pre (Ren.weaken Γ) σ.lift = post σ (Ren.weaken Δ) := rfl

theorem lift_comp (σ : Sub Δ Γ) (τ : Sub Ξ Δ) : (comp σ τ).lift = comp σ.lift τ.lift := by
  apply ext (up_comp σ.base τ.base).symm
  · funext v; cases v with
    | base v =>
      exact (depSub_post τ (Ren.weaken Ξ) (σ.dep v)).trans
          (depSub_pre (Ren.weaken Δ) τ.lift (σ.dep v)).symm
  · funext v; cases v with
    | base v =>
      exact (funcSub_post τ (Ren.weaken Ξ) (σ.func v)).trans
          (funcSub_pre (Ren.weaken Δ) τ.lift (σ.func v)).symm
mutual
 theorem depSub_comp {n m k} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx k}
     (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (t : Dep Γ) :
     τ.depSub (σ.depSub t) = (comp σ τ).depSub t := by
   cases t with
   | var => rfl
   | point => rfl
   | app f a => simp only [depSub, funcSub_comp σ τ f, Base.sub_comp]; rfl
 theorem funcSub_comp {n m k} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx k}
     (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (t : Func Γ) :
     τ.funcSub (σ.funcSub t) = (comp σ τ).funcSub t := by
   cases t with
   | var => rfl
   | lam t => simp only [funcSub, depSub_comp σ.lift τ.lift t, lift_comp]
end
end Sub

end SquareKit.Internal.DependentFunctions
