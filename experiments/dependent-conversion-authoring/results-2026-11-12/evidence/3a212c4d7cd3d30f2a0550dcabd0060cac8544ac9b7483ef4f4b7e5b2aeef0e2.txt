import SquareKit.Internal.DependentFunctions

/-! Experimental typing and conversion for the first-order dependent function
source. Type inference is structural, so a term has one inferred type. A typed
assignment checks the inferred types of every assigned variable. -/
namespace SquareKit.Internal.DependentFunctions
open DependentStructural (Base)

namespace Ren
variable {n m} {Γ : Ctx n} {Δ : Ctx m}
structure Typed (ρ : Ren Δ Γ) : Prop where
  dep : ∀ v, (ρ.dep v).type = v.type.sub ρ.base
  func : ∀ v, (ρ.func v).type = v.type.sub (up ρ.base)

theorem Typed.lift {ρ : Ren Δ Γ} (h : Typed ρ) : Typed ρ.lift where
  dep | .base v => (congrArg Base.wk (h.dep v)).trans (wk_up v.type ρ.base).symm
  func
    | .base v => by
        change ((ρ.func v).type.sub (up (Ren.weaken Δ).base)) =
          (v.type.sub (up (Ren.weaken Γ).base)).sub (up (up ρ.base))
        rw [h.func, Base.sub_comp, Base.sub_comp]
        congr 1
        rw [up_comp, up_comp]
        rfl

theorem typed_weaken (Γ : Ctx n) : Typed (weaken Γ) := ⟨fun _ => rfl, fun _ => rfl⟩

mutual
 theorem depMap_type {n m} {Γ : Ctx n} {Δ : Ctx m} (ρ : Ren Δ Γ) (h : Typed ρ)
         (t : Dep Γ) : (ρ.depMap t).type = t.type.sub ρ.base := by
   cases t with
   | var v => exact h.dep v
   | point => rfl
   | app f a =>
     change instantiate (ρ.funcMap f).type (a.sub ρ.base) = _
     rw [funcMap_type ρ h f]
     exact (instantiate_sub f.type a ρ.base).symm
 theorem funcMap_type {n m} {Γ : Ctx n} {Δ : Ctx m} (ρ : Ren Δ Γ) (h : Typed ρ)
     (t : Func Γ) : (ρ.funcMap t).type = t.type.sub (up ρ.base) := by
   cases t with
   | var v => exact h.func v
   | lam t => exact depMap_type ρ.lift h.lift t
end
end Ren

namespace Sub
variable {n m k} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx k}
structure Typed (σ : Sub Δ Γ) : Prop where
  dep : ∀ v, (σ.dep v).type = v.type.sub σ.base
  func : ∀ v, (σ.func v).type = v.type.sub (up σ.base)

theorem Typed.lift {σ : Sub Δ Γ} (h : Typed σ) : Typed σ.lift where
  dep
    | .base v => by
        exact (Ren.depMap_type (Ren.weaken Δ) (Ren.typed_weaken Δ) (σ.dep v)).trans
          ((congrArg Base.wk (h.dep v)).trans (wk_up v.type σ.base).symm)
  func
    | .base v => by
        rw [show (σ.lift.func (.base v)).type = (σ.func v).type.sub (up (Ren.weaken Δ).base) from
          Ren.funcMap_type _ (Ren.typed_weaken Δ) (σ.func v)]
        change _ = (v.type.sub (up (Ren.weaken Γ).base)).sub (up (up σ.base))
        rw [h.func, Base.sub_comp, Base.sub_comp]
        congr 1
        rw [up_comp, up_comp]
        rfl
mutual
 theorem depSub_type {n m} {Γ : Ctx n} {Δ : Ctx m} (σ : Sub Δ Γ) (h : Typed σ)
         (t : Dep Γ) : (σ.depSub t).type = t.type.sub σ.base := by
   cases t with
   | var v => exact h.dep v
   | point => rfl
   | app f a =>
     change instantiate (σ.funcSub f).type (a.sub σ.base) = _
     rw [funcSub_type σ h f]
     exact (instantiate_sub f.type a σ.base).symm
 theorem funcSub_type {n m} {Γ : Ctx n} {Δ : Ctx m} (σ : Sub Δ Γ) (h : Typed σ)
     (t : Func Γ) : (σ.funcSub t).type = t.type.sub (up σ.base) := by
   cases t with
   | var v => exact h.func v
   | lam t => exact depSub_type σ.lift h.lift t
end

theorem typed_id (Γ : Ctx n) : Typed (id Γ) where
  dep v := (Base.sub_id v.type).symm
  func v := by change v.type = v.type.sub (up Base.var); rw [up_id, Base.sub_id]

theorem Typed.comp {σ : Sub Δ Γ} {τ : Sub Ξ Δ} (h : Typed σ) (k : Typed τ) :
    Typed (comp σ τ) where
  dep v := (depSub_type τ k (σ.dep v)).trans
    ((congrArg (Base.sub τ.base) (h.dep v)).trans (Base.sub_comp _ _ _))
  func v := by
    change (τ.funcSub (σ.func v)).type = _
    rw [funcSub_type τ k, h.func, Base.sub_comp, up_comp]
    rfl

def plug (Γ : Ctx n) (a : Base n) : Sub Γ (.base Γ) where
  base := Fin.cases a Base.var
  dep | .base v => .var v
  func | .base v => .var v

theorem typed_plug (Γ : Ctx n) (a : Base n) : Typed (plug Γ a) where
  dep
    | .base v => by
        change v.type = v.type.wk.sub (Fin.cases a Base.var)
        rw [DependentStructural.Sub.wk_sub, Base.sub_id]
  func
    | .base v => by
        change v.type = (v.type.sub (up (Ren.weaken Γ).base)).sub (up (Fin.cases a Base.var))
        rw [Base.sub_comp, up_comp]
        change v.type = v.type.sub (up Base.var)
        rw [up_id, Base.sub_id]
end Sub

inductive Ty (n : Nat) where
  | base : Ty n
  | family : Base n → Ty n
  | pi : Base (n+1) → Ty n

abbrev Tm {n} (Γ : Ctx n) : Ty n → Type
  | .base => Base n
  | .family b => {t : Dep Γ // t.type = b}
  | .pi b => {t : Func Γ // t.type = b}

def convert {n} {Γ : Ctx n} {A B : Ty n} (h : A = B) (t : Tm Γ A) : Tm Γ B := h ▸ t

theorem convert_trans {n} {Γ : Ctx n} {A B D : Ty n} (h : A = B) (k : B = D) (t : Tm Γ A) :
    convert k (convert h t) = convert (h.trans k) t := by cases h; cases k; rfl

end SquareKit.Internal.DependentFunctions
