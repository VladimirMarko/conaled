import SquareKit.Internal.DependentFunctionNormalFormLaws

/-! Structural normalization for the existing base-domain function grammar. -/
namespace SquareKit.Internal.DependentFunctions
open DependentStructural (Base)

mutual
  def Dep.normal {n} {Γ : Ctx n} : Dep Γ → Normal.Dep Γ
    | .var v => .var v
    | .point => .point
    | .app f a => (Func.normal f).plug a
  def Func.normal {n} {Γ : Ctx n} : Func Γ → Normal.Func Γ
    | .var v => Normal.reflect v
    | .lam t => Dep.normal t
end

mutual
  theorem Dep.normal_sound : {n : Nat} → {Γ : Ctx n} → (t : Dep Γ) →
      DepEq t (Normal.Dep.embed t.normal)
    | _, _, .var _ => .refl _
    | _, _, .point => .refl _
    | _, _, .app f a => .trans (.app (Func.normal_sound f) a)
        (by simpa only [Dep.normal, Normal.Func.embed, Normal.Dep.embed_plug] using
          DepEq.beta (Normal.Dep.embed f.normal) a)
  theorem Func.normal_sound : {n : Nat} → {Γ : Ctx n} → (f : Func Γ) →
      FuncEq f (Normal.Func.embed f.normal)
    | _, _, .var v => .symm (.eta (.var v))
    | _, _, .lam t => .lam (Dep.normal_sound t)
end

mutual
  theorem Dep.normal_map : {n m : Nat} → {Γ : Ctx n} → {Δ : Ctx m} →
      (ρ : Ren Δ Γ) → (t : Dep Γ) →
      (ρ.depMap t).normal = t.normal.map ρ
    | _, _, _, _, _, .var _ => rfl
    | _, _, _, _, _, .point => rfl
    | _, _, _, _, ρ, .app f a => by
      simp only [Ren.depMap, Dep.normal, Func.normal_map ρ f,
        Normal.Dep.map_plug]
  theorem Func.normal_map : {n m : Nat} → {Γ : Ctx n} → {Δ : Ctx m} →
      (ρ : Ren Δ Γ) → (f : Func Γ) →
      (ρ.funcMap f).normal = f.normal.map ρ.lift
    | _, _, _, _, _, .var _ => rfl
    | _, _, _, _, ρ, .lam t => Dep.normal_map ρ.lift t
end

theorem Dep.normal_type {n} {Γ : Ctx n} (t : Dep Γ) :
    (Normal.Dep.embed t.normal).type = t.type := (DepEq.type t.normal_sound).symm

theorem Func.normal_type {n} {Γ : Ctx n} (f : Func Γ) :
    (Normal.Func.embed f.normal).type = f.type := (FuncEq.type f.normal_sound).symm

@[simp] theorem Normal.Dep.normal_embed {n} {Γ : Ctx n} (t : Normal.Dep Γ) :
    t.embed.normal = t := by cases t <;> rfl

@[simp] theorem Normal.Func.normal_embed {n} {Γ : Ctx n} (f : Normal.Func Γ) :
    (Normal.Func.embed f).normal = f := Normal.Dep.normal_embed f

end SquareKit.Internal.DependentFunctions
