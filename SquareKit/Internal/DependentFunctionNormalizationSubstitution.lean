import SquareKit.Internal.DependentFunctionNormalization

/-! Substitution acts on canonical forms by replacing their free heads and
renormalizing the resulting applications. -/
namespace SquareKit.Internal.DependentFunctions
open DependentStructural (Base)
namespace Normal
variable {n m : Nat} {Γ : Ctx n} {Δ : Ctx m}

def Dep.sub (σ : Sub Δ Γ) : Dep Γ → Dep Δ
  | .var v => (σ.dep v).normal
  | .point => .point
  | .app f a => (σ.func f).normal.plug (a.sub σ.base)

theorem Dep.sub_plug (σ : Sub Δ Γ) (t : Dep (.base Γ)) (a : Base n) :
    (t.plug a).sub σ = (t.sub σ.lift).plug (a.sub σ.base) := by
  cases t with
  | var v =>
    cases v with
    | base v =>
      change (σ.dep v).normal = ((Ren.weaken Δ).depMap (σ.dep v)).normal.plug (a.sub σ.base)
      rw [DependentFunctions.Dep.normal_map, Dep.plug_weaken]
  | point => rfl
  | app f b =>
    cases f with
    | base f =>
      simp only [Dep.plug, Dep.map, plugRen, Dep.sub, Sub.lift,
        DependentFunctions.Func.normal_map]
      change (σ.func f).normal.plug ((instantiate b a).sub σ.base) =
        (((σ.func f).normal.map (Ren.weaken Δ).lift).plug (b.sub (up σ.base))).plug
          (a.sub σ.base)
      rw [Dep.double_plug, instantiate_sub]

theorem reflect_sub (σ : Sub Δ Γ) (f : FVar Γ) :
    (reflect f).sub σ.lift = (σ.func f).normal := by
  simp only [reflect, Dep.sub, Sub.lift, DependentFunctions.Func.normal_map]
  exact Dep.eta_plug _
end Normal

mutual
  theorem Dep.normal_sub : {n m : Nat} → {Γ : Ctx n} → {Δ : Ctx m} →
      (σ : Sub Δ Γ) → (t : Dep Γ) →
      (σ.depSub t).normal = t.normal.sub σ
    | _, _, _, _, _, .var _ => rfl
    | _, _, _, _, _, .point => rfl
    | _, _, _, _, σ, .app f a => by
      simp only [Sub.depSub, Dep.normal, Func.normal_sub σ f, Normal.Dep.sub_plug]
  theorem Func.normal_sub : {n m : Nat} → {Γ : Ctx n} → {Δ : Ctx m} →
      (σ : Sub Δ Γ) → (f : Func Γ) →
      (σ.funcSub f).normal = f.normal.sub σ.lift
    | _, _, _, _, σ, .var f => (Normal.reflect_sub σ f).symm
    | _, _, _, _, σ, .lam t => Dep.normal_sub σ.lift t
end
end SquareKit.Internal.DependentFunctions
