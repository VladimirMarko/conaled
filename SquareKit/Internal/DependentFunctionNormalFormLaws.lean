import SquareKit.Internal.DependentFunctionNormalForms

/-! Variable-preserving actions on the bounded normal forms. -/
namespace SquareKit.Internal.DependentFunctions
open DependentStructural (Base)
namespace Normal
variable {n m k : Nat} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx k}

@[simp] theorem Dep.map_id (t : Dep Γ) : t.map (Ren.id Γ) = t := by
  cases t <;> simp [Dep.map, Ren.id, Base.sub_id]

theorem Dep.map_comp (ρ : Ren Δ Γ) (τ : Ren Ξ Δ) (t : Dep Γ) :
    (t.map ρ).map τ = t.map (Ren.comp ρ τ) := by
  cases t <;> simp [Dep.map, Ren.comp, Base.sub_comp]

theorem Dep.embed_map (ρ : Ren Δ Γ) (t : Dep Γ) :
    (t.map ρ).embed = ρ.depMap t.embed := by cases t <;> rfl

theorem plug_ofRen (a : Base n) : Sub.ofRen (plugRen Γ a) = Sub.plug Γ a := by
  apply Sub.ext (σ := Sub.ofRen (plugRen Γ a)) (τ := Sub.plug Γ a) rfl <;> funext v <;> cases v <;> rfl

theorem Dep.embed_plug (t : Dep (.base Γ)) (a : Base n) :
    (t.plug a).embed = (Sub.plug Γ a).depSub t.embed := by
  rw [Dep.plug, Dep.embed_map, ← plug_ofRen]
  exact (Sub.depSub_ofRen _ _).symm

theorem weaken_plug (a : Base n) :
    Ren.comp (Ren.weaken Γ) (plugRen Γ a) = Ren.id Γ := by
  apply Ren.ext rfl <;> funext v <;> rfl

@[simp] theorem Dep.plug_weaken (t : Dep Γ) (a : Base n) :
    (t.map (Ren.weaken Γ)).plug a = t := by
  rw [Dep.plug, Dep.map_comp, weaken_plug, Dep.map_id]

@[simp] theorem reflect_plug (f : FVar Γ) (a : Base n) :
    (reflect f).plug a = .app f a := rfl

theorem plug_lift (ρ : Ren Δ Γ) (a : Base n) :
    Ren.comp ρ.lift (plugRen Δ (a.sub ρ.base)) = Ren.comp (plugRen Γ a) ρ := by
  apply Ren.ext
  · funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact DependentStructural.Sub.wk_sub (ρ.base j) Base.var (a.sub ρ.base) |>.trans
      (Base.sub_id _)
  · funext v; cases v; rfl
  · funext v; cases v; rfl

theorem Dep.map_plug (ρ : Ren Δ Γ) (t : Dep (.base Γ)) (a : Base n) :
    (t.plug a).map ρ = (t.map ρ.lift).plug (a.sub ρ.base) := by
  simp only [Dep.plug, Dep.map_comp, plug_lift]

theorem reflect_map (ρ : Ren Δ Γ) (f : FVar Γ) :
    (reflect f).map ρ.lift = reflect (ρ.func f) := rfl

theorem eta_ren :
    Ren.comp (Ren.weaken Γ).lift (plugRen (.base Γ) (.var 0)) = Ren.id (.base Γ) := by
  apply Ren.ext (ρ := Ren.comp (Ren.weaken Γ).lift (plugRen (.base Γ) (.var 0)))
    (τ := Ren.id (.base Γ))
  · funext i; refine Fin.cases rfl (fun j => rfl) i
  · funext v; cases v; rfl
  · funext v; cases v; rfl

@[simp] theorem Dep.eta_plug (t : Dep (.base Γ)) :
    (t.map (Ren.weaken Γ).lift).plug (.var 0) = t := by
  rw [Dep.plug, Dep.map_comp, eta_ren, Dep.map_id]

theorem double_plug_ren (b : Base (n+1)) (a : Base n) :
    Ren.comp (Ren.comp (Ren.weaken Γ).lift (plugRen (.base Γ) b)) (plugRen Γ a) =
      plugRen Γ (instantiate b a) := by
  apply Ren.ext
  · funext i; refine Fin.cases rfl (fun j => rfl) i
  · funext v; cases v; rfl
  · funext v; cases v; rfl

theorem Dep.double_plug (t : Dep (.base Γ)) (b : Base (n+1)) (a : Base n) :
    ((t.map (Ren.weaken Γ).lift).plug b).plug a = t.plug (instantiate b a) := by
  simp only [Dep.plug, Dep.map_comp, double_plug_ren]

end Normal
end SquareKit.Internal.DependentFunctions
