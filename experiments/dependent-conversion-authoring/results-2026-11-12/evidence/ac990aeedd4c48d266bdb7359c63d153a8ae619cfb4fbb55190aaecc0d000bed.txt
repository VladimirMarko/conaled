import Examples.ConversionTrial.Scale
namespace Examples.ConversionTrial
open SquareKit.Internal.DependentFunctions
open SquareKit.Internal.DependentStructural (Base)

theorem renTypedComp {n m k} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx k}
    (ρ : Ren Δ Γ) (τ : Ren Ξ Δ) (h : ρ.Typed) (j : τ.Typed) :
    (Ren.comp ρ τ).Typed where
  dep v := (j.dep (ρ.dep v)).trans ((congrArg (Base.sub τ.base) (h.dep v)).trans (Base.sub_comp _ _ _))
  func v := by
    change (τ.func (ρ.func v)).type = _
    rw [j.func, h.func, Base.sub_comp, up_comp]
    rfl

theorem liftRenTyped (k : Nat) : (liftRen k).Typed := by
  induction k with
  | zero =>
    constructor
    · intro v; exact (Base.sub_id _).symm
    · intro v; change v.type = v.type.sub (up Base.var); rw [up_id, Base.sub_id]
  | succ k ih => exact renTypedComp _ _ ih (Ren.typed_weaken _)

theorem expandEq {n} {Δ : Ctx n} (r : Nat) (f : Func Δ) : FuncEq (expand r f) f := by
  induction r with
  | zero => exact .refl f
  | succ r ih => exact .trans (.eta (expand r f)) ih

theorem sourceEq (r : Nat) : DepEq (source r) target :=
  .app (expandEq r parameter) (.neg (.var 0))

theorem renamedEq (k r : Nat) :
    DepEq ((liftRen k).depMap (source r)) ((liftRen k).depMap target) := by
  have ht : (Sub.ofRen (liftRen k)).Typed := ⟨(liftRenTyped k).dep, (liftRenTyped k).func⟩
  have h := DepEq.sub (Sub.ofRen (liftRen k)) ht (sourceEq r)
  simpa only [Sub.depSub_ofRen] using h

theorem chainEq (k d : Nat) {t u : Dep (widen k)} (h : DepEq t u) :
    DepEq (applyChain (chain k d) t) (applyChain (chain k d) u) := by
  induction d generalizing t u with
  | zero => exact h
  | succ d ih =>
    exact ih (DepEq.sub (liftedNegate k) (liftedNegate_typed k) h)

theorem leftRightEq (k r d : Nat) : DepEq (left k r d) (right k d) :=
  chainEq k d (renamedEq k r)

namespace Scale

theorem compositionSolved : CompositionTask := by
  intro r _
  have h := leftRightEq 1 r 2
  exact ⟨h, h.type.trans rfl⟩

theorem contextSolved : ContextTask := by
  intro k _
  have h := leftRightEq k 1 2
  exact ⟨h, h.type⟩

theorem substitutionSolved : SubstitutionTask := by
  intro d _
  have h := leftRightEq 1 1 d
  exact ⟨h, h.type⟩
end Scale
end Examples.ConversionTrial
