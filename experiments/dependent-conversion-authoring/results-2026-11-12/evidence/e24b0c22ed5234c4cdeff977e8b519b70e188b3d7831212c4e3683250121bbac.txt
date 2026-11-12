import Examples.ConversionTrial.Scale
set_option autoImplicit false
set_option warningAsError true
namespace Examples.ConversionTrial.Author
open SquareKit.Internal.DependentFunctions
open SquareKit.Internal.DependentStructural (Base)

theorem ren_id_typed {n : Nat} (Δ : Ctx n) : (Ren.id Δ).Typed where
  dep v := (Base.sub_id v.type).symm
  func v := by change v.type = v.type.sub (up Base.var); rw [up_id, Base.sub_id]

theorem ren_comp_typed {n m l : Nat} {Δ : Ctx n} {Ξ : Ctx m} {Ω : Ctx l}
    {ρ : Ren Ξ Δ} {τ : Ren Ω Ξ} (hρ : ρ.Typed) (hτ : τ.Typed) :
    (Ren.comp ρ τ).Typed where
  dep v := by
    change (τ.dep (ρ.dep v)).type = _
    rw [hτ.dep, hρ.dep, Base.sub_comp]
    rfl
  func v := by
    change (τ.func (ρ.func v)).type = _
    rw [hτ.func, hρ.func, Base.sub_comp, up_comp]
    rfl

theorem rename_eq {n m : Nat} {Δ : Ctx n} {Ξ : Ctx m}
    (ρ : Ren Ξ Δ) (hρ : ρ.Typed) {t u : Dep Δ} (h : DepEq t u) :
    DepEq (ρ.depMap t) (ρ.depMap u) := by
  have hs : (Sub.ofRen ρ).Typed := ⟨hρ.dep, hρ.func⟩
  have e := DepEq.sub (Sub.ofRen ρ) hs h
  rw [Sub.depSub_ofRen, Sub.depSub_ofRen] at e
  exact e

theorem liftRen_typed (k : Nat) : (liftRen k).Typed := by
  induction k with
  | zero => exact ren_id_typed Γ
  | succ k ih => exact ren_comp_typed ih (Ren.typed_weaken (widen k))

theorem expand_eq {n : Nat} {Δ : Ctx n} (r : Nat) (f : Func Δ) :
    FuncEq (expand r f) f := by
  induction r with
  | zero => exact .refl f
  | succ r ih => exact .trans (.eta (expand r f)) ih

theorem chain_eq (k d : Nat) {t u : Dep (widen k)} (h : DepEq t u) :
    DepEq (applyChain (chain k d) t) (applyChain (chain k d) u) := by
  induction d generalizing t u with
  | zero => exact h
  | succ d ih => exact ih (.sub (liftedNegate k) (liftedNegate_typed k) h)

theorem left_eq_right (k r d : Nat) : DepEq (left k r d) (right k d) :=
  chain_eq k d (rename_eq (liftRen k) (liftRen_typed k)
    (.app (expand_eq r parameter) (.neg (.var 0))))
end Examples.ConversionTrial.Author

namespace Examples.ConversionTrial.Scale
open SquareKit.Internal.DependentFunctions
open Author

theorem composition_proof : CompositionTask := by
  intro r _
  have h := left_eq_right 1 r 2
  exact ⟨h, h.type.trans (show (right 1 2).type = Initial.index from rfl)⟩

theorem context_proof : ContextTask := by
  intro k _
  have h := left_eq_right k 1 2
  exact ⟨h, h.type⟩

theorem substitution_proof : SubstitutionTask := by
  intro d _
  have h := left_eq_right 1 1 d
  exact ⟨h, h.type⟩
end Examples.ConversionTrial.Scale
