import Examples.ConversionTrial.HeldOut
set_option autoImplicit false
set_option warningAsError true
namespace Examples.ConversionTrial
open SquareKit.Internal.DependentFunctions
open SquareKit.Internal.DependentStructural (Base)

theorem expand_equal {n : Nat} {Δ : Ctx n} (r : Nat) (f : Func Δ) :
    FuncEq (expand r f) f := by
  induction r with
  | zero => exact .refl f
  | succ r ih => exact .trans (.eta (expand r f)) ih

theorem rename_typed_comp {n m l : Nat} {A : Ctx n} {B : Ctx m} {C : Ctx l}
    (ρ : Ren B A) (τ : Ren C B) (hρ : ρ.Typed) (hτ : τ.Typed) :
    (Ren.comp ρ τ).Typed where
  dep v := by
    change (τ.dep (ρ.dep v)).type = _
    rw [hτ.dep, hρ.dep, Base.sub_comp]
    rfl
  func v := by
    change (τ.func (ρ.func v)).type = _
    rw [hτ.func, hρ.func, Base.sub_comp, up_comp]
    rfl

theorem liftRen_typed (k : Nat) : (liftRen k).Typed := by
  induction k with
  | zero =>
    constructor
    · intro v; exact (Base.sub_id v.type).symm
    · intro v; change v.type = v.type.sub (up Base.var); rw [up_id, Base.sub_id]
  | succ k ih => exact rename_typed_comp _ _ ih (Ren.typed_weaken _)

theorem renamed_equal {n m : Nat} {A : Ctx n} {B : Ctx m}
    (ρ : Ren B A) (hρ : ρ.Typed) {t u : Dep A} (h : DepEq t u) :
    DepEq (ρ.depMap t) (ρ.depMap u) := by
  have hs : (Sub.ofRen ρ).Typed := ⟨hρ.dep, hρ.func⟩
  simpa only [Sub.depSub_ofRen] using DepEq.sub (Sub.ofRen ρ) hs h

theorem chain_equal {n : Nat} {A : Ctx n} (ss : List (Sub A A))
    (hs : ∀ s ∈ ss, s.Typed) {t u : Dep A} (h : DepEq t u) :
    DepEq (applyChain ss t) (applyChain ss u) := by
  induction ss generalizing t u with
  | nil => exact h
  | cons s ss ih =>
    apply ih (fun s hmem => hs s (List.mem_cons_of_mem _ hmem))
    exact DepEq.sub s (hs s (List.mem_cons_self)) h

theorem left_right_equal (k r d : Nat) : DepEq (left k r d) (right k d) := by
  apply chain_equal
  · intro s hs
    have he : s = liftedNegate k := List.eq_of_mem_replicate hs
    subst s
    exact liftedNegate_typed k
  · exact renamed_equal (liftRen k) (liftRen_typed k)
      (DepEq.app (expand_equal r parameter) (.neg (.var 0)))

namespace HeldOut
 theorem held_out_solution : Task := by
  exact ⟨left_right_equal 2 2 3, rfl, rfl⟩
end HeldOut
end Examples.ConversionTrial
