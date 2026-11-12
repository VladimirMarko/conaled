import Examples.ConversionTrial.Scale
import Examples.ConversionTrial.Repair
import Examples.ConversionTrial.HeldOut
import Examples.ConversionTrial.Negative

/-! Private direct-helper oracle. No converter or service reference is imported. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.ConversionTrial.DirectReference
open SquareKit.Internal.DependentFunctions

theorem expansion {n : Nat} {Δ : Ctx n} (r : Nat) (f : Func Δ) : FuncEq (expand r f) f := by
  induction r with
  | zero => exact .refl _
  | succ r ih => exact .trans (.eta _) ih

theorem source_eq (r : Nat) : DepEq (source r) target := .app (expansion r parameter) _

theorem mapped {t u : Dep Γ} (h : DepEq t u) (k : Nat) :
    DepEq ((liftRen k).depMap t) ((liftRen k).depMap u) := by
  induction k with
  | zero =>
    change DepEq ((Ren.id Γ).depMap t) ((Ren.id Γ).depMap u)
    rw [Ren.depMap_id, Ren.depMap_id]
    exact h
  | succ k ih =>
    change DepEq ((Ren.comp (liftRen k) (Ren.weaken (widen k))).depMap t)
      ((Ren.comp (liftRen k) (Ren.weaken (widen k))).depMap u)
    rw [← Ren.depMap_comp, ← Ren.depMap_comp]
    have ht : (Sub.ofRen (Ren.weaken (widen k))).Typed := ⟨fun _ => rfl, fun _ => rfl⟩
    simpa only [Sub.depSub_ofRen] using DepEq.sub (Sub.ofRen (Ren.weaken (widen k))) ht ih

theorem chained {n : Nat} {Δ : Ctx n} (ss : List (Sub Δ Δ))
    (hs : ∀ s ∈ ss, s.Typed) {t u : Dep Δ} (h : DepEq t u) :
    DepEq (applyChain ss t) (applyChain ss u) := by
  induction ss generalizing t u with
  | nil => exact h
  | cons s ss ih =>
    exact ih (fun q hq => hs q (List.mem_cons_of_mem s hq))
      (.sub s (hs s List.mem_cons_self) h)

theorem all_sizes (k r d : Nat) : DepEq (left k r d) (right k d) := by
  apply chained (chain k d) _ (mapped (source_eq r) k)
  intro s hs
  have he : s = liftedNegate k := List.eq_of_mem_replicate hs
  subst s
  exact liftedNegate_typed k

theorem initial : Initial.Task := ⟨all_sizes 1 1 2, rfl, rfl⟩
theorem composition : Scale.CompositionTask := by
  intro r _
  exact ⟨all_sizes 1 r 2, (DepEq.type (all_sizes 1 r 2)).trans rfl⟩
theorem contexts : Scale.ContextTask := fun k _ =>
  ⟨all_sizes k 1 2, DepEq.type (all_sizes k 1 2)⟩
theorem substitutions : Scale.SubstitutionTask := fun d _ =>
  ⟨all_sizes 1 1 d, DepEq.type (all_sizes 1 1 d)⟩
theorem before_repair : Repair.BeforeTask :=
  ⟨.sub (Repair.assignment .zero) (Repair.assignment_typed _) (source_eq 2), rfl⟩
theorem repair : Repair.Task := by
  refine ⟨.sub (Repair.assignment (.var 0)) (Repair.assignment_typed _) (source_eq 2), rfl, ?_⟩
  intro h; cases h

theorem held_out : HeldOut.Task := ⟨all_sizes 2 2 3, rfl, rfl⟩
theorem index_negative : Negative.IndexTask := by
  constructor
  · intro h; cases h
  · intro h; have ht := DepEq.type h; cases ht

-- Instantiated dimensions are checked explicitly, not merely listed in metadata.
example : DepEq (left 1 1 2) (right 1 2) := all_sizes 1 1 2
example : DepEq (left 1 4 2) (right 1 2) := all_sizes 1 4 2
example : DepEq (left 1 8 2) (right 1 2) := all_sizes 1 8 2
example : DepEq (left 3 1 2) (right 3 2) := all_sizes 3 1 2
example : DepEq (left 7 1 2) (right 7 2) := all_sizes 7 1 2
example : DepEq (left 1 1 1) (right 1 1) := all_sizes 1 1 1
example : DepEq (left 1 1 4) (right 1 4) := all_sizes 1 1 4
end Examples.ConversionTrial.DirectReference
