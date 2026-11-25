import Applications.Resources.TuringSimulation.OrdinaryPackage
import Applications.Resources.TuringSimulation.TapeToPrimitive

set_option autoImplicit false
set_option warningAsError true

/-!
# Actual source runs as inputs to the ordinary native wrapper

UNCOMPILED implementation draft. This generic consumer fixes the source package
before the input. It composes the existing stack, primitive and finite-support
simulations; no delimiter or controller construction is imported. Its premise
is an actual bounded source witness and occupancy of its actual prefixes.
-/

namespace Resources.TuringSimulation.StackToTape.OrdinaryPackage

open Function Turing

-- Use exactly the finiteness data already bundled with the fixed source.
attribute [local instance] FinTM2.kFin FinTM2.ΛFin

/-- An actual finite source computation yields the encoded primitive witness
required by the ordinary wrapper, retaining its complete related endpoint.
The finite action maximum belongs to the fixed complete source program. -/
theorem encodedRun_of_outputsInTime (tm : FinTM2)
    (raw : List (tm.Γ tm.k₀)) (out : List (tm.Γ tm.k₁)) (T B : ℕ)
    (source : TM2OutputsInTime tm raw (some out) T)
    (hprefix : ∀ (i : ℕ) (c : tm.Cfg), i < source.steps →
      (flip Bind.bind tm.step)^[i] (some (initList tm raw)) = some c →
      (∑ k, (c.stk k).length) ≤ B) :
    ∃ target : NativeTarget tm,
      TM2to1.TrCfg (haltList tm out) target ∧
      Nonempty (EncodedRun tm raw target
        (3 * (T * (1 + finiteActionBound tm.m *
          (2 * (B + finiteActionBound tm.m) + 2))))) := by
  let : Inhabited tm.Λ := ⟨tm.main⟩
  let : Inhabited tm.σ := ⟨tm.initialState⟩
  let A := finiteActionBound tm.m
  let W := T * (1 + A * (2 * (B + A) + 2))
  have sourceRun : (flip Bind.bind (TM2.step tm.m))^[source.steps]
      (some (initList tm raw)) = some (haltList tm out) := source.evals_in_steps
  have sourcePrefix : ∀ (i : ℕ) (c : TM2.Cfg tm.Γ tm.Λ tm.σ), i < source.steps →
      (flip Bind.bind (TM2.step tm.m))^[i] (some (initList tm raw)) = some c →
      (∀ k, (c.stk k).length ≤ B) ∧
      (∀ l, c.l = some l → actionBound (tm.m l) ≤ A) := by
    intro i c within reached
    refine ⟨?_, fun l _ => actionBound_le_finiteActionBound tm.m l⟩
    intro k
    have single : (c.stk k).length ≤ ∑ j, (c.stk j).length :=
      Finset.single_le_sum (f := fun j => (c.stk j).length)
        (fun j _ => Nat.zero_le (c.stk j).length) (Finset.mem_univ k)
    exact single.trans (hprefix i c within reached)
  obtain ⟨target, related, ⟨middle⟩⟩ :=
    Resources.TuringSimulation.StackToTape.finite_run_bounded tm.m
      (initList tm raw) (haltList tm out) (encodedInitial tm raw)
      (encodedInitial_related tm raw) source.steps A B sourceRun sourcePrefix
  let middleBound : StateTransition.EvalsToInTime (TM1.step (TM2to1.tr tm.m))
      (encodedInitial tm raw) (some target) W :=
    { toEvalsTo := middle.toEvalsTo
      steps_le_m := middle.steps_le_m.trans
        (Nat.mul_le_mul_right (1 + A * (2 * (B + A) + 2)) source.steps_le_m) }
  obtain ⟨primitive⟩ := Resources.TuringSimulation.TapeToPrimitive.stack_run_bounded
    tm.m (encodedInitial tm raw) target W middleBound
  let : Inhabited (Package.AmbientControl tm) := Package.ambientInhabited tm
  have native : StateTransition.EvalsToInTime (TM0.step (Package.ambientMachine tm))
      (Package.initial tm raw) (some (TM1to0.trCfg (TM2to1.tr tm.m) target))
      (3 * W) := primitive
  have finite : EncodedRun tm raw target (3 * W) :=
    Package.closedInitialRun tm raw (some (TM1to0.trCfg (TM2to1.tr tm.m) target))
      (3 * W) native
  exact ⟨target, related, ⟨finite⟩⟩

end Resources.TuringSimulation.StackToTape.OrdinaryPackage
