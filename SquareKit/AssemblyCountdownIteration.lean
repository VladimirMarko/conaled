import SquareKit.AssemblyCountdown

/-! Finite observations of the internal strict-algebra iteration. -/
namespace Realizability.Assembly

def countdownFinite (enabled : Bool) (seed fuel k : Nat) : Option Nat :=
  if enabled = true ∧ k < fuel then some (seed+k) else none

theorem countdownFinite_step (enabled : Bool) (seed fuel k : Nat) :
    countdownValue enabled seed (countdownFinite enabled seed fuel) k =
      countdownFinite enabled seed (fuel+1) k := by
  cases enabled with
  | false => simp [countdownValue, countdownFinite]
  | true =>
    cases k with
    | zero => simp [countdownValue, countdownFinite]
    | succ k =>
      simp only [countdownValue, ↓reduceIte, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, Nat.add_sub_cancel, countdownFinite, true_and]
      by_cases h : k < fuel
      · simp [h, show k+1 < fuel+1 by omega, Nat.add_assoc]
      · simp [h, show ¬k+1 < fuel+1 by omega]

theorem countdown_iteration {Γ : Assembly} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (γ : Γ.Carrier) (fuel k : Nat) :
    ((strictIteration sequenceAlgebra (countdown enabled seed)).toFun (γ,⟨fuel⟩)).toFun k =
      countdownFinite (enabled.toFun γ) (seed.toFun γ) fuel k := by
  induction fuel generalizing k with
  | zero =>
    simp only [countdownFinite, Nat.not_lt_zero, and_false, ite_false]
    rfl
  | succ fuel ih =>
    have step := congrArg (fun q : partialSequences.Carrier => q.toFun k)
      (strictIteration_succ sequenceAlgebra (countdown enabled seed) γ fuel)
    have he : ((strictIteration sequenceAlgebra (countdown enabled seed)).toFun (γ,⟨fuel⟩)).toFun =
        countdownFinite (enabled.toFun γ) (seed.toFun γ) fuel := funext ih
    exact step.trans ((countdown_apply enabled seed γ _ k).trans
      ((congrArg (fun f => countdownValue (enabled.toFun γ) (seed.toFun γ) f k) he).trans
        (countdownFinite_step _ _ _ _)))

theorem countdown_iteration_bounded {Γ : Assembly} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (γ : Γ.Carrier) (n : Nat) (hs : Nat.le (seed.toFun γ) n)
    (fuel : Nat) : SequenceBounded n
      ((strictIteration sequenceAlgebra (countdown enabled seed)).toFun (γ,⟨fuel⟩)) := by
  induction fuel with
  | zero => intro k v hv; cases hv
  | succ fuel ih =>
    exact (congrArg (SequenceBounded n)
      (strictIteration_succ sequenceAlgebra (countdown enabled seed) γ fuel)).mpr
      (countdown_bounded enabled seed γ n hs ih)

end Realizability.Assembly
