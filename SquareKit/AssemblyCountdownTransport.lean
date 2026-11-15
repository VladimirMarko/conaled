import SquareKit.AssemblyCountdownFamily

/-! Local strict-algebra squares transport selection before any closed-form comparison. -/
namespace Realizability.Assembly

noncomputable def shiftSeed {Γ : Assembly} (seed : Hom Γ (encoded Nat)) (d : Nat) :
    Hom Γ (encoded Nat) := seed.comp (ofComputable (fun v : Nat => v+d)
      (Primrec.nat_add.comp Primrec.id (Primrec.const d)).to_comp)

theorem countdownValue_shift (enabled : Bool) (seed d : Nat) (q : Nat → Option Nat) (k : Nat) :
    (countdownValue enabled seed q k).map (fun v => v+d) =
      countdownValue enabled (seed+d) (fun i => (q i).map (fun v => v+d)) k := by
  cases enabled with
  | false => rfl
  | true =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [countdownValue, ↓reduceIte, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, Nat.add_sub_cancel]
      cases q k <;> simp [Nat.add_assoc, Nat.add_comm]

theorem countdown_shift_square {Γ : Assembly} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (d : Nat) :
    (countdown enabled seed).comp (sequenceShiftAlgebra d).f =
      (pair (fst _ _) ((snd _ _).comp (sequenceShiftAlgebra d).f)).comp
        (countdown enabled (shiftSeed seed d)) := by
  apply Hom.ext
  rintro ⟨γ,q⟩
  apply Hom.ext
  intro k
  change Nat at k
  have hs := sequenceShift_apply d ((countdown enabled seed).toFun (γ,q)) k
  have hc := countdown_apply enabled seed γ q k
  have ht := countdown_apply enabled (shiftSeed seed d) γ ((sequenceShift d).toFun q) k
  have hq : ((sequenceShift d).toFun q).toFun = fun i => (q.toFun i).map (fun v : Nat => v+d) :=
    funext (sequenceShift_apply d q)
  exact hs.trans ((congrArg (Option.map (fun v : Nat => v+d)) hc).trans
    ((countdownValue_shift _ _ _ _ _).trans
      ((congrArg (fun f => countdownValue (enabled.toFun γ) (Nat.add (seed.toFun γ) d) f k) hq).symm.trans ht.symm)))

theorem boundedCountdown_shift_square {Γ : Assembly} {n m : Nat} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n)
    (d : Nat) (hd : n+d ≤ m) :
    (boundedCountdown n enabled seed hs).comp (boundedShiftAlgebra d hd).f =
      (pair (fst _ _) ((snd _ _).comp (boundedShiftAlgebra d hd).f)).comp
        (boundedCountdown m enabled (shiftSeed seed d)
          (fun γ => Nat.le_trans (Nat.add_le_add_right (hs γ) d) hd)) := by
  apply Hom.ext
  rintro ⟨γ,q⟩
  apply Subtype.ext
  exact congrArg (fun f => f.toFun (γ,q.val)) (countdown_shift_square enabled seed d)

theorem boundedCountdown_selected_shift {Γ : Assembly} {n m : Nat} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n)
    (d : Nat) (hd : n+d ≤ m) :
    (cutSelected (boundedSequenceAlgebra n) (boundedSequences_complete n)
      (boundedCountdown n enabled seed hs)).comp (boundedShift d hd) =
      cutSelected (boundedSequenceAlgebra m) (boundedSequences_complete m)
        (boundedCountdown m enabled (shiftSeed seed d)
          (fun γ => Nat.le_trans (Nat.add_le_add_right (hs γ) d) hd)) :=
  cutSelected_transport _ _ (boundedSequences_complete n) (boundedSequences_complete m)
    (boundedShiftAlgebra d hd) _ _ (boundedCountdown_shift_square enabled seed hs d hd)

end Realizability.Assembly
