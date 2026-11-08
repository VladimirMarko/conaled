import Examples.InternalCertificateSolver

/-! The tracked internal countdown implements the original full-record step. -/
namespace InternalCertificateSolver
open Realizability Realizability.Assembly
open VaryingPartialCertificates UniformCertificateStates AssemblyCertificateFamily

theorem coordinate_step (enabled : Bool) (n j : Nat) (hj : j ≤ n) (q : State n) (k : Nat) :
    coordinate (runStep enabled n j hj q) k = countdownValue enabled j (coordinate q) k := by
  cases enabled with
  | false => rfl
  | true =>
    cases k with
    | zero => simp [coordinate, runStep, countdownValue, selected]
    | succ k =>
      change coordinate (runStep true n j hj q) (k+1) = (coordinate q k).map Nat.succ
      apply Option.ext
      intro v
      rw [coordinate_eq_some, Option.map_eq_some_iff]
      constructor
      · rintro ⟨a,ha,hv⟩
        change a ∈ Part.map step (q k) at ha
        obtain ⟨b,hb,hba⟩ := (Part.mem_map_iff _).mp ha
        refine ⟨b.value.val,(coordinate_eq_some q k _).mpr ⟨b,hb,rfl⟩,?_⟩
        exact (congrArg (fun c : Cert n (k+1) => c.value.val) hba).trans hv
      · rintro ⟨w,hw,hv⟩
        obtain ⟨b,hb,hbw⟩ := (coordinate_eq_some q k w).mp hw
        refine ⟨step b, Part.mem_map _ hb, ?_⟩
        exact (congrArg Nat.succ hbw).trans hv

theorem countdown_forget_step {Γ : Assembly} (n : Nat) (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n)
    (γ : Γ.Carrier) (q : (boundedSequences n).Carrier) :
    forget n ((boundedCountdown n enabled seed hs).toFun (γ,q)) =
      runStep (enabled.toFun γ) n (seed.toFun γ) (hs γ) (forget n q) := by
  apply coordinate_injective
  funext k
  have hq : coordinate (forget n q) = q.val.toFun := funext (recover_coordinate q)
  exact (recover_coordinate _ k).trans
    ((countdown_apply enabled seed γ q.val k).trans
      ((congrArg (fun f => countdownValue (enabled.toFun γ) (seed.toFun γ) f k) hq).symm.trans
        (coordinate_step _ _ _ _ _ k).symm))

end InternalCertificateSolver
