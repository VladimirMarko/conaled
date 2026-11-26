import SquareKit.AssemblyCutContinuity
import SquareKit.AssemblyCutComplete

/-! Concrete all-context completeness of the natural-number assembly. -/
namespace Realizability.Assembly

theorem iterationCuts_hom_encoded_nat_constant {Γ : Assembly} (h : Hom (prod Γ iterationCuts) (encoded Nat))
    (γ : Γ.Carrier) (n : Nat) : h.toFun (γ, ⟨n⟩) = h.toFun (γ, ⟨0⟩) := by
  exact Option.some.inj (iterationCuts_hom_mono (h.comp (programLiftUnit _)) γ (Nat.zero_le n) rfl)

theorem finalCuts_hom_encoded_nat_constant {Γ : Assembly} (h : Hom (prod Γ finalCuts) (encoded Nat))
    (γ : Γ.Carrier) (n : Option Nat) : h.toFun (γ, ⟨n⟩) = h.toFun (γ, ⟨some 0⟩) := by
  cases n with
  | some n => exact iterationCuts_hom_encoded_nat_constant ((cutContextInclusion Γ).comp h) γ n
  | none =>
    exact Option.some.inj ((finalCuts_hom_infinity_iff (h.comp (programLiftUnit _)) γ
      (h.toFun (γ, ⟨some 0⟩))).mpr ⟨0, rfl⟩)

/-- The context is arbitrary; no coding or inhabitance assumption is imposed on it. -/
theorem nat_cutComplete : CutComplete (encoded Nat) := by
  intro Γ
  constructor
  · intro h k hk
    apply Hom.ext
    rintro ⟨γ, ⟨n⟩⟩
    exact (finalCuts_hom_encoded_nat_constant h γ n).trans
      ((congrArg (fun f => f.toFun (γ, ⟨0⟩)) hk).trans (finalCuts_hom_encoded_nat_constant k γ n).symm)
  · intro h
    refine ⟨(fst Γ finalCuts).comp ((pair (Hom.id Γ) (cutZero Γ)).comp h), ?_⟩
    apply Hom.ext
    rintro ⟨γ, ⟨n⟩⟩
    exact (iterationCuts_hom_encoded_nat_constant h γ n).symm

end Realizability.Assembly
