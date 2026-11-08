import SquareKit.AssemblyCutSearchPrograms

/-! The dovetail search preserves the unique selected value of a tracked cut arrow. -/
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

theorem cutArrow_values_agree {Γ : Assembly}
    (h : Hom (prod Γ iterationCuts) (programLift (encoded Nat))) (γ : Γ.Carrier)
    {n m v w : Nat} (hv : h.toFun (γ, ⟨n⟩) = some v)
    (hw : h.toFun (γ, ⟨m⟩) = some w) : v = w := by
  rcases le_total n m with hnm | hmn
  · exact Option.some.inj ((cutArrow_mono h γ hnm hv).symm.trans hw)
  · exact Option.some.inj (hv.symm.trans (cutArrow_mono h γ hmn hw))

theorem cutSearch_mem {Γ : Assembly}
    {h : Hom (prod Γ iterationCuts) (programLift (encoded Nat))}
    {p : Code} (hp : Tracks (prod Γ iterationCuts) (programLift (encoded Nat)) p.eval h.toFun)
    {γ : Γ.Carrier} {r : Nat} (hr : Γ.realizes r γ) (e v : Nat) :
    v ∈ run (encode (searchCode (encode (observerCode p r)) e)) ↔
      ∃ n, CutAccessible e n ∧ h.toFun (γ, ⟨n⟩) = some v := by
  have hg (w : Nat) : (∃ z, w ∈ cutSearchStep (encode (observerCode p r)) e z) ↔
      ∃ n, CutAccessible e n ∧ h.toFun (γ, ⟨n⟩) = some w := by
    rw [cutSearchStep_exists]
    apply exists_congr
    intro n
    apply and_congr_right
    intro _
    simp only [ofNat_encode, observerCode_eval]
    exact liftObserver_mem hp hr (cutCode_realizes n) w
  rw [searchCode_run]
  refine (rfindOpt_mem_of_unique ?_ v).trans (hg v)
  intro i j w z hw hz
  obtain ⟨n, _, hn⟩ := (hg w).mp ⟨i, hw⟩
  obtain ⟨m, _, hm⟩ := (hg z).mp ⟨j, hz⟩
  exact cutArrow_values_agree h γ hn hm

theorem accessible_final {e n : Nat} {t : Option Nat} (he : finalCuts.{0}.realizes e ⟨t⟩) :
    CutAccessible e n ↔ match t with | none => True | some m => n ≤ m := by
  cases t with
  | none => exact ⟨fun _ => trivial, fun _ => Or.inr (he (n-1))⟩
  | some m =>
    change (n = 0 ∨ ((ofNat Code e).eval (n-1)).Dom) ↔ n ≤ m
    rw [he (n-1)]
    omega

/-- The semantic value at infinity is the unique value found at any finite cut. -/
noncomputable def cutLimitValue (f : Nat → Option Nat) : Option Nat := by
  classical
  exact
  if h : ∃ v, ∃ n, f n = some v then some h.choose else none

theorem cutLimitValue_eq_some (f : Nat → Option Nat)
    (hu : ∀ n m v w, f n = some v → f m = some w → v = w) (v : Nat) :
    cutLimitValue f = some v ↔ ∃ n, f n = some v := by
  classical
  unfold cutLimitValue
  split_ifs with h
  · constructor
    · intro he
      exact Option.some.inj he ▸ h.choose_spec
    · rintro ⟨n, hn⟩
      obtain ⟨m, hm⟩ := h.choose_spec
      exact congrArg some (hu m n _ v hm hn)
  · simp only [false_iff, not_exists]
    intro n hn
    exact h ⟨v, n, hn⟩

end Realizability.Assembly
