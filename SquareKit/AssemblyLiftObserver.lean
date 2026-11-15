import SquareKit.AssemblyCutObservation

/-! Exact partial-value observations extracted from lifted-natural trackers. -/
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

theorem liftNat_realizes_iff {e : Nat} {x : Option Nat} :
    (programLift (encoded Nat)).realizes e x ↔ ∀ v, v ∈ run e ↔ x = some v := by
  cases x with
  | none =>
    change ¬ (run e).Dom ↔ ∀ v, v ∈ run e ↔ none = some v
    simp only [reduceCtorEq, iff_false]
    simp only [Part.dom_iff_mem, not_exists]
  | some x =>
    change (∃ m, m ∈ run e ∧ m = x) ↔ ∀ v, v ∈ run e ↔ some x = some v
    constructor
    · rintro ⟨m, hm, rfl⟩ v
      simp only [Option.some.injEq]
      exact ⟨fun hv => (Part.mem_unique hv hm).symm, fun hv => hv ▸ hm⟩
    · intro h
      exact ⟨x, (h x).mpr rfl, rfl⟩

/-- The source tracker emits a partial-value program; observation then runs it. -/
def liftObserver (p : Code) (r e : Nat) : Part Nat :=
  (p.eval (Nat.pair r e)).bind run

theorem liftObserver_partrec (p : Code) : Partrec₂ (liftObserver p) :=
  Partrec.bind (Code.eval_part.comp (Computable.const p) Primrec₂.pair.to_comp)
    ((Partrec.nat_iff.mpr run_partrec).comp Computable.snd)

theorem liftObserver_mem {Γ A : Assembly} {h : Hom (prod Γ A) (programLift (encoded Nat))}
    {p : Code} (hp : Tracks (prod Γ A) (programLift (encoded Nat)) p.eval h.toFun)
    {γ : Γ.Carrier} {r : Nat} (hr : Γ.realizes r γ)
    {a : A.Carrier} {e : Nat} (he : A.realizes e a) (v : Nat) :
    v ∈ liftObserver p r e ↔ h.toFun (γ,a) = some v := by
  obtain ⟨m, hm, hx⟩ := hp (γ,a) (Nat.pair r e) (by simpa [prod] using And.intro hr he)
  rw [liftObserver, Part.mem_bind_iff]
  constructor
  · rintro ⟨k, hk, hv⟩
    have hkm := Part.mem_unique hk hm
    subst k
    exact (liftNat_realizes_iff.mp hx v).mp hv
  · intro hv
    exact ⟨m, hm, (liftNat_realizes_iff.mp hx v).mpr hv⟩

end Realizability.Assembly
