import SquareKit.AssemblyLiftObserver

/-! Finite observations characterize lifted-natural arrows at infinity. -/
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

theorem cutArrow_mono {Γ : Assembly}
    (h : Hom (prod Γ iterationCuts) (programLift (encoded Nat))) (γ : Γ.Carrier)
    {n m v : Nat} (hnm : n ≤ m) (hv : h.toFun (γ, ⟨n⟩) = some v) :
    h.toFun (γ, ⟨m⟩) = some v := by
  obtain ⟨p, hp⟩ := h.has_code
  obtain ⟨r, hr⟩ := Γ.inhabited γ
  have hq : Partrec (liftObserver p r) :=
    (liftObserver_partrec p).comp (Computable.const r) Computable.id
  obtain ⟨e, he, hev⟩ := cut_growth (liftObserver p r) hq n v (fun k => k < m)
    (Primrec.nat_lt.comp Primrec.id (Primrec.const m)) (fun k hk => by omega)
    (fun e he => (liftObserver_mem hp hr he v).mpr hv)
  exact (liftObserver_mem hp hr he v).mp hev

theorem cutArrow_infinity_iff {Γ : Assembly}
    (h : Hom (prod Γ finalCuts) (programLift (encoded Nat))) (γ : Γ.Carrier) (v : Nat) :
    h.toFun (γ, ⟨none⟩) = some v ↔ ∃ n, h.toFun (γ, ⟨some n⟩) = some v := by
  obtain ⟨p, hp⟩ := h.has_code
  obtain ⟨r, hr⟩ := Γ.inhabited γ
  have hq : Partrec (liftObserver p r) :=
    (liftObserver_partrec p).comp (Computable.const r) Computable.id
  constructor
  · intro hv
    obtain ⟨e, n, he, hev⟩ := cut_finite_witness (liftObserver p r) hq v
      (fun e he => (liftObserver_mem hp hr (a := ⟨none⟩) he v).mpr hv)
    exact ⟨n, (liftObserver_mem hp hr (a := ⟨some n⟩) he v).mp hev⟩
  · rintro ⟨n, hv⟩
    obtain ⟨e, he, hev⟩ := cut_growth (liftObserver p r) hq n v (fun _ => True)
      (⟨inferInstance, Primrec.const true⟩) (fun _ _ => trivial)
      (fun e he => (liftObserver_mem hp hr (a := ⟨some n⟩) he v).mpr hv)
    exact (liftObserver_mem hp hr (a := ⟨none⟩) (fun k => (he k).mpr trivial) v).mp hev

end Realizability.Assembly
