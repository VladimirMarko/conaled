import Examples.VaryingPartialCertificates
import SquareKit.AssemblyLift

/-! Independently specified uniform realizability of the existing external states.
The external state space remains unchanged; this predicate selects its internal clients. -/
namespace UniformCertificateStates
open VaryingPartialCertificates Realizability Realizability.Assembly Encodable Denumerable
open Nat.Partrec (Code)

/-- A single program emits a partial-value program for every coordinate.
Its partial graph retains the certificate value, not merely definedness. -/
def StateRealizer {n : Nat} (e : Nat) (q : State n) : Prop := ∀ k,
  ∃ c, c ∈ (ofNat Code e).eval k ∧ ∀ v,
    v ∈ run c ↔ ∃ a : Cert n k, a ∈ q k ∧ a.value.val = v

def UniformRealizable {n : Nat} (q : State n) : Prop := ∃ e, StateRealizer e q

def stateAssembly (n : Nat) : Assembly where
  Carrier := {q : State n // UniformRealizable q}
  realizes e q := StateRealizer e q.val
  inhabited q := q.property

noncomputable def coordinate {n : Nat} (q : State n) (k : Nat) : Option Nat := by
  classical
  exact if h : (q k).Dom then some ((q k).get h).value.val else none

theorem coordinate_eq_some {n : Nat} (q : State n) (k v : Nat) :
    coordinate q k = some v ↔ ∃ a : Cert n k, a ∈ q k ∧ a.value.val = v := by
  classical
  unfold coordinate
  split_ifs with h
  · constructor
    · intro hv
      exact ⟨(q k).get h, Part.get_mem h, Option.some.inj hv⟩
    · rintro ⟨a, ha, hv⟩
      exact congrArg some ((congrArg (fun b : Cert n k => b.value.val)
        (Part.mem_unique (Part.get_mem h) ha)).trans hv)
  · constructor
    · intro hv; cases hv
    · rintro ⟨a, ha, _⟩
      exact (h ha.1).elim

/-- Value equality recovers full records because the independent specification
fixes the canonical trace; no proof witness or successful value is discarded. -/
theorem coordinate_injective {n : Nat} : Function.Injective (coordinate (n := n)) := by
  intro q r h
  funext k
  apply Part.ext
  intro a
  constructor
  · intro ha
    have hv := (coordinate_eq_some q k a.value.val).mpr ⟨a, ha, rfl⟩
    have hv' := (congrFun h k).symm.trans hv
    obtain ⟨b, hb, he⟩ := (coordinate_eq_some r k a.value.val).mp hv'
    have hba : b = a := Cert.ext (Fin.ext he)
    exact hba ▸ hb
  · intro ha
    have hv := (coordinate_eq_some r k a.value.val).mpr ⟨a, ha, rfl⟩
    have hv' := (congrFun h k).trans hv
    obtain ⟨b, hb, he⟩ := (coordinate_eq_some q k a.value.val).mp hv'
    have hba : b = a := Cert.ext (Fin.ext he)
    exact hba ▸ hb

end UniformCertificateStates
