import Examples.UniformCertificateStates

/-! The external all-states space strictly exceeds the internally admitted states. -/
namespace NonUniformCertificateState
open VaryingPartialCertificates UniformCertificateStates Realizability.Assembly Denumerable
open Nat.Partrec (Code)

def observe (e k : Nat) : Part Nat := ((ofNat Code e).eval k).bind run

noncomputable def value (k : Nat) : Nat := by
  classical
  exact if k = 0 then 0 else if 0 ∈ observe (k-1) k then 1 else 0

theorem value_bound (k : Nat) : value k < 0+k+1 := by
  classical
  unfold value
  split_ifs <;> omega

noncomputable def diagonal : State 0 := fun k =>
  Part.some ⟨⟨value k,value_bound k⟩, IndexedPartialComputation.trace k, rfl⟩

/-- Even total bounded certificate states need not have a uniform realizer. -/
theorem diagonal_not_uniform : ¬ UniformRealizable diagonal := by
  classical
  rintro ⟨e, he⟩
  obtain ⟨c, hc, hs⟩ := he (e+1)
  have ho (v : Nat) : v ∈ observe e (e+1) ↔ value (e+1) = v := by
    unfold observe
    rw [Part.mem_bind_iff]
    constructor
    · rintro ⟨d,hd,hv⟩
      have hdc := Part.mem_unique hd hc
      subst d
      obtain ⟨a,ha,hav⟩ := (hs v).mp hv
      have ha' := Part.mem_some_iff.mp ha
      exact (congrArg (fun b : Cert 0 (e+1) => b.value.val) ha').symm.trans hav
    · intro hv
      exact ⟨c,hc,(hs v).mpr
        ⟨⟨⟨value (e+1),value_bound _⟩,IndexedPartialComputation.trace _,rfl⟩,
          Part.mem_some_iff.mpr rfl,hv⟩⟩
  by_cases hz : 0 ∈ observe e (e+1)
  · have h := (ho 0).mp hz
    simp [value,hz] at h
  · apply hz
    apply (ho 0).mpr
    simp [value,hz]

example (k : Nat) : (diagonal k).Dom := Part.some_dom _

end NonUniformCertificateState
