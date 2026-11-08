import Examples.InternalCertificateTransport

/-! The earlier unique-certificate client is recovered by a declared partial observation. -/
namespace InternalCertificateSolver
open Realizability Realizability.Assembly Encodable Denumerable
open VaryingPartialCertificates AssemblyCertificateFamily
open Nat.Partrec (Code)

/-- Wait for each successful input, then return the unique client's required value.
This is not an equivalence between the two certificate specifications. -/
noncomputable def uniqueObservation (n : Nat) : Hom partialSequences partialSequences :=
  functionPostcompose (programLiftMap (natConstant (encoded Nat) n)) (encoded Nat)

def observeUnique {n : Nat} (q : State n) (k : Nat) : Part (IndexedPartialComputation.Cert n k) :=
  (q k).map (fun _ => IndexedPartialComputation.certificate n k)

theorem uniqueObservation_graph {n : Nat} (q : (boundedSequences n).Carrier) (k v : Nat) :
    (((uniqueObservation n).toFun q.val).toFun k = some v) ↔
      ∃ a ∈ observeUnique (forget n q) k, a.value.val = v := by
  have h := functionPostcompose_apply
    (programLiftMap (natConstant (encoded Nat) n)) q.val k
  change ((uniqueObservation n).toFun q.val).toFun k =
    (q.val.toFun k).map (fun _ => n) at h
  constructor
  · intro hx
    obtain ⟨w,hw,hv⟩ := Option.map_eq_some_iff.mp (h.symm.trans hx)
    obtain ⟨b,hb,_⟩ := (recover_graph q k w).mpr hw
    exact ⟨IndexedPartialComputation.certificate n k, Part.mem_map _ hb, hv⟩
  · rintro ⟨a,ha,hv⟩
    obtain ⟨b,hb,hba⟩ := (Part.mem_map_iff _).mp ha
    apply h.trans
    apply Option.map_eq_some_iff.mpr
    refine ⟨b.value.val,(recover_graph q k _).mp ⟨b,hb,rfl⟩,?_⟩
    exact (congrArg (fun c : IndexedPartialComputation.Cert n k => c.value.val) hba).trans hv

/-- One actual program emits the delayed coordinates of the unique observation. -/
theorem uniqueObservation_uniform {n : Nat} (q : (boundedSequences n).Carrier) :
    ∃ e : Nat, ∀ k : Nat, ∃ c, c ∈ (ofNat Code e).eval k ∧ ∀ v,
      v ∈ run c ↔ ∃ a ∈ observeUnique (forget n q) k, a.value.val = v := by
  obtain ⟨e,he⟩ := partialSequences.inhabited ((uniqueObservation n).toFun q.val)
  refine ⟨e,?_⟩
  intro k
  obtain ⟨c,hc,hr⟩ := he k k rfl
  exact ⟨c,hc,fun v => (liftNat_realizes_iff.mp hr v).trans (uniqueObservation_graph q k v)⟩

theorem solver_unique {Γ : Assembly} (n : Nat) (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n) :
    (fun γ k => observeUnique (forget n ((solver n enabled seed hs).toFun γ)) k) =
      SelectedFixedPoint.solution (IndexedPartialComputation.functional enabled.toFun (fun _ => n)) := by
  apply Eq.trans ?_ (IndexedPartialComputation.solution_eq_meaning enabled.toFun (fun _ => n)).symm
  funext γ k
  apply Eq.trans (congrArg (fun q => observeUnique q k) (solver_forget n enabled seed hs γ))
  cases h : enabled.toFun γ <;>
    simp [observeUnique, meaning, IndexedPartialComputation.meaning, h]

end InternalCertificateSolver
