import Examples.AssemblyCertificateContext
import SquareKit.AssemblySequenceTransport

/-! Actual capacity embeddings commute with the unchanged full-record client. -/
namespace AssemblyCertificateFamily
open VaryingPartialCertificates UniformCertificateStates
open Realizability Realizability.Assembly

theorem coordinate_transport {n m : Nat} (d : Nat) (hd : n+d ≤ m) (q : State n) (k : Nat) :
    coordinate (transport d hd q) k = (coordinate q k).map (fun v => v+d) := by
  apply Option.ext
  intro v
  change coordinate (transport d hd q) k = some v ↔
    (coordinate q k).map (fun w => w+d) = some v
  rw [coordinate_eq_some, Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, hav⟩
    change a ∈ Part.map (embed d hd) (q k) at ha
    obtain ⟨b, hb, hba⟩ := (Part.mem_map_iff _).mp ha
    refine ⟨b.value.val, (coordinate_eq_some q k _).mpr ⟨b,hb,rfl⟩, ?_⟩
    exact (congrArg (fun c : Cert m k => c.value.val) hba).trans hav
  · rintro ⟨w, hw, hwv⟩
    obtain ⟨b,hb,hbw⟩ := (coordinate_eq_some q k w).mp hw
    refine ⟨embed d hd b, Part.mem_map _ hb, ?_⟩
    change b.value.val+d = v
    exact (congrArg (fun z => z+d) hbw).trans hwv

theorem forget_shift {n m : Nat} (d : Nat) (hd : n+d ≤ m) (q : (boundedSequences n).Carrier) :
    forget m ((boundedShift d hd).toFun q) = transport d hd (forget n q) := by
  apply coordinate_injective
  funext k
  exact (recover_coordinate _ _).trans
    ((sequenceShift_apply d q.val k).trans
      ((congrArg (Option.map (fun v : Nat => v+d)) (recover_coordinate q k).symm).trans
        (coordinate_transport d hd (forget n q) k).symm))

noncomputable def selectedState (n j : Nat) (hj : j ≤ n) : (boundedSequences n).Carrier :=
  ⟨(ofComputable (fun k : Nat => j+k)
      (Primrec.nat_add.comp (Primrec.const j) Primrec.id).to_comp).comp
        (programLiftUnit (encoded Nat)), by
    intro k v hv
    have he : j+k = v := Option.some.inj hv
    omega⟩

theorem forget_selected (n j : Nat) (hj : j ≤ n) :
    forget n (selectedState n j hj) = fun k => Part.some (selected n j k hj) := rfl

example : forget 4
    ((boundedShift 1 (show 2+1 ≤ 4 by omega)).toFun
      ((boundedShift 0 (show 1+0 ≤ 2 by omega)).toFun (selectedState 1 0 (by omega)))) 2 =
    Part.some (⟨⟨3, by decide⟩, [2,1,0], rfl⟩ : Cert 4 2) := by
  rw [forget_shift, forget_shift, forget_selected]
  rfl

example (n : Nat) :
    ¬ Function.Surjective (boundedShift 0 (show n+0 ≤ n+1 by omega)).toFun :=
  boundedShift_first_proper n

example (n : Nat) :
    ¬ Function.Surjective (boundedShift 1 (show n+1+1 ≤ n+3 by omega)).toFun :=
  boundedShift_second_proper n

example : ((sequenceFilter.toFun ((1 : Nat),constantSequence 5)).toFun (0 : Nat)) = none := by
  rw [sequenceFilter_apply]
  rfl

example : ((sequenceFilter.toFun ((1 : Nat),constantSequence 5)).toFun (5 : Nat)) = some (5 : Nat) := by
  rw [sequenceFilter_apply]
  rfl

end AssemblyCertificateFamily
