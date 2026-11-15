import SquareKit.AssemblyBoundedFamily
import SquareKit.AssemblyCartesian

/-! Tracked value shifts and their proper capacity embeddings. -/
namespace Realizability.Assembly

noncomputable def sequenceShift (d : Nat) : Hom partialSequences partialSequences :=
  functionPostcompose (programLiftMap (ofComputable (fun v : Nat => v+d)
    (Primrec.nat_add.comp Primrec.id (Primrec.const d)).to_comp)) (encoded Nat)

theorem sequenceShift_apply (d : Nat) (q : partialSequences.Carrier) (k : Nat) :
    ((sequenceShift d).toFun q).toFun k = (q.toFun k).map (fun v : Nat => v+d) :=
  functionPostcompose_apply _ _ _

theorem sequenceShift_bounded {n m : Nat} (d : Nat) (hd : n+d ≤ m)
    {q : partialSequences.Carrier} (hq : SequenceBounded n q) :
    SequenceBounded m ((sequenceShift d).toFun q) := by
  intro k v hv
  have hv' := (sequenceShift_apply d q k).symm.trans hv
  obtain ⟨w, hw, he⟩ := Option.map_eq_some_iff.mp hv'
  have hb := hq k w hw
  change w+d = v at he
  omega

noncomputable def boundedShift {n m : Nat} (d : Nat) (hd : n+d ≤ m) :
    Hom (boundedSequences n) (boundedSequences m) :=
  factor _ ((inclusion _ _).comp (sequenceShift d))
    (fun q => sequenceShift_bounded d hd q.property)

private theorem shiftOption_comp (q : Option Nat) (d e : Nat) :
    (q.map (fun v => v+d)).map (fun v => v+e) = q.map (fun v => v+(d+e)) := by
  simp [Option.map_map]

private theorem shiftOption_zero (q : Option Nat) : q.map (fun v => v+0) = q := by simp

theorem boundedShift_comp {n m r : Nat} (d e : Nat) (hd : n+d ≤ m) (he : m+e ≤ r) :
    (boundedShift d hd).comp (boundedShift e he) = boundedShift (d+e) (by omega) := by
  apply Hom.ext
  intro q
  apply Subtype.ext
  apply Hom.ext
  intro k
  change Nat at k
  have h₁ := sequenceShift_apply e ((sequenceShift d).toFun q.val) k
  have h₂ := sequenceShift_apply d q.val k
  have h₃ := sequenceShift_apply (d+e) q.val k
  have hadd := shiftOption_comp (q.val.toFun k) d e
  exact h₁.trans ((congrArg (Option.map (fun v : Nat => v+e)) h₂).trans
    (hadd.trans h₃.symm))

def constantSequence (v : Nat) : partialSequences.Carrier :=
  (natConstant (encoded Nat) v).comp (programLiftUnit (encoded Nat))

def boundedConstant (n v : Nat) (hv : v ≤ n) : (boundedSequences n).Carrier :=
  ⟨constantSequence v, by
    intro k w hw
    have he : v = w := Option.some.inj hw
    omega⟩

theorem boundedShift_first_proper (n : Nat) :
    ¬ Function.Surjective (boundedShift 0 (show n+0 ≤ n+1 by omega)).toFun := by
  intro hs
  obtain ⟨q, hq⟩ := hs (boundedConstant (n+1) (n+1) (by omega))
  have hv := congrArg (fun q => q.val.toFun (0 : Nat)) hq
  have he := (sequenceShift_apply 0 q.val 0).symm.trans hv
  change (q.val.toFun (0 : Nat)).map (fun v : Nat => v+0) = some (n+1) at he
  have hz : q.val.toFun (0 : Nat) = some (n+1) := (shiftOption_zero _).symm.trans he
  have hb := q.property 0 (n+1) hz
  omega

theorem boundedShift_second_proper (n : Nat) :
    ¬ Function.Surjective (boundedShift 1 (show n+1+1 ≤ n+3 by omega)).toFun := by
  intro hs
  obtain ⟨q, hq⟩ := hs (boundedConstant (n+3) 0 (by omega))
  have hv := congrArg (fun q => q.val.toFun (0 : Nat)) hq
  have he := (sequenceShift_apply 1 q.val 0).symm.trans hv
  obtain ⟨w, _, hw⟩ := Option.map_eq_some_iff.mp he
  change w+1 = 0 at hw
  omega

end Realizability.Assembly
