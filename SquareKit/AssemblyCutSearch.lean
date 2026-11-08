import SquareKit.AssemblyCutContinuity

/-! Uniform dovetailing of cut accessibility and finite value observations. -/
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

/-- A finite cut of length n is accessible when its last observation terminates.
Length zero requires no observation. -/
def CutAccessible (e n : Nat) : Prop := n = 0 ∨ ((ofNat Code e).eval (n-1)).Dom

noncomputable def cutSearchStep (q e z : Nat) : Option Nat :=
  let n := z.unpair.1
  let s := z.unpair.2.unpair.1
  let t := z.unpair.2.unpair.2
  if n = 0 ∨ (Code.evaln s (ofNat Code e) (n-1)).isSome then
    Code.evaln t (ofNat Code q) (encode (cutCode n)) else none

private def searchN (x : (Nat × Nat) × Nat) := x.2.unpair.1
private def searchS (x : (Nat × Nat) × Nat) := x.2.unpair.2.unpair.1
private def searchT (x : (Nat × Nat) × Nat) := x.2.unpair.2.unpair.2
private theorem searchN_primrec : Primrec searchN :=
  Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
private theorem searchS_primrec : Primrec searchS :=
  Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
private theorem searchT_primrec : Primrec searchT :=
  Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))

private theorem accessEval_primrec : Primrec (fun x : (Nat × Nat) × Nat =>
    Code.evaln (searchS x) (ofNat Code x.1.2) (searchN x-1)) :=
  Code.primrec_evaln.comp
    ((searchS_primrec.pair ((Primrec.ofNat Code).comp (Primrec.snd.comp Primrec.fst))).pair
      (Primrec.nat_sub.comp searchN_primrec (Primrec.const 1)))

private theorem accessible_primrec : PrimrecPred (fun x : (Nat × Nat) × Nat =>
    searchN x = 0 ∨ (Code.evaln (searchS x) (ofNat Code x.1.2) (searchN x-1)).isSome) :=
  (Primrec.eq.comp searchN_primrec (Primrec.const 0)).or
    (Primrec.eq.comp (Primrec.option_isSome.comp accessEval_primrec) (Primrec.const true))

private theorem valueInput_computable : Computable (fun x : (Nat × Nat) × Nat =>
    ((searchT x, ofNat Code x.1.1), encode (cutCode (searchN x)))) :=
  (searchT_primrec.to_comp.pair
    ((Computable.ofNat Code).comp (Computable.fst.comp Computable.fst))).pair
    (Computable.encode.comp (cutCode_computable.comp searchN_primrec.to_comp))

private theorem valueEval_computable : Computable (fun x : (Nat × Nat) × Nat =>
    Code.evaln (searchT x) (ofNat Code x.1.1) (encode (cutCode (searchN x)))) :=
  (Computable.comp Code.primrec_evaln.to_comp valueInput_computable).of_eq (fun _ => rfl)

theorem cutSearchStep_computable : Computable (fun x : (Nat × Nat) × Nat =>
    cutSearchStep x.1.1 x.1.2 x.2) :=
  (Computable.cond accessible_primrec.decide.to_comp valueEval_computable
    (Computable.const none)).of_eq (fun x => by simp only [Bool.cond_decide]; rfl)

/-- No monotonicity of the scheduling order is assumed: all successful stages
must instead agree on their value. -/
theorem rfindOpt_mem_of_unique {f : Nat → Option Nat}
    (hu : ∀ i j v w, v ∈ f i → w ∈ f j → v = w) (v : Nat) :
    v ∈ Nat.rfindOpt f ↔ ∃ z, v ∈ f z := by
  refine ⟨Nat.rfindOpt_spec, ?_⟩
  rintro ⟨z, hz⟩
  have hd := Nat.rfindOpt_dom.mpr ⟨z, v, hz⟩
  obtain ⟨k, hk⟩ := Nat.rfindOpt_spec (Part.get_mem hd)
  exact (hu k z _ v hk hz) ▸ Part.get_mem hd

/-- Exact graph before imposing agreement of competing successful observations. -/
theorem cutSearchStep_exists (q e v : Nat) :
    (∃ z, v ∈ cutSearchStep q e z) ↔
      ∃ n, CutAccessible e n ∧ v ∈ (ofNat Code q).eval (encode (cutCode n)) := by
  constructor
  · rintro ⟨z, hz⟩
    dsimp [cutSearchStep] at hz
    split_ifs at hz with ha
    · refine ⟨z.unpair.1, ?_, Code.evaln_sound hz⟩
      rcases ha with hn | hs
      · exact Or.inl hn
      · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
        exact Or.inr (Part.dom_iff_mem.mpr ⟨w, Code.evaln_sound (by simpa using hw)⟩)
    · simp at hz
  · rintro ⟨n, hn, hv⟩
    obtain ⟨t, ht⟩ := Code.evaln_complete.mp hv
    have hs : ∃ s, n = 0 ∨ (Code.evaln s (ofNat Code e) (n-1)).isSome := by
      rcases hn with hn | hn
      · exact ⟨0, Or.inl hn⟩
      · obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp hn
        obtain ⟨s, hs⟩ := Code.evaln_complete.mp hw
        exact ⟨s, Or.inr (Option.isSome_iff_exists.mpr ⟨w, hs⟩)⟩
    obtain ⟨s, hs⟩ := hs
    refine ⟨Nat.pair n (Nat.pair s t), ?_⟩
    simpa [cutSearchStep, hs] using ht

end Realizability.Assembly
