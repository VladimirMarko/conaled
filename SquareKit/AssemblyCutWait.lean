import SquareKit.AssemblyLiftNatComplete

/-! A coordinate observation emits a delayed program and discards enumeration labels. -/
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

private def waitCode (z : Nat) : Code :=
  Code.comp (Code.const z.unpair.2)
    (Code.comp (ofNat Code z.unpair.1) (Code.const z.unpair.2))

private theorem waitCode_computable : Computable waitCode := by
  have fst := Computable.fst.comp Computable.unpair
  have snd := Computable.snd.comp Computable.unpair
  exact Computable₂.comp Code.primrec₂_comp.to_comp
    (Code.primrec_const.to_comp.comp snd)
    (Computable₂.comp Code.primrec₂_comp.to_comp
      ((Computable.ofNat Code).comp fst) (Code.primrec_const.to_comp.comp snd))

private theorem waitCode_run (e k : Nat) :
    run (encode (waitCode (Nat.pair e k))) = ((ofNat Code e).eval k).map (fun _ => k) := by
  rw [run_encode]
  simp only [waitCode, Nat.unpair_pair, Code.eval]
  change (((Code.const k).eval 0).bind (fun r => (ofNat Code e).eval r)).bind
    (fun r => (Code.const k).eval r) = _
  simp_rw [Code.eval_const]
  simp only [Part.bind_some]
  exact Part.bind_some_eq_map _ _

def cutWaitValue (t : Option Nat) (k : Nat) : Option Nat :=
  match t with
  | none => some k
  | some n => if k < n then some k else none

noncomputable def cutWait : Hom (prod finalCuts (encoded Nat)) (programLift (encoded Nat)) where
  toFun x := cutWaitValue x.1.down x.2
  tracked := by
    refine ⟨fun z => Part.some (encode (waitCode z)),
      Partrec.nat_iff.mp (Computable.encode.comp waitCode_computable), ?_⟩
    rintro ⟨⟨t⟩,k⟩ z ⟨ht,hk⟩
    change Nat at k
    change z.unpair.2 = k at hk
    refine ⟨encode (waitCode z), by simp, ?_⟩
    apply liftNat_realizes_iff.mpr
    intro v
    have hz := Nat.pair_unpair z
    rw [← hz, waitCode_run, hk]
    rw [Part.mem_map_iff]
    change (∃ a ∈ (ofNat Code z.unpair.1).eval k, k = v) ↔ cutWaitValue t k = some v
    have hh : (∃ a ∈ (ofNat Code z.unpair.1).eval k, k = v) ↔
        ((ofNat Code z.unpair.1).eval k).Dom ∧ k = v := by
      constructor
      · rintro ⟨a,ha,h⟩; exact ⟨Part.dom_iff_mem.mpr ⟨a,ha⟩,h⟩
      · rintro ⟨h,hv⟩; obtain ⟨a,ha⟩ := Part.dom_iff_mem.mp h; exact ⟨a,ha,hv⟩
    rw [hh]
    cases t with
    | none => simp [cutWaitValue, ht k]
    | some n =>
      change Cut z.unpair.1 n at ht
      rw [ht k]
      simp only [cutWaitValue]
      split <;> simp_all

end Realizability.Assembly
