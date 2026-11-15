import SquareKit.AssemblyLiftNatComplete
import SquareKit.AssemblyCompleteClosure

/-! A tracked bound filter on uniformly tracked partial-natural sequences. -/
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

private def boundProgram (b e : Nat) : Part Nat :=
  (run e).bind fun v => Part.ofOption (if v < b then some v else none)

private theorem boundProgram_partrec : Partrec₂ boundProgram := by
  apply Partrec.bind ((Partrec.nat_iff.mpr run_partrec).comp Computable.snd)
  apply Computable.ofOption
  exact (Primrec.ite
    (Primrec.nat_lt.comp Primrec.snd (Primrec.fst.comp Primrec.fst))
    (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to_comp

private noncomputable def boundCode (z : Nat) : Code :=
  Code.comp (templateCode boundProgram boundProgram_partrec) (Code.const z)

private theorem boundCode_computable : Computable boundCode :=
  Code.primrec₂_comp.to_comp.comp (Computable.const _) Code.primrec_const.to_comp

private theorem boundCode_run (b e : Nat) :
    run (encode (boundCode (Nat.pair b e))) = boundProgram b e := by
  rw [run_encode]
  change ((Code.const (Nat.pair b e)).eval 0).bind
    (fun k => (templateCode boundProgram boundProgram_partrec).eval k) = _
  rw [Code.eval_const, Part.bind_some]
  exact templateCode_eval _ _ b e

def filterBoundValue (b : Nat) (x : Option Nat) : Option Nat := x.filter (fun v => v < b)

noncomputable def filterBound : Hom (prod (encoded Nat) (programLift (encoded Nat)))
    (programLift (encoded Nat)) where
  toFun x := filterBoundValue x.1 x.2
  tracked := by
    refine ⟨fun z => Part.some (encode (boundCode z)),
      Partrec.nat_iff.mp (Computable.encode.comp boundCode_computable), ?_⟩
    rintro ⟨b, x⟩ z ⟨hb, hx⟩
    change Nat at b
    change Option Nat at x
    refine ⟨encode (boundCode z), by simp, ?_⟩
    apply liftNat_realizes_iff.mpr
    intro v
    have hz := Nat.pair_unpair z
    rw [← hz, boundCode_run]
    change z.unpair.1 = b at hb
    rw [hb]
    change (v ∈ (run z.unpair.2).bind (fun w => Part.ofOption (if w < b then some w else none))) ↔
      x.filter (fun w => w < b) = some v
    rw [Part.mem_bind_iff]
    simp_rw [liftNat_realizes_iff.mp hx]
    cases x <;> simp
    aesop

/-- The ambient sequence object contains uniformly tracked maps, not every external sequence. -/
abbrev partialSequences := function (encoded Nat) (programLift (encoded Nat))

theorem partialSequences_complete : CutComplete partialSequences :=
  function_cutComplete liftNat_cutComplete _

private def natBound : Hom (prod (encoded Nat) (encoded Nat)) (encoded Nat) where
  toFun := fun (x : Nat × Nat) => x.1 + x.2 + 1
  tracked := by
    have hp : Primrec (fun z : Nat => z.unpair.1 + z.unpair.2 + 1) :=
      Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.unpair)
        (Primrec.snd.comp Primrec.unpair)) (Primrec.const 1)
    refine ⟨_, Partrec.nat_iff.mp hp.to_comp, ?_⟩
    rintro ⟨n,k⟩ z ⟨hn,hk⟩
    change Nat at n k
    refine ⟨z.unpair.1+z.unpair.2+1, by simp, ?_⟩
    change z.unpair.1 = n at hn
    change z.unpair.2 = k at hk
    change z.unpair.1+z.unpair.2+1 = n+k+1
    rw [hn,hk]

noncomputable def sequenceFilter : Hom (prod (encoded Nat) partialSequences) partialSequences :=
  curry ((pair
    ((pair ((fst _ _).comp (fst _ _)) (snd _ _)).comp natBound)
    ((pair ((fst _ _).comp (snd _ _)) (snd _ _)).comp (evaluation _ _))).comp filterBound)

theorem sequenceFilter_apply (n : Nat) (q : partialSequences.Carrier) (k : Nat) :
    ((sequenceFilter.toFun (n,q)).toFun k) = (q.toFun k).filter (fun v => v < n+k+1) :=
  curry_apply _ _ _

end Realizability.Assembly
