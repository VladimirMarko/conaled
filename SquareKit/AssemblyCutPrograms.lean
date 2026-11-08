import SquareKit.AssemblyCuts

/-! Computable transformations used by the cut algebra and coalgebra. -/
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

/-- Choose the code of a fixed two-argument template. Parameters are supplied
by currying this one template, rather than by choosing a new code per input. -/
noncomputable def templateCode (f : Nat → Nat → Part Nat) (hf : Partrec₂ f) : Code :=
  (Code.exists_code.mp (Partrec₂.unpaired'.mpr hf)).choose

theorem templateCode_eval (f : Nat → Nat → Part Nat) (hf : Partrec₂ f) (a b : Nat) :
    (templateCode f hf).eval (Nat.pair a b) = f a b := by
  have h := congrFun (Code.exists_code.mp (Partrec₂.unpaired'.mpr hf)).choose_spec (Nat.pair a b)
  simpa [templateCode, Nat.unpaired] using h

/-- Wait for the lifted value; then prepend its first positive observation. -/
def rollProgram (e k : Nat) : Part Nat :=
  (run e).bind fun m => k.casesOn (Part.some 0) (fun j => (ofNat Code m).eval j)

theorem rollProgram_partrec : Partrec₂ rollProgram := by
  apply Partrec.bind (Partrec.nat_iff.mpr run_partrec |>.comp Computable.fst)
  exact (Partrec.nat_casesOn_right (Computable.snd.comp Computable.fst)
    (Computable.const 0)
    (Code.eval_part.comp ((Computable.ofNat Code).comp (Computable.snd.comp Computable.fst))
      Computable.snd).to₂).to₂

noncomputable def rollCode (e : Nat) : Code := (templateCode rollProgram rollProgram_partrec).curry e

theorem rollCode_computable : Computable rollCode :=
  (Code.primrec₂_curry.comp (Primrec.const _) Primrec.id).to_comp

@[simp] theorem rollCode_eval (e k : Nat) : (rollCode e).eval k = rollProgram e k := by
  simp [rollCode, Code.eval_curry, templateCode_eval]

/-- Return the shifted cut only after observing membership of zero. -/
def unrollCode (e : Nat) : Code :=
  Code.comp (Code.const (encode (shiftCode e))) (ofNat Code e)

theorem unrollCode_computable : Computable unrollCode :=
  Code.primrec₂_comp.to_comp.comp
    (Code.primrec_const.to_comp.comp (Computable.encode.comp shiftCode_computable))
    (Computable.ofNat Code)

@[simp] theorem unrollCode_run (e : Nat) :
    run (encode (unrollCode e)) = (run e).map (fun _ => encode (shiftCode e)) := by
  rw [run_encode]
  change (run e).bind (fun k => (Code.const (encode (shiftCode e))).eval k) = _
  simp_rw [Code.eval_const]
  exact Part.bind_some_eq_map _ _

end Realizability.Assembly
