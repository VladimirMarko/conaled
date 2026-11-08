import SquareKit.AssemblyCutSearch

/-! Fixed templates compile observation and dovetailing uniformly in their inputs. -/
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

private def observerTemplate (z e : Nat) : Part Nat :=
  liftObserver (ofNat Code z.unpair.1) z.unpair.2 e

private theorem observerTemplate_partrec : Partrec₂ observerTemplate := by
  apply Partrec.bind
    (Code.eval_part.comp
      ((Computable.ofNat Code).comp
        (Computable.fst.comp (Primrec.unpair.to_comp.comp Computable.fst)))
      (Computable₂.comp Primrec₂.pair.to_comp
        (Computable.snd.comp (Primrec.unpair.to_comp.comp Computable.fst)) Computable.snd))
  exact (Partrec.nat_iff.mpr run_partrec).comp Computable.snd

noncomputable def observerCode (p : Code) (r : Nat) : Code :=
  (templateCode observerTemplate observerTemplate_partrec).curry (Nat.pair (encode p) r)

theorem observerCode_computable : Computable₂ observerCode :=
  Code.primrec₂_curry.to_comp.comp (Computable.const _)
    (Computable₂.comp Primrec₂.pair.to_comp
      (Computable.encode.comp Computable.fst) Computable.snd)

@[simp] theorem observerCode_eval (p : Code) (r e : Nat) :
    (observerCode p r).eval e = liftObserver p r e := by
  simp [observerCode, Code.eval_curry, templateCode_eval, observerTemplate]

private noncomputable def searchTemplate (q e : Nat) : Part Nat :=
  Nat.rfindOpt (cutSearchStep q e)

private theorem searchTemplate_partrec : Partrec₂ searchTemplate :=
  Partrec.rfindOpt cutSearchStep_computable

/-- The compiled program can diverge when run, but its construction terminates. -/
noncomputable def searchCode (q e : Nat) : Code :=
  Code.comp (templateCode searchTemplate searchTemplate_partrec) (Code.const (Nat.pair q e))

theorem searchCode_computable : Computable₂ searchCode :=
  Code.primrec₂_comp.to_comp.comp (Computable.const _)
    (Code.primrec_const.to_comp.comp Primrec₂.pair.to_comp)

@[simp] theorem searchCode_run (q e : Nat) :
    run (encode (searchCode q e)) = Nat.rfindOpt (cutSearchStep q e) := by
  rw [run_encode]
  change ((Code.const (Nat.pair q e)).eval 0).bind
    (fun k => (templateCode searchTemplate searchTemplate_partrec).eval k) = _
  rw [Code.eval_const, Part.bind_some]
  exact templateCode_eval _ _ q e

end Realizability.Assembly
