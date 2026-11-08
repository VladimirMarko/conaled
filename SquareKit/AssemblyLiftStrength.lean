import SquareKit.AssemblyLiftMonad

/-! A tracked strength retains parameters while waiting for partial data. -/
universe u
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

private def strengthCode (p : Nat × Nat) : Code :=
  Code.comp (Code.pair (Code.const p.1) Code.id) (ofNat Code p.2)

private theorem strengthCode_computable : Computable strengthCode :=
  Computable₂.comp Code.primrec₂_comp.to_comp
    (Computable₂.comp Code.primrec₂_pair.to_comp
      (Code.primrec_const.to_comp.comp Computable.fst) (Computable.const Code.id))
    ((Computable.ofNat Code).comp Computable.snd)

private theorem strengthCode_run (r e : Nat) :
    run (encode (strengthCode (r,e))) = (run e).map (Nat.pair r) := by
  rw [run_encode]
  change (run e).bind (fun k => (Code.pair (Code.const r) Code.id).eval k) = _
  have hp : ∀ k, (Code.pair (Code.const r) Code.id).eval k = Part.some (Nat.pair r k) := by
    intro k
    simp [Code.eval, Code.eval_const, Code.eval_id, Seq.seq]
  simp_rw [hp]
  exact Part.bind_some_eq_map _ _

/-- Products supply the explicit context retained by uniform iteration. -/
def liftStrength (Γ A : Assembly.{u}) : Hom (prod Γ (programLift A)) (programLift (prod Γ A)) where
  toFun x := x.2.map (fun a => (x.1,a))
  tracked := by
    have hp := Computable.encode.comp (strengthCode_computable.comp Computable.unpair)
    refine ⟨fun z => Part.some (encode (strengthCode z.unpair)), Partrec.nat_iff.mp hp, ?_⟩
    rintro ⟨γ,t⟩ z ⟨hγ, ht⟩
    refine ⟨encode (strengthCode z.unpair), by simp, ?_⟩
    cases t with
    | none =>
      change ¬ (run (encode (strengthCode z.unpair))).Dom
      rw [strengthCode_run]
      exact ht
    | some a =>
      obtain ⟨e, he, ha⟩ := ht
      refine ⟨Nat.pair z.unpair.1 e, ?_, ?_⟩
      · rw [strengthCode_run]
        exact Part.mem_map _ he
      · simpa [prod] using And.intro hγ ha

end Realizability.Assembly
