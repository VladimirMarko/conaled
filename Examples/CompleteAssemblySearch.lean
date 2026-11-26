import Examples.CompleteAssemblyFunctions

/-! Program-level controls for the constructed extension compiler. -/
namespace CompleteAssemblySearch
open Realizability Realizability.Assembly InternalIteration Encodable Denumerable
open Nat.Partrec (Code)

/-- Full-cut labels need not be canonical: the compiler observes termination. -/
theorem search_keeps_selected (p : Code)
    (hp : Tracks (prod natAssembly iterationCuts) (programLift natAssembly) p.eval
      (strictIteration liftedNaturals chooseParameter).toFun) :
    17 ∈ run (encode (searchCode (encode (observerCode p 17)) (encode (Code.const 99)))) := by
  apply (searchCode_observerCode_mem hp (γ := (17 : Nat)) rfl _ _).mpr
  exact ⟨1, Or.inr (by simp [Code.eval_const]), parameter_iteration_one⟩

/-- The tracker emits a partial program even when no finite observation succeeds. -/
theorem search_zero_cut_diverges (p : Code)
    (hp : Tracks (prod natAssembly iterationCuts) (programLift natAssembly) p.eval
      (strictIteration liftedNaturals chooseParameter).toFun) :
    ¬ (run (encode (searchCode (encode (observerCode p 17)) (encode (cutCode 0))))).Dom := by
  intro hd
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hd
  obtain ⟨n, hn, hnvalue⟩ := (searchCode_observerCode_mem hp (γ := (17 : Nat)) rfl _ v).mp hv
  have he : finalCuts.{0}.Realizes (encode (cutCode 0)) ⟨some 0⟩ := cutCode_realizes 0
  have hz : n = 0 := by have := (accessible_final he).mp hn; omega
  subst n
  cases hnvalue

example : ∃ p : Code,
    Tracks (prod natAssembly iterationCuts) (programLift natAssembly) p.eval
      (strictIteration liftedNaturals chooseParameter).toFun ∧
    17 ∈ run (encode (searchCode (encode (observerCode p 17)) (encode (Code.const 99)))) ∧
    ¬ (run (encode (searchCode (encode (observerCode p 17)) (encode (cutCode 0))))).Dom := by
  obtain ⟨p,hp⟩ := (strictIteration liftedNaturals chooseParameter).has_code
  exact ⟨p,hp,search_keeps_selected p hp,search_zero_cut_diverges p hp⟩

def emptyContext : Assembly where
  Carrier := Empty
  Realizes _ _ := False
  inhabited x := x.elim

example : Function.Bijective (fun h : Hom (prod emptyContext finalCuts) (programLift natAssembly) =>
    (cutContextInclusion emptyContext).comp h) := programLift_encoded_nat_cutComplete emptyContext

end CompleteAssemblySearch
