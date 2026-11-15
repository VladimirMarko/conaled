import Examples.UniformCertificateStates
import SquareKit.AssemblyBoundedSequences

/-! The complete bounded sequence object represents uniformly realizable certificate states. -/
namespace AssemblyCertificateFamily
open VaryingPartialCertificates UniformCertificateStates
open Realizability Realizability.Assembly Encodable Denumerable CategoryTheory
open Nat.Partrec (Code)

noncomputable def recover {n : Nat} (q : (boundedSequences n).Carrier) : State n := fun k =>
  match h : q.val.toFun k with
  | none => Part.none
  | some v => Part.some ⟨⟨v, q.property k v h⟩, IndexedPartialComputation.trace k, rfl⟩

theorem recover_graph {n : Nat} (q : (boundedSequences n).Carrier) (k v : Nat) :
    (∃ a : Cert n k, a ∈ recover q k ∧ a.value.val = v) ↔ q.val.toFun k = some v := by
  unfold recover
  split <;> simp_all
  exact ⟨congrArg some, Option.some.inj⟩

theorem recover_coordinate {n : Nat} (q : (boundedSequences n).Carrier) (k : Nat) :
    coordinate (recover q) k = q.val.toFun k := by
  apply Option.ext
  intro v
  exact (coordinate_eq_some _ _ _).trans (recover_graph q k v)

theorem recover_realizer_iff {n e : Nat} (q : (boundedSequences n).Carrier) :
    StateRealizer e (recover q) ↔ partialSequences.realizes e q.val := by
  constructor
  · intro hr k r hk
    change r = k at hk
    subst r
    obtain ⟨c, hc, hs⟩ := hr k
    refine ⟨c, hc, liftNat_realizes_iff.mpr ?_⟩
    intro v
    exact (hs v).trans (recover_graph q k v)
  · intro hr k
    obtain ⟨c, hc, hs⟩ := hr k k rfl
    refine ⟨c, hc, fun v => ?_⟩
    exact (liftNat_realizes_iff.mp hs v).trans (recover_graph q k v).symm

noncomputable def toStates (n : Nat) : Hom (boundedSequences n) (stateAssembly n) where
  toFun q := ⟨recover q, by
    obtain ⟨e, he⟩ := partialSequences.inhabited q.val
    exact ⟨e, (recover_realizer_iff q).mpr he⟩⟩
  tracked := ⟨Part.some, Nat.Partrec.some, fun q e he =>
    ⟨e, by simp, (recover_realizer_iff q).mpr he⟩⟩

noncomputable def stateSequence {n : Nat} (q : State n) (hq : UniformRealizable q) :
    Hom (encoded Nat) (programLift (encoded Nat)) where
  toFun := coordinate q
  tracked := by
    obtain ⟨e, he⟩ := hq
    refine ⟨(ofNat Code e).eval,
      Partrec.nat_iff.mp (Code.eval_part.comp (Computable.const _) Computable.id), ?_⟩
    intro k r hr
    change r = k at hr
    subst r
    obtain ⟨c, hc, hs⟩ := he k
    refine ⟨c, hc, liftNat_realizes_iff.mpr ?_⟩
    intro v
    exact (hs v).trans (coordinate_eq_some q k v).symm

theorem stateSequence_bounded {n : Nat} (q : State n) (hq : UniformRealizable q) :
    SequenceBounded n (stateSequence q hq) := by
  intro k v hv
  obtain ⟨a, _, ha⟩ := (coordinate_eq_some q k v).mp hv
  exact ha ▸ a.value.isLt

noncomputable def fromStates (n : Nat) : Hom (stateAssembly n) (boundedSequences n) where
  toFun q := ⟨stateSequence q.val q.property, stateSequence_bounded q.val q.property⟩
  tracked := by
    refine ⟨Part.some, Nat.Partrec.some, ?_⟩
    intro q e he
    refine ⟨e, by simp, ?_⟩
    intro k r hr
    change r = k at hr
    subst r
    obtain ⟨c, hc, hs⟩ := he k
    refine ⟨c, hc, liftNat_realizes_iff.mpr ?_⟩
    intro v
    exact (hs v).trans (coordinate_eq_some q.val k v).symm

noncomputable def stateComparison (n : Nat) : boundedSequences n ≅ stateAssembly n where
  hom := toStates n
  inv := fromStates n
  hom_inv_id := by
    apply Hom.ext
    intro q
    apply Subtype.ext
    apply Hom.ext
    intro k
    exact recover_coordinate q k
  inv_hom_id := by
    apply Hom.ext
    intro q
    apply Subtype.ext
    apply coordinate_injective
    funext k
    exact recover_coordinate (fromStates n |>.toFun q) k

/-- Forgetting the internal admission proof retains the entire external state. -/
noncomputable def forget (n : Nat) (q : (boundedSequences n).Carrier) : State n := recover q

theorem forget_injective (n : Nat) : Function.Injective (forget n) := by
  intro q r h
  apply Subtype.ext
  apply Hom.ext
  intro k
  exact (recover_coordinate q k).symm.trans
    ((congrArg (fun s => coordinate s k) h).trans (recover_coordinate r k))

end AssemblyCertificateFamily
