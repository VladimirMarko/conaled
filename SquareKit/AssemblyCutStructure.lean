import SquareKit.AssemblyCutPrograms

/-! The cut endofunctor algebra and coalgebra, with actual tracked inverses. -/
universe u
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

private theorem bind_dom_at {p : Part Nat} {m : Nat} (hm : m ∈ p) (f : Nat → Part Nat) :
    (p.bind f).Dom ↔ (f m).Dom := by
  have he : p = Part.some m := Part.eq_some_iff.mpr hm
  rw [he, Part.bind_some]

noncomputable def cutRoll : Hom (programLift iterationCuts.{u}) iterationCuts.{u} where
  toFun x := ⟨x.elim 0 (fun n => n.down + 1)⟩
  tracked := by
    refine ⟨fun e => Part.some (encode (rollCode e)),
      Partrec.nat_iff.mp (Computable.encode.comp rollCode_computable), ?_⟩
    intro x e he
    refine ⟨encode (rollCode e), by simp, ?_⟩
    intro k
    simp only [Denumerable.ofNat_encode, rollCode_eval, rollProgram]
    cases x with
    | none =>
      constructor
      · intro h
        exact (he h.1).elim
      · exact fun h => (Nat.not_lt_zero k h).elim
    | some n =>
      obtain ⟨m, hm, hn⟩ := he
      rw [bind_dom_at hm]
      cases k with
      | zero => simp
      | succ k => simpa using hn k

noncomputable def cutUnroll : Hom iterationCuts.{u} (programLift iterationCuts.{u}) where
  toFun n := n.down.casesOn none (fun k => some ⟨k⟩)
  tracked := by
    refine ⟨fun e => Part.some (encode (unrollCode e)),
      Partrec.nat_iff.mp (Computable.encode.comp unrollCode_computable), ?_⟩
    rintro ⟨n⟩ e he
    refine ⟨encode (unrollCode e), by simp, ?_⟩
    cases n with
    | zero =>
      change ¬ (run (encode (unrollCode e))).Dom
      rw [unrollCode_run]
      exact fun hd => Nat.not_lt_zero 0 ((he 0).mp hd)
    | succ n =>
      refine ⟨encode (shiftCode e), ?_, Cut.shift he⟩
      rw [unrollCode_run]
      obtain ⟨m, hm⟩ := Part.dom_iff_mem.mp ((he 0).mpr (Nat.zero_lt_succ n))
      exact Part.mem_map _ hm

theorem cutRoll_unroll : cutRoll.comp cutUnroll = Hom.id (programLift iterationCuts.{u}) := by
  apply Hom.ext
  intro x
  cases x <;> rfl

theorem cutUnroll_roll : cutUnroll.comp cutRoll = Hom.id iterationCuts.{u} := by
  apply Hom.ext
  rintro ⟨n⟩
  cases n <;> rfl

noncomputable def cutSuccessor : Hom iterationCuts.{u} iterationCuts.{u} :=
  (programLiftUnit iterationCuts).comp cutRoll

noncomputable def finalRoll : Hom (programLift finalCuts.{u}) finalCuts.{u} where
  toFun x := ⟨x.elim (some 0) (fun n => n.down.map Nat.succ)⟩
  tracked := by
    refine ⟨fun e => Part.some (encode (rollCode e)),
      Partrec.nat_iff.mp (Computable.encode.comp rollCode_computable), ?_⟩
    intro x e he
    refine ⟨encode (rollCode e), by simp, ?_⟩
    cases x with
    | none =>
      intro k
      simp only [Denumerable.ofNat_encode, rollCode_eval, rollProgram]
      exact ⟨fun h => (he h.1).elim, fun h => (Nat.not_lt_zero k h).elim⟩
    | some n =>
      obtain ⟨m, hm, hn⟩ := he
      rcases n with ⟨n⟩
      cases n with
      | none =>
        intro k
        simp only [Denumerable.ofNat_encode, rollCode_eval, rollProgram]
        apply (bind_dom_at hm _).mpr
        cases k with
        | zero => trivial
        | succ k => exact hn k
      | some n =>
        intro k
        simp only [Denumerable.ofNat_encode, rollCode_eval, rollProgram]
        rw [bind_dom_at hm]
        cases k with
        | zero => simp
        | succ k => simpa using hn k

noncomputable def finalUnroll : Hom finalCuts.{u} (programLift finalCuts.{u}) where
  toFun n := match n.down with
    | none => some ⟨none⟩
    | some 0 => none
    | some (n + 1) => some ⟨some n⟩
  tracked := by
    refine ⟨fun e => Part.some (encode (unrollCode e)),
      Partrec.nat_iff.mp (Computable.encode.comp unrollCode_computable), ?_⟩
    rintro ⟨n⟩ e he
    refine ⟨encode (unrollCode e), by simp, ?_⟩
    cases n with
    | none =>
      refine ⟨encode (shiftCode e), ?_, FullCut.shift he⟩
      rw [unrollCode_run]
      obtain ⟨m, hm⟩ := Part.dom_iff_mem.mp (he 0)
      exact Part.mem_map _ hm
    | some n =>
      cases n with
      | zero =>
        change ¬ (run (encode (unrollCode e))).Dom
        rw [unrollCode_run]
        exact fun hd => Nat.not_lt_zero 0 ((he 0).mp hd)
      | succ n =>
        refine ⟨encode (shiftCode e), ?_, Cut.shift he⟩
        rw [unrollCode_run]
        obtain ⟨m, hm⟩ := Part.dom_iff_mem.mp ((he 0).mpr (Nat.zero_lt_succ n))
        exact Part.mem_map _ hm

theorem finalRoll_unroll : finalRoll.comp finalUnroll = Hom.id (programLift finalCuts.{u}) := by
  apply Hom.ext
  intro x
  cases x with
  | none => rfl
  | some n => rcases n with ⟨n⟩; cases n <;> rfl

theorem finalUnroll_roll : finalUnroll.comp finalRoll = Hom.id finalCuts.{u} := by
  apply Hom.ext
  rintro ⟨n⟩
  cases n with
  | none => rfl
  | some n => cases n <;> rfl

noncomputable def finalSuccessor : Hom finalCuts.{u} finalCuts.{u} :=
  (programLiftUnit finalCuts).comp finalRoll

theorem inclusion_successor : cutSuccessor.comp cutInclusion =
    cutInclusion.comp finalSuccessor := Hom.ext fun _ => rfl

theorem infinity_successor (A : Assembly.{u}) :
    (cutInfinity A).comp finalSuccessor = cutInfinity A := Hom.ext fun _ => rfl

end Realizability.Assembly
