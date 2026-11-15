import SquareKit.AssemblyCutStructure

/-! Uniform iteration from finite cut realizers. -/
universe u
namespace Realizability.Assembly
open Encodable Denumerable
open Nat.Partrec (Code)

/-- The recursive call is delayed until the cut admits its first observation. -/
def foldDelay (c : Code) (r e : Nat) : Code := Code.comp (c.curry r) (unrollCode e)

theorem foldDelay_computable : Computable (fun p : Code × (Nat × Nat) =>
    foldDelay p.1 p.2.1 p.2.2) :=
  Code.primrec₂_comp.to_comp.comp
    (Code.primrec₂_curry.to_comp.comp Computable.fst (Computable.fst.comp Computable.snd))
    (unrollCode_computable.comp (Computable.snd.comp Computable.snd))

theorem foldDelay_run (c : Code) (r e : Nat) :
    run (encode (foldDelay c r e)) =
      (run e).bind (fun _ => c.eval (Nat.pair r (encode (shiftCode e)))) := by
  rw [run_encode]
  change ((unrollCode e).eval 0).bind (fun k => (c.curry r).eval k) = _
  have hu := unrollCode_run e
  rw [run_encode] at hu
  rw [hu]
  simp only [Part.bind_map, Code.eval_curry]

/-- The recursion theorem supplies a single program retaining the context
realizer `r`; it does not choose independent programs for each parameter. -/
theorem exists_fold_program (q : Code) : ∃ c : Code, ∀ r e,
    c.eval (Nat.pair r e) = q.eval (Nat.pair r (encode (foldDelay c r e))) := by
  have hpair : Computable (fun p : Code × Nat => (p.1, p.2.unpair)) :=
    (Computable.fst : Computable (@Prod.fst Code Nat)).pair
      (Computable.unpair.comp (Computable.snd : Computable (@Prod.snd Code Nat)))
  have hd : Computable (fun p : Code × Nat => foldDelay p.1 p.2.unpair.1 p.2.unpair.2) :=
    (foldDelay_computable.comp hpair).of_eq (fun _ => rfl)
  have hg : Computable (fun p : Code × Nat =>
      Nat.pair p.2.unpair.1 (encode (foldDelay p.1 p.2.unpair.1 p.2.unpair.2))) :=
    Computable₂.comp Primrec₂.pair.to_comp
      (Computable.fst.comp (Primrec.unpair.to_comp.comp Computable.snd))
      (Computable.encode.comp hd)
  have hp : Partrec₂ (fun c : Code => fun z : Nat =>
      q.eval (Nat.pair z.unpair.1 (encode (foldDelay c z.unpair.1 z.unpair.2)))) :=
    (Code.eval_part.comp (Computable.const q) hg).to₂
  obtain ⟨c, hc⟩ := Code.fixed_point₂ hp
  exact ⟨c, fun r e => by simpa using congrFun hc (Nat.pair r e)⟩

/-- External recursion defines the intended values; tracking below must use
cut observations, and cannot inspect their hidden finite length. -/
def cutFoldValue {Γ A : Assembly.{u}} (a : Hom (prod Γ (programLift A)) A)
    (γ : Γ.Carrier) : Nat → A.Carrier
  | 0 => a.toFun (γ, none)
  | n + 1 => a.toFun (γ, some (cutFoldValue a γ n))

/-- The single self-referential program tracks every context fiber uniformly. -/
theorem cutFold_tracked {Γ A : Assembly.{u}} (a : Hom (prod Γ (programLift A)) A) :
    ∃ φ, Nat.Partrec φ ∧ Tracks (prod Γ iterationCuts) A φ
      (fun x => cutFoldValue a x.1 x.2.down) := by
  obtain ⟨q, hq⟩ := a.has_code
  obtain ⟨c, hc⟩ := exists_fold_program q
  refine ⟨c.eval, Code.exists_code.mpr ⟨c, rfl⟩, ?_⟩
  suffices h : ∀ n γ r e, Γ.realizes r γ → Cut e n →
      ∃ v, v ∈ c.eval (Nat.pair r e) ∧ A.realizes v (cutFoldValue a γ n) by
    intro x z hz
    simpa using h x.2.down x.1 z.unpair.1 z.unpair.2 hz.1 hz.2
  intro n
  induction n with
  | zero =>
    intro γ r e hr he
    have hd : (programLift A).realizes (encode (foldDelay c r e)) none := by
      change ¬ (run (encode (foldDelay c r e))).Dom
      rw [foldDelay_run]
      exact fun h => Nat.not_lt_zero 0 ((he 0).mp h.1)
    obtain ⟨v, hv, hx⟩ := hq (γ, none) (Nat.pair r (encode (foldDelay c r e)))
      (by simpa [prod] using And.intro hr hd)
    exact ⟨v, (hc r e).symm ▸ hv, hx⟩
  | succ n ih =>
    intro γ r e hr he
    obtain ⟨v, hv, hx⟩ := ih γ r (encode (shiftCode e)) hr (Cut.shift he)
    have hd : (programLift A).realizes (encode (foldDelay c r e))
        (some (cutFoldValue a γ n)) := by
      refine ⟨v, ?_, hx⟩
      rw [foldDelay_run]
      obtain ⟨m, hm⟩ := Part.dom_iff_mem.mp ((he 0).mpr (Nat.zero_lt_succ n))
      exact Part.mem_bind_iff.mpr ⟨m, hm, hv⟩
    obtain ⟨w, hw, hy⟩ := hq (γ, some (cutFoldValue a γ n))
      (Nat.pair r (encode (foldDelay c r e))) (by simpa [prod] using And.intro hr hd)
    exact ⟨w, (hc r e).symm ▸ hw, hy⟩

noncomputable def cutFold {Γ A : Assembly.{u}} (a : Hom (prod Γ (programLift A)) A) :
    Hom (prod Γ iterationCuts) A :=
  ⟨fun x => cutFoldValue a x.1 x.2.down, cutFold_tracked a⟩

@[simp] theorem cutFold_zero {Γ A : Assembly.{u}} (a : Hom (prod Γ (programLift A)) A)
    (γ : Γ.Carrier) : (cutFold a).toFun (γ, ⟨0⟩) = a.toFun (γ, none) := rfl

@[simp] theorem cutFold_succ {Γ A : Assembly.{u}} (a : Hom (prod Γ (programLift A)) A)
    (γ : Γ.Carrier) (n : Nat) :
    (cutFold a).toFun (γ, ⟨n + 1⟩) = a.toFun (γ, some ((cutFold a).toFun (γ, ⟨n⟩))) := rfl

end Realizability.Assembly
