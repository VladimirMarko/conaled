import SquareKit.AssemblySequenceAlgebra
import SquareKit.AssemblyChoice

/-! A uniformly tracked countdown functional on partial sequences. -/
namespace Realizability.Assembly

/-- Coordinate zero supplies the seed; successors request the preceding coordinate. -/
def countdownValue (enabled : Bool) (seed : Nat) (q : Nat → Option Nat) (k : Nat) : Option Nat :=
  if enabled then if k = 0 then some seed else (q (k-1)).map Nat.succ else q k

noncomputable def countdown {Γ : Assembly} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) : Hom (prod Γ partialSequences) partialSequences := by
  let E := prod (prod Γ partialSequences) (encoded Nat)
  let ctx : Hom E Γ := (fst _ _).comp (fst _ _)
  let seq : Hom E partialSequences := (fst _ _).comp (snd _ _)
  let ix : Hom E (encoded Nat) := snd _ _
  let prev := ix.comp (ofComputable (fun k : Nat => k-1)
    (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)).to_comp)
  let current : Hom E (programLift (encoded Nat)) := (pair seq ix).comp (evaluation _ _)
  let before := ((pair seq prev).comp (evaluation _ _)).comp
    (programLiftMap (ofComputable Nat.succ Computable.succ))
  let start := (ctx.comp seed).comp (programLiftUnit _)
  let zero := ix.comp (ofComputable (fun k : Nat => if k = 0 then true else false)
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
      (Primrec.const true) (Primrec.const false)).to_comp)
  let next := (pair zero (pair start before)).comp (booleanChoice _)
  exact curry ((pair (ctx.comp enabled) (pair next current)).comp (booleanChoice _))

theorem countdown_apply {Γ : Assembly} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (γ : Γ.Carrier) (q : partialSequences.Carrier) (k : Nat) :
    ((countdown enabled seed).toFun (γ,q)).toFun k =
      countdownValue (enabled.toFun γ) (seed.toFun γ) q.toFun k := by
  unfold countdown
  change (cond (enabled.toFun γ) (cond (if k = 0 then true else false) (some (seed.toFun γ))
    ((q.toFun (k-1)).map Nat.succ)) (q.toFun k)) = _
  cases enabled.toFun γ <;> by_cases h : k = 0 <;> simp [countdownValue, h, cond] <;> rfl

theorem countdown_bounded {Γ : Assembly} (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (γ : Γ.Carrier) (n : Nat) (hs : Nat.le (seed.toFun γ) n)
    {q : partialSequences.Carrier} (hq : SequenceBounded n q) :
    SequenceBounded n ((countdown enabled seed).toFun (γ,q)) := by
  intro k v hv
  rw [countdown_apply] at hv
  unfold countdownValue at hv
  cases he : enabled.toFun γ with
  | false => simp only [he, Bool.false_eq_true, ↓reduceIte] at hv; exact hq k v hv
  | true =>
    simp only [he, ↓reduceIte] at hv
    split at hv
    · have h := Option.some.inj hv
      have hn : v ≤ n := (congrArg (fun s : Nat => s ≤ n) h).mp hs
      omega
    · obtain ⟨w, hw, he⟩ := Option.map_eq_some_iff.mp hv
      have hb := hq (k-1) w hw
      change Nat.succ w = v at he
      omega

end Realizability.Assembly
