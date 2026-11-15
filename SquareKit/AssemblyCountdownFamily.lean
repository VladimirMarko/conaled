import SquareKit.AssemblyCountdownExtension

/-! Selection in the common complete object factors through bounded fibers and families. -/
namespace Realizability.Assembly

noncomputable def boundedCountdown {Γ : Assembly} (n : Nat) (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n) :
    Hom (prod Γ (boundedSequences n)) (boundedSequences n) :=
  factor _ (((pair (fst _ _) ((snd _ _).comp (inclusion _ _)))).comp (countdown enabled seed))
    (fun x => countdown_bounded enabled seed x.1 n (hs x.1) x.2.property)

theorem boundedCountdown_square {Γ : Assembly} (n : Nat) (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n) :
    (boundedCountdown n enabled seed hs).comp (boundedSequenceInclusion n).f =
      (pair (fst _ _) ((snd _ _).comp (boundedSequenceInclusion n).f)).comp
        (countdown enabled seed) := Hom.ext fun _ => rfl

theorem boundedCountdown_selected_inclusion {Γ : Assembly} (n : Nat) (enabled : Hom Γ (encoded Bool))
    (seed : Hom Γ (encoded Nat)) (hs : ∀ γ, Nat.le (seed.toFun γ) n) :
    (cutSelected (boundedSequenceAlgebra n) (boundedSequences_complete n)
      (boundedCountdown n enabled seed hs)).comp (boundedSequenceInclusion n).f =
        cutSelected sequenceAlgebra partialSequences_complete (countdown enabled seed) :=
  cutSelected_transport _ _ (boundedSequences_complete n) partialSequences_complete
    (boundedSequenceInclusion n) _ _ (boundedCountdown_square n enabled seed hs)

theorem countdown_selected_bounded {Γ : Assembly} (capacity : Hom Γ (encoded Nat))
    (enabled : Hom Γ (encoded Bool)) (seed : Hom Γ (encoded Nat))
    (hs : ∀ γ, Nat.le (seed.toFun γ) (capacity.toFun γ)) (γ : Γ.Carrier) :
    SequenceBounded (capacity.toFun γ)
      ((cutSelected sequenceAlgebra partialSequences_complete (countdown enabled seed)).toFun γ) :=
  bounded_extension capacity _
    (fun δ fuel => countdown_iteration_bounded enabled seed δ _ (hs δ) fuel) γ ⟨none⟩

/-- This is a section of the varying family, not a choice of a global bottom capacity. -/
noncomputable def countdownSelectedFamily {Γ : Assembly} (capacity : Hom Γ (encoded Nat))
    (enabled : Hom Γ (encoded Bool)) (seed : Hom Γ (encoded Nat))
    (hs : ∀ γ, Nat.le (seed.toFun γ) (capacity.toFun γ)) : Hom Γ (boundedFamily capacity) :=
  factor _ (pair (Hom.id Γ)
    (cutSelected sequenceAlgebra partialSequences_complete (countdown enabled seed)))
    (countdown_selected_bounded capacity enabled seed hs)

theorem countdownSelectedFamily_base {Γ : Assembly} (capacity : Hom Γ (encoded Nat))
    (enabled : Hom Γ (encoded Bool)) (seed : Hom Γ (encoded Nat))
    (hs : ∀ γ, Nat.le (seed.toFun γ) (capacity.toFun γ)) :
    (countdownSelectedFamily capacity enabled seed hs).comp (familyBase capacity) = Hom.id Γ :=
  Hom.ext fun _ => rfl

theorem countdownSelectedFamily_reindex {Γ Δ : Assembly} (capacity : Hom Γ (encoded Nat))
    (enabled : Hom Γ (encoded Bool)) (seed : Hom Γ (encoded Nat))
    (hs : ∀ γ, Nat.le (seed.toFun γ) (capacity.toFun γ)) (σ : Hom Δ Γ) :
    (countdownSelectedFamily (σ.comp capacity) (σ.comp enabled) (σ.comp seed)
      (fun δ => hs (σ.toFun δ))).comp (familyReindex capacity σ) =
        σ.comp (countdownSelectedFamily capacity enabled seed hs) := by
  apply Hom.ext
  intro δ
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (congrArg (fun f => f.toFun δ)
      (cutSelected_substitution sequenceAlgebra partialSequences_complete
        (countdown enabled seed) σ)).symm

end Realizability.Assembly
