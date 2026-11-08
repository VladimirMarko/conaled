import SquareKit.AssemblySequenceFilter

/-! Complete bounded fibers and uniform extension of context-dependent bounds. -/
namespace Realizability.Assembly

/-- Every defined value obeys the independently stated coordinate bound. -/
def SequenceBounded (n : Nat) (q : partialSequences.Carrier) : Prop :=
  ∀ k v : Nat, q.toFun k = some v → v < n+k+1

theorem sequenceFilter_bounded (n : Nat) (q : partialSequences.Carrier) :
    SequenceBounded n (sequenceFilter.toFun (n,q)) := by
  intro k v hv
  have he := sequenceFilter_apply n q k
  have hv' : (q.toFun k).filter (fun v => v < n+k+1) = some v := he.symm.trans hv
  exact of_decide_eq_true (Option.filter_eq_some_iff.mp hv').2

theorem sequenceFilter_fixed_iff (n : Nat) (q : partialSequences.Carrier) :
    sequenceFilter.toFun (n,q) = q ↔ SequenceBounded n q := by
  constructor
  · intro h
    exact h ▸ sequenceFilter_bounded n q
  · intro h
    apply Hom.ext
    intro k
    change Nat at k
    have he := sequenceFilter_apply n q k
    refine he.trans ?_
    cases hk : q.toFun k with
    | none => rfl
    | some v =>
      change Nat at v
      change (some v : Option Nat).filter (fun w => w < n+k+1) = some v
      simp [h k v hk]

theorem sequenceFilter_idempotent (n : Nat) (q : partialSequences.Carrier) :
    sequenceFilter.toFun (n, sequenceFilter.toFun (n,q)) = sequenceFilter.toFun (n,q) :=
  (sequenceFilter_fixed_iff _ _).mpr (sequenceFilter_bounded n q)

def boundedSequences (n : Nat) : Assembly := restrict partialSequences (SequenceBounded n)

def natConstant (Γ : Assembly) (n : Nat) : Hom Γ (encoded Nat) where
  toFun _ := n
  tracked := by
    refine ⟨fun _ => Part.some n, Nat.Partrec.of_primrec (Nat.Primrec.const n), ?_⟩
    intro x e he
    exact ⟨n, by simp, rfl⟩

noncomputable def boundedRetraction (n : Nat) : Hom partialSequences (boundedSequences n) :=
  factor (SequenceBounded n) ((pair (natConstant _ n) (Hom.id _)).comp sequenceFilter)
    (sequenceFilter_bounded n)

theorem bounded_retract (n : Nat) :
    (inclusion partialSequences (SequenceBounded n)).comp (boundedRetraction n) =
      Hom.id (boundedSequences n) := by
  apply Hom.ext
  intro q
  apply Subtype.ext
  exact (sequenceFilter_fixed_iff n q.val).mpr q.property

theorem boundedSequences_complete (n : Nat) : CutComplete (boundedSequences n) :=
  retract_cutComplete partialSequences_complete _ _ (bounded_retract n)

/-- The capacity is read through an admitted arrow from an arbitrary context. -/
noncomputable def contextualFilter {Γ : Assembly} (capacity : Hom Γ (encoded Nat)) :
    Hom (prod Γ partialSequences) partialSequences :=
  (contextMap capacity partialSequences).comp sequenceFilter

/-- Extension stays in the varying bounded family by uniqueness in the ambient
complete sequence object. No completeness of arbitrary slices is assumed. -/
theorem bounded_extension {Γ : Assembly} (capacity : Hom Γ (encoded Nat))
    (h : Hom (prod Γ iterationCuts) partialSequences)
    (hb : ∀ γ n, SequenceBounded (capacity.toFun γ) (h.toFun (γ, ⟨n⟩)))
    (γ : Γ.Carrier) (t : finalCuts.{0}.Carrier) :
    SequenceBounded (capacity.toFun γ) ((cutExtend partialSequences_complete h).toFun (γ,t)) := by
  have he : (pair (fst Γ finalCuts) (cutExtend partialSequences_complete h)).comp
      (contextualFilter capacity) = cutExtend partialSequences_complete h := by
    apply (partialSequences_complete Γ).1
    apply Hom.ext
    rintro ⟨δ, ⟨n⟩⟩
    have hv := cutExtend_value partialSequences_complete h δ n
    change sequenceFilter.toFun (capacity.toFun δ,
      (cutExtend partialSequences_complete h).toFun (δ, ⟨some n⟩)) =
      (cutExtend partialSequences_complete h).toFun (δ, ⟨some n⟩)
    exact (congrArg (fun q => sequenceFilter.toFun (capacity.toFun δ,q)) hv).trans
      (((sequenceFilter_fixed_iff _ _).mpr (hb δ n)).trans hv.symm)
  exact (sequenceFilter_fixed_iff _ _).mp (congrArg (fun f => f.toFun (γ,t)) he)

end Realizability.Assembly
