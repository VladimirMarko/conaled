import SquareKit.AssemblyBoundedSequences

/-! Relative extension for the actual capacity-indexed bounded family. -/
namespace Realizability.Assembly

def boundedFamily {Γ : Assembly} (capacity : Hom Γ (encoded Nat)) : Assembly :=
  restrict (prod Γ partialSequences) fun x => SequenceBounded (capacity.toFun x.1) x.2

def familyBase {Γ : Assembly} (capacity : Hom Γ (encoded Nat)) : Hom (boundedFamily capacity) Γ :=
  (inclusion _ _).comp (fst _ _)

def familySequence {Γ : Assembly} (capacity : Hom Γ (encoded Nat)) :
    Hom (boundedFamily capacity) partialSequences := (inclusion _ _).comp (snd _ _)

theorem family_finite_bounded {Γ : Assembly} (capacity : Hom Γ (encoded Nat))
    (h : Hom (prod Γ iterationCuts) (boundedFamily capacity))
    (hb : h.comp (familyBase capacity) = fst Γ iterationCuts) (γ : Γ.Carrier) (n : Nat) :
    SequenceBounded (capacity.toFun γ) ((h.comp (familySequence capacity)).toFun (γ, ⟨n⟩)) := by
  have hp := (h.toFun (γ, ⟨n⟩)).property
  have he := congrArg (fun f => f.toFun (γ, ⟨n⟩)) hb
  change (h.toFun (γ, ⟨n⟩)).val.1 = γ at he
  exact (congrArg (fun δ => SequenceBounded (capacity.toFun δ)
    (h.toFun (γ, ⟨n⟩)).val.2) he) ▸ hp

noncomputable def extendFamily {Γ : Assembly} (capacity : Hom Γ (encoded Nat))
    (h : Hom (prod Γ iterationCuts) (boundedFamily capacity))
    (hb : h.comp (familyBase capacity) = fst Γ iterationCuts) :
    Hom (prod Γ finalCuts) (boundedFamily capacity) :=
  factor _ (pair (fst Γ finalCuts)
    (cutExtend partialSequences_complete (h.comp (familySequence capacity))))
    (fun x => bounded_extension capacity _ (family_finite_bounded capacity h hb) x.1 x.2)

theorem extendFamily_base {Γ : Assembly} (capacity : Hom Γ (encoded Nat))
    (h : Hom (prod Γ iterationCuts) (boundedFamily capacity))
    (hb : h.comp (familyBase capacity) = fst Γ iterationCuts) :
    (extendFamily capacity h hb).comp (familyBase capacity) = fst Γ finalCuts := Hom.ext fun _ => rfl

theorem extendFamily_restrict {Γ : Assembly} (capacity : Hom Γ (encoded Nat))
    (h : Hom (prod Γ iterationCuts) (boundedFamily capacity))
    (hb : h.comp (familyBase capacity) = fst Γ iterationCuts) :
    (cutContextInclusion Γ).comp (extendFamily capacity h hb) = h := by
  apply Hom.ext
  rintro ⟨γ, ⟨n⟩⟩
  apply Subtype.ext
  apply Prod.ext
  · exact (congrArg (fun f => f.toFun (γ, ⟨n⟩)) hb).symm
  · exact cutExtend_value partialSequences_complete _ γ n

theorem family_extension_unique {Γ : Assembly} (capacity : Hom Γ (encoded Nat))
    (h k : Hom (prod Γ finalCuts) (boundedFamily capacity))
    (hb : h.comp (familyBase capacity) = fst Γ finalCuts)
    (kb : k.comp (familyBase capacity) = fst Γ finalCuts)
    (he : (cutContextInclusion Γ).comp h = (cutContextInclusion Γ).comp k) : h = k := by
  have hv : h.comp (familySequence capacity) = k.comp (familySequence capacity) :=
    (partialSequences_complete Γ).1 (congrArg (fun f => f.comp (familySequence capacity)) he)
  apply Hom.ext
  intro x
  apply Subtype.ext
  exact Prod.ext
    ((congrArg (fun f => f.toFun x) hb).trans (congrArg (fun f => f.toFun x) kb).symm)
    (congrArg (fun f => f.toFun x) hv)

/-- Restriction is bijective on tracked sections retaining their base. -/
theorem boundedFamily_complete {Γ : Assembly} (capacity : Hom Γ (encoded Nat)) :
    Function.Bijective (fun h : {h : Hom (prod Γ finalCuts) (boundedFamily capacity) //
        h.comp (familyBase capacity) = fst Γ finalCuts} =>
      (⟨(cutContextInclusion Γ).comp h.val,
        (congrArg (fun f => (cutContextInclusion Γ).comp f) h.property)⟩ :
        {h : Hom (prod Γ iterationCuts) (boundedFamily capacity) //
          h.comp (familyBase capacity) = fst Γ iterationCuts})) := by
  constructor
  · intro h k he
    apply Subtype.ext
    exact family_extension_unique capacity _ _ h.property k.property (congrArg Subtype.val he)
  · intro h
    exact ⟨⟨extendFamily capacity h.val h.property, extendFamily_base capacity h.val h.property⟩,
      Subtype.ext (extendFamily_restrict capacity h.val h.property)⟩

/-- Every tracked base change, including non-surjective ones, preserves the family. -/
def familyReindex {Γ Δ : Assembly} (capacity : Hom Γ (encoded Nat)) (f : Hom Δ Γ) :
    Hom (boundedFamily (f.comp capacity)) (boundedFamily capacity) :=
  factor _ ((inclusion _ _).comp (contextMap f partialSequences)) (fun x => x.property)

theorem familyReindex_comp {Γ Δ Θ : Assembly} (capacity : Hom Γ (encoded Nat))
    (f : Hom Δ Γ) (g : Hom Θ Δ) :
    (familyReindex (f.comp capacity) g).comp (familyReindex capacity f) =
      familyReindex capacity (g.comp f) := Hom.ext fun _ => rfl

end Realizability.Assembly
