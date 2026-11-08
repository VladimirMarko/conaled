import SquareKit.AssemblyBoundedFamily

/-! Relative extension commutes with every admitted parameter substitution. -/
namespace Realizability.Assembly

noncomputable def reindexFamilySection {Γ Δ : Assembly} (capacity : Hom Γ (encoded Nat))
    (f : Hom Δ Γ) (T : Assembly)
    (h : Hom (prod Γ T) (boundedFamily capacity))
    (hb : h.comp (familyBase capacity) = fst Γ T) :
    Hom (prod Δ T) (boundedFamily (f.comp capacity)) :=
  factor _ (pair (fst Δ T) (((contextMap f T).comp h).comp (familySequence capacity)))
    (fun x => by
      have hp := (h.toFun (f.toFun x.1,x.2)).property
      have he := congrArg (fun k => k.toFun (f.toFun x.1,x.2)) hb
      change (h.toFun (f.toFun x.1,x.2)).val.1 = f.toFun x.1 at he
      exact (congrArg (fun γ => SequenceBounded (capacity.toFun γ)
        (h.toFun (f.toFun x.1,x.2)).val.2) he) ▸ hp)

theorem reindexFamilySection_base {Γ Δ : Assembly} (capacity : Hom Γ (encoded Nat))
    (f : Hom Δ Γ) (T : Assembly)
    (h : Hom (prod Γ T) (boundedFamily capacity))
    (hb : h.comp (familyBase capacity) = fst Γ T) :
    (reindexFamilySection capacity f T h hb).comp (familyBase (f.comp capacity)) = fst Δ T :=
  Hom.ext fun _ => rfl

theorem reindexFamilySection_square {Γ Δ : Assembly} (capacity : Hom Γ (encoded Nat))
    (f : Hom Δ Γ) (T : Assembly)
    (h : Hom (prod Γ T) (boundedFamily capacity))
    (hb : h.comp (familyBase capacity) = fst Γ T) :
    (reindexFamilySection capacity f T h hb).comp (familyReindex capacity f) =
      (contextMap f T).comp h := by
  apply Hom.ext
  intro x
  apply Subtype.ext
  exact Prod.ext (congrArg (fun k => k.toFun (f.toFun x.1,x.2)) hb).symm rfl

theorem extendFamily_reindex {Γ Δ : Assembly} (capacity : Hom Γ (encoded Nat)) (f : Hom Δ Γ)
    (h : Hom (prod Γ iterationCuts) (boundedFamily capacity))
    (hb : h.comp (familyBase capacity) = fst Γ iterationCuts) :
    reindexFamilySection capacity f finalCuts (extendFamily capacity h hb)
        (extendFamily_base capacity h hb) =
      extendFamily (f.comp capacity) (reindexFamilySection capacity f iterationCuts h hb)
        (reindexFamilySection_base capacity f iterationCuts h hb) := by
  apply Hom.ext
  intro x
  apply Subtype.ext
  exact Prod.ext rfl (congrArg (fun k => k.toFun x)
    (cutExtend_substitution partialSequences_complete (h.comp (familySequence capacity)) f))

theorem reindexFamilySection_comp {Γ Δ Θ : Assembly} (capacity : Hom Γ (encoded Nat))
    (f : Hom Δ Γ) (g : Hom Θ Δ) (T : Assembly)
    (h : Hom (prod Γ T) (boundedFamily capacity))
    (hb : h.comp (familyBase capacity) = fst Γ T) :
    reindexFamilySection (f.comp capacity) g T (reindexFamilySection capacity f T h hb)
        (reindexFamilySection_base capacity f T h hb) =
      reindexFamilySection capacity (g.comp f) T h hb := Hom.ext fun _ => rfl

end Realizability.Assembly
