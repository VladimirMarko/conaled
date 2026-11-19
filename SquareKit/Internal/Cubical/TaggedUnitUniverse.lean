import SquareKit.Internal.Cubical.UniverseFilling
import SquareKit.Internal.Cubical.EquivalenceFamilies
import SquareKit.Internal.Cubical.DiscreteEquivalences
import SquareKit.Internal.PresheafFamilyClassification

/-! A fibrant discrete universe with two codes for the unit family.
This bounded universe supplies a decoder and lawful uniform fillers, but no
constructor or Glue closure. Its native path-to-equivalence map fails univalence. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.TaggedUnit
open CategoryTheory

/-- Discrete Boolean codes, stable under arbitrary context substitution. -/

abbrev codes (Γ : Context.{0}) := constantFamily Γ Bool

abbrev tag {Γ : Context.{0}} (b : Bool) : Term (codes Γ) := DiscreteEquivalences.constant b

/-- The actual universe context, with one closed code at each Boolean tag. -/

abbrev codeContext : Context.{0} := total (codes terminal)

/-- Both tags decode to the unit family. -/

abbrev decoder : Family codeContext := constantFamily codeContext PUnit

abbrev decoded {Γ : Context.{0}} (a : Term (codes Γ)) : Family Γ :=
  reindex decoder (pair (terminalSub Γ) a)

def constantFilling (Γ : Context.{0}) (S : Type) : Filling (constantFamily Γ S) :=
  discreteFilling (DiscreteEquivalences.constant (Γ := Γ) PUnit.unit) (fun _ => S)

theorem constantFilling_lawful (Γ : Context.{0}) (S : Type) :
    (constantFilling Γ S).Lawful :=
  discreteFilling_lawful (DiscreteEquivalences.constant (Γ := Γ) PUnit.unit) (fun _ => S)

def codeFilling (Γ : Context.{0}) : Filling (codes Γ) := constantFilling Γ Bool

def decoderFilling : Filling decoder := constantFilling codeContext PUnit

abbrev codeLine {Γ : Context.{0}} {a b : Term (codes Γ)}
    (p : Term (homogeneousPath (codes Γ) a b)) : total (interval Γ) ⟶ codeContext :=
  pair (terminalSub _) (pathApp p)

/-- Transport along a native code path uses the decoder's chosen filler. -/
noncomputable def pathEquivalence {Γ : Context.{0}} {a b : Term (codes Γ)}
    (p : Term (homogeneousPath (codes Γ) a b)) :
    Σ f : decoded a ⟶ decoded b, HomotopyEquivalence f :=
  ⟨IntervalTransport.map (decoderFilling.reindex (codeLine p)),
    IntervalTransport.equivalence (decoderFilling.reindex (codeLine p))
      ((constantFilling_lawful codeContext PUnit).reindex (codeLine p))⟩

/-- Native paths, not just equality of Lean codes, separate the two tags. -/

theorem no_path : IsEmpty (Term (homogeneousPath (codes terminal) (tag false) (tag true))) :=
  ⟨fun p => Bool.false_ne_true
    (congrArg (fun t => t.val DiscreteEquivalences.point) (discretePath_endpoints p))⟩

def sameFiber : decoded (tag (Γ := terminal) false) ≅ decoded (tag (Γ := terminal) true) := Iso.refl _

theorem pathEquivalence_not_surjective : ¬ Function.Surjective
    (@pathEquivalence terminal (tag false) (tag true)) := by
  intro h
  obtain ⟨p, _⟩ := h ⟨sameFiber.hom, HomotopyEquivalence.ofIso sameFiber⟩
  exact no_path.false p

abbrev paths {Γ : Context.{0}} (a b : Term (codes Γ)) := homogeneousPath (codes Γ) a b

abbrev equivalences {Γ : Context.{0}} (a b : Term (codes Γ)) :=
  EquivalenceFamilies.equiv (decoded a) (decoded b)
noncomputable def pathEquivalenceSection {Γ : Context.{0}} (a b : Term (codes Γ)) :
    Term (reindex (equivalences a b) (projection (paths a b))) :=
  EquivalenceFamilies.equivReindexSections (decoded a) (decoded b) (projection (paths a b))
    (pathEquivalence (Term.map (pathReindex (reindex (codes Γ) (projection (interval Γ)))
      a b (projection (paths a b))) (generic (paths a b))))

/-- Internalize transport with its full native contraction witnesses. -/
noncomputable def pathToEquiv {Γ : Context.{0}} (a b : Term (codes Γ)) :
    paths a b ⟶ equivalences a b :=
  IntervalTransport.mapOfSection (pathEquivalenceSection a b)

noncomputable def equivalentFibers : Term (equivalences (tag (Γ := terminal) false) (tag true)) :=
  EquivalenceFamilies.equivSections _ _ ⟨sameFiber.hom, HomotopyEquivalence.ofIso sameFiber⟩

/-- A hypothetical native equivalence would provide a forbidden tag path
from the fiber center over the existing identity equivalence of decoded units. -/

theorem not_univalent : ¬ Nonempty (HomotopyEquivalence
    (pathToEquiv (tag (Γ := terminal) false) (tag true))) := by
  rintro ⟨E⟩
  let f := pathToEquiv (tag (Γ := terminal) false) (tag true)
  let σ := pair (A := equivalences (tag (Γ := terminal) false) (tag true)) (𝟙 terminal) equivalentFibers
  exact no_path.false (genericFiberFst f σ (E.fibers.center.reindex σ))

theorem codes_fibrant (Γ : Context.{0}) : (codeFilling Γ).Lawful :=
  constantFilling_lawful Γ Bool

theorem decoder_fibrant : decoderFilling.Lawful :=
  constantFilling_lawful codeContext PUnit

theorem decoded_reindex {Γ Δ : Context.{0}} (a : Term (codes Γ)) (σ : Δ ⟶ Γ) :
    reindex (decoded a) σ = decoded (a.reindex σ) := rfl

def decodedFilling {Γ : Context.{0}} (a : Term (codes Γ)) : Filling (decoded a) :=
  decoderFilling.reindex (pair (terminalSub Γ) a)

theorem decodedFilling_lawful {Γ : Context.{0}} (a : Term (codes Γ)) :
    (decodedFilling a).Lawful := decoder_fibrant.reindex _

theorem decodedFilling_reindex {Γ Δ : Context.{0}} (a : Term (codes Γ)) (σ : Δ ⟶ Γ) :
    (decodedFilling a).reindex σ = decodedFilling (a.reindex σ) := rfl

/-- The ordinary shared decoder recovers the actual universal decoding family.
Its construction has no hypothesis about the tag universe's univalence. -/

def classifierRecovery :
    RepresentableClassification.PresheafFamily.system.decode
      RepresentableClassification.PresheafFamily.universalDecode
      (RepresentableClassification.PresheafFamily.system.code decoder) ≅ decoder :=
  RepresentableClassification.PresheafFamily.recovery decoder

end SquareKit.Cubical.Presheaf.TaggedUnit
