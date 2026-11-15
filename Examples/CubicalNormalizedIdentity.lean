import SquareKit.Internal.Cubical.NormalizedIdentityElimination
import Examples.CubicalIdentityFilling

/-! The normalized marked Id retains its selected witness, chosen filler,
and strict dependent branch. These examples do not claim a nonzero higher class. -/
namespace Examples.CubicalNormalizedIdentity
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
  CubicalPresheaf CubicalDiscreteFilling CubicalIdentity

abbrev normalizedUnmarked : Term (normalizedIdentity fiber finiteLast finiteLast) :=
  Term.map (normalizedIdentityIso fiber finiteLast finiteLast).hom unmarked

theorem roundtrip : Term.map (normalizedIdentityIso fiber finiteLast finiteLast).inv normalizedUnmarked = unmarked :=
  Term.map_iso_roundtrip _ unmarked

theorem selected_face_retained :
    (normalizedUnmarked.val (naturals.elementsMk (Opposite.op ⟨0⟩) (2 : ℕ))).val.2 = Face.bot 0 := rfl

theorem refl_replacement_rejected : normalizedUnmarked ≠ normalizedIdentityRefl finiteLast := by
  intro h
  have he := congrArg (fun t => Term.map (normalizedIdentityIso fiber finiteLast finiteLast).inv t) h
  exact markers_retained (roundtrip.symm.trans (he.trans (Term.map_iso_roundtrip _ (identityRefl finiteLast))))

noncomputable abbrev provider := normalizedIdentityFilling (discreteFilling index (fun n => Fin (n+1)))
  (discreteFilling_lawful index (fun n => Fin (n+1))) finiteLast finiteLast

theorem selected_provider_lawful : provider.Lawful := normalizedIdentityFilling_lawful _ _ _ _

theorem two_substitutions : (provider.reindex (twice ≫ successor)).convert
    (normalizedIdentity_reindex fiber finiteLast finiteLast (twice ≫ successor)) =
    normalizedIdentityFilling ((discreteFilling index (fun n => Fin (n+1))).reindex (twice ≫ successor))
      ((discreteFilling_lawful index (fun n => Fin (n+1))).reindex (twice ≫ successor))
      (finiteLast.reindex (twice ≫ successor)) (finiteLast.reindex (twice ≫ successor)) :=
  normalizedIdentityFilling_reindex _ _ _ _ _

abbrev singleton := NormalizedIdentitySingleton.context fiber finiteLast
abbrev base : singleton ⟶ naturals :=
  projection (NormalizedIdentitySingleton.fiber fiber finiteLast) ≫ projection fiber
abbrev motive := reindex fiber base
abbrev motiveFilling := (discreteFilling index (fun n => Fin (n+1))).reindex base
noncomputable abbrev eliminated : Term motive :=
  NormalizedIdentityElimination.eliminate fiber finiteLast motive finiteLast motiveFilling.toComposition

theorem strict_branch : eliminated.reindex (NormalizedIdentitySingleton.reflexivity fiber finiteLast) = finiteLast :=
  NormalizedIdentityElimination.eliminate_beta fiber finiteLast motive finiteLast motiveFilling.toComposition
    (Filling.toComposition_lawful ((discreteFilling_lawful index (fun n => Fin (n+1))).reindex base))

end Examples.CubicalNormalizedIdentity
