import SquareKit.Internal.Cubical.CocycleSecondIdentity
import SquareKit.Internal.Cubical.NormalizedIdentitySubstitution

/-! Evaluation of the constructed second identity retains the chosen square. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

theorem secondIdentityBody_eval (Γ : Context.{0}) (x : Γ.Elements)
    (r s : (interval Γ).obj x) :
    (((secondIdentityBody Γ).val (extendObj (interval Γ) x r)).fromLocal).path.val.val (𝟙 x) s =
      squareValue r.down s.down := by
  have e := normalizedIdentity_fromReindexed (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ)
    (projection (interval Γ)) (normalizedSquareIdentity (generic (interval Γ)))
  have en : Term.map (normalizedIdentityIso (cocycleFamily (total (interval Γ)))
      (zeroTerm (total (interval Γ))) (zeroTerm (total (interval Γ)))).inv
      (normalizedSquareIdentity (generic (interval Γ))) = squareIdentity (generic (interval Γ)) :=
    Term.map_iso_roundtrip (normalizedIdentityIso _ _ _) (squareIdentity (generic (interval Γ)))
  have e := (congrArg
    (fun q => Term.map (Functor.whiskerLeft (projection (interval Γ)).mapElements
        (normalizedIdentityIso (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ)).hom)
      (Term.map (identityReindexIso (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ)
        (projection (interval Γ))).inv q)) en).symm.trans e
  have h := congrArg (fun t => ((t.val (extendObj (interval Γ) x r)).fromLocal).path.val.val (𝟙 x) s) e
  change _ = _ at h
  refine h.symm.trans ?_
  change ((identityReindexIso (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ)
    (projection (interval Γ))).inv.app (extendObj (interval Γ) x r)
      ((squareIdentity (generic (interval Γ))).val (extendObj (interval Γ) x r))).toLocal.fromLocal.path.val.val (𝟙 x) s = _
  refine (congrArg (fun p : IdentityElement (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ) x =>
    p.path.val.val (𝟙 x) s) (LocalIdentity.fromLocal_toLocal
      ((identityReindexIso (cocycleFamily Γ) (zeroTerm Γ) (zeroTerm Γ)
        (projection (interval Γ))).inv.app (extendObj (interval Γ) x r)
          ((squareIdentity (generic (interval Γ))).val (extendObj (interval Γ) x r))))).trans ?_
  exact piInverseValue_map (A := interval Γ)
    (B := reindex (cocycleFamily Γ) (projection (interval Γ)))
    (projection (interval Γ))
    ((squareIdentity (generic (interval Γ))).val (extendObj (interval Γ) x r)).path.val
    (𝟙 (extendObj (interval Γ) x r)) s

end SquareKit.Cubical.CategoryCocycles
