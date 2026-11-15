import SquareKit.Internal.Cubical.NativeUnivalenceMapLaws
import SquareKit.Internal.Cubical.EquivalenceFamilySubstitution

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace EquivalenceFamilies

theorem decodeMap_lam_reindex_apply {Γ Δ : Context.{u}} {A B : Family Γ}
    (s : Term (reindex B (projection A))) (σ : Δ ⟶ Γ)
    (a : Term (reindex A σ)) :
    Term.map (Functor.whiskerLeft σ.mapElements (decodeMap (lam s))) a =
      s.reindex (pair σ a) := by
  apply Term.ext
  intro x
  rfl

end EquivalenceFamilies
namespace SmallUniverse.NativeUnivalence
variable {Γ Δ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}

theorem genericPath_pair (σ : Δ ⟶ Γ) (p : Term (reindex (paths a b) σ)) :
    reindexPath (genericPath a b) (pair (A := paths a b) σ p) =
      Term.map (pathReindex (reindex (family Γ) (projection (interval Γ)))
        (term a) (term b) σ) p := by
  apply eq_of_heq
  apply pathTerm_hext
  rfl

private theorem pathToEquivalence_congr {p q : Term (paths a b)} (h : p = q) :
    HEq (pathToEquivalence p) (pathToEquivalence q) := by
  cases h
  rfl

/-- Evaluation after any substitution recovers all selected equivalence data. -/
theorem pathEquivalence_pair (σ : Δ ⟶ Γ) (p : Term (reindex (paths a b) σ)) :
    let q : Term (paths (σ ≫ a) (σ ≫ b)) := Term.map (pathReindex (reindex (family Γ) (projection (interval Γ)))
      (term a) (term b) σ) p
    (⟨Functor.whiskerLeft (pair (A := paths a b) σ p).mapElements
        (pathToMap (genericPath a b)),
      (pathToEquivalence (genericPath a b)).reindex (pair (A := paths a b) σ p)⟩ :
      Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ b), HomotopyEquivalence f) =
      ⟨pathToMap q, pathToEquivalence q⟩ := by
  dsimp only
  have hm := (pathToMap_reindex (genericPath a b) (pair (A := paths a b) σ p)).trans
    (congrArg (@pathToMap Δ (σ ≫ a) (σ ≫ b)) (genericPath_pair σ p))
  have hE := (pathToEquivalence_reindex (genericPath a b) (pair (A := paths a b) σ p)).trans
    (pathToEquivalence_congr (genericPath_pair σ p))
  exact Sigma.ext hm hE

theorem pathSection_reindex_pair {C : Family Γ}
    (s : Term (reindex (paths a b) (projection C))) (σ : Δ ⟶ Γ)
    (c : Term (reindex C σ)) :
    reindexPath (a := projection C ≫ a) (b := projection C ≫ b)
      (Term.map (pathReindex (reindex (family Γ) (projection (interval Γ)))
        (term a) (term b) (projection C)) s) (pair (A := C) σ c) =
      Term.map (pathReindex (reindex (family Γ) (projection (interval Γ)))
        (term a) (term b) σ) (s.reindex (pair (A := C) σ c)) := by
  apply eq_of_heq
  apply pathTerm_hext
  rfl

theorem equivalencePathSection_reindex_pair (σ : Δ ⟶ Γ)
    (c : Term (reindex (equivalences a b) σ)) :
    Term.map (pathReindex (reindex (family Γ) (projection (interval Γ)))
      (term a) (term b) σ)
      ((equivalencePathSection a b).reindex (pair (A := equivalences a b) σ c)) =
      ua (σ ≫ a) (σ ≫ b)
        (Functor.whiskerLeft (pair (A := equivalences a b) σ c).mapElements (genericEquivalence a b).1)
        ((genericEquivalence a b).2.reindex (pair (A := equivalences a b) σ c)) := by
  have h := Term.map_iso_roundtrip
    (pathReindexIso (reindex (family Γ) (projection (interval Γ)))
      (term a) (term b) (projection (equivalences a b))).symm
    (ua (projection (equivalences a b) ≫ a) (projection (equivalences a b) ≫ b)
      (genericEquivalence a b).1 (genericEquivalence a b).2)
  exact (pathSection_reindex_pair (equivalencePathSection a b) σ c).symm.trans
    ((congrArg (fun p => reindexPath p (pair (A := equivalences a b) σ c)) h).trans
      (ua_reindex _ _ _ _ (pair (A := equivalences a b) σ c)))

/-- The native forward map evaluates to the full selected transport equivalence
in every substituted context. -/
theorem pathToEquiv_reindex_beta (σ : Δ ⟶ Γ) (p : Term (reindex (paths a b) σ)) :
    Term.map (Functor.whiskerLeft σ.mapElements (pathToEquiv a b)) p =
      EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ
        ⟨pathToMap (a := σ ≫ a) (b := σ ≫ b) (Term.map (pathReindex (reindex (family Γ) (projection (interval Γ)))
          (term a) (term b) σ) p),
         pathToEquivalence (a := σ ≫ a) (b := σ ≫ b) (Term.map (pathReindex (reindex (family Γ) (projection (interval Γ)))
          (term a) (term b) σ) p)⟩ := by
  let q := pair (A := paths a b) σ p
  have h := EquivalenceFamilies.equivReindexSections_comp (liftedDecode a) (liftedDecode b)
    (projection (paths a b)) q (pathToMap (genericPath a b)) (pathToEquivalence (genericPath a b))
  exact (EquivalenceFamilies.decodeMap_lam_reindex_apply (pathEquivalenceSection a b) σ p).trans
    (h.symm.trans (congrArg
      (EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ)
      (pathEquivalence_pair σ p)))

/-- Generic evaluation recovers the supplied internal section's full decoded data. -/
theorem genericEquivalence_reindex_pair (σ : Δ ⟶ Γ)
    (s : Term (reindex (equivalences a b) σ)) :
    (⟨Functor.whiskerLeft (pair (A := equivalences a b) σ s).mapElements
        (genericEquivalence a b).1,
      (genericEquivalence a b).2.reindex (pair (A := equivalences a b) σ s)⟩ :
      Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ b), HomotopyEquivalence f) =
      (EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ).symm s := by
  let q := pair (A := equivalences a b) σ s
  let S := EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ
  apply S.injective
  have h := EquivalenceFamilies.equivReindexSections_comp (liftedDecode a) (liftedDecode b)
    (projection (equivalences a b)) q (genericEquivalence a b).1 (genericEquivalence a b).2
  have hr := (EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b)
    (projection (equivalences a b))).apply_symm_apply (generic (equivalences a b))
  exact (h.trans (congrArg (fun t => t.reindex q) hr)).trans (S.apply_symm_apply s).symm

private theorem ua_congr_data (a b : Γ ⟶ smallFamilyCodes.{u})
    (f g : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (F : HomotopyEquivalence g)
    (h : (⟨f,E⟩ : Σ k : liftedDecode a ⟶ liftedDecode b, HomotopyEquivalence k) = ⟨g,F⟩) :
    ua a b f E = ua a b g F :=
  @congrArg (Σ k : liftedDecode a ⟶ liftedDecode b, HomotopyEquivalence k)
    (Term (paths a b)) ⟨f,E⟩ ⟨g,F⟩ (fun z => ua a b z.1 z.2) h

/-- The native reverse map evaluates to the actual chosen Glue path in every
substituted context, retaining the section's selected equivalence witness. -/
theorem equivToPath_reindex_beta (σ : Δ ⟶ Γ)
    (s : Term (reindex (equivalences a b) σ)) :
    Term.map (pathReindex (reindex (family Γ) (projection (interval Γ)))
      (term a) (term b) σ)
      (Term.map (Functor.whiskerLeft σ.mapElements (equivToPath a b)) s) =
      ua (σ ≫ a) (σ ≫ b)
        ((EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ).symm s).1
        ((EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ).symm s).2 := by
  have h := EquivalenceFamilies.decodeMap_lam_reindex_apply (equivalencePathSection a b) σ s
  let q := pair (A := equivalences a b) σ s
  let d := (EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ).symm s
  have hu : ua (σ ≫ a) (σ ≫ b)
      (Functor.whiskerLeft q.mapElements (genericEquivalence a b).1)
      ((genericEquivalence a b).2.reindex q) = ua (σ ≫ a) (σ ≫ b) d.1 d.2 :=
    ua_congr_data (σ ≫ a) (σ ≫ b)
      (Functor.whiskerLeft q.mapElements (genericEquivalence a b).1) d.1
      ((genericEquivalence a b).2.reindex q) d.2 (genericEquivalence_reindex_pair σ s)
  exact (congrArg (Term.map (pathReindex (reindex (family Γ) (projection (interval Γ)))
    (term a) (term b) σ)) h).trans
    ((equivalencePathSection_reindex_pair σ s).trans hu)

/-- Global sections of the forward native map retain the chosen contractions. -/
theorem pathToEquiv_beta (p : Term (paths a b)) :
    EquivalenceFamilies.equivSections (liftedDecode a) (liftedDecode b)
      ⟨pathToMap p, pathToEquivalence p⟩ = Term.map (pathToEquiv a b) p := by
  exact (EquivalenceFamilies.equivReindexSections_id (liftedDecode a) (liftedDecode b)
    (pathToMap p) (pathToEquivalence p)).symm.trans
    (pathToEquiv_reindex_beta (𝟙 Γ) p).symm

/-- Global sections of the reverse native map recover the actual chosen Glue path. -/
theorem equivToPath_beta (f : liftedDecode a ⟶ liftedDecode b)
    (E : HomotopyEquivalence f) :
    Term.map (equivToPath a b)
      (EquivalenceFamilies.equivSections (liftedDecode a) (liftedDecode b) ⟨f,E⟩) =
      ua a b f E := by
  let S := EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) (𝟙 Γ)
  have hd : S.symm (EquivalenceFamilies.equivSections (liftedDecode a) (liftedDecode b) ⟨f,E⟩) =
      ⟨f,E⟩ :=
    (congrArg S.symm (EquivalenceFamilies.equivReindexSections_id
      (liftedDecode a) (liftedDecode b) f E).symm).trans (S.symm_apply_apply ⟨f,E⟩)
  exact (equivToPath_reindex_beta (𝟙 Γ)
    (EquivalenceFamilies.equivSections (liftedDecode a) (liftedDecode b) ⟨f,E⟩)).trans
    (ua_congr_data a b _ f _ E hd)

end SmallUniverse.NativeUnivalence
end SquareKit.Cubical.Presheaf
