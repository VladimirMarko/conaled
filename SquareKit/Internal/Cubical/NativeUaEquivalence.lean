import SquareKit.Internal.Cubical.NativeUnivalence

/-! The selected native ua map is itself a homotopy equivalence. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u

/-- The reverse map between based totals uses the same selected ua construction. -/
noncomputable def movingUaEquivalence {Γ : Context.{u+1}} (a : Γ ⟶ smallFamilyCodes.{u}) :
    HomotopyEquivalence (equivToPath (movingSource a) (movingTarget (Γ := Γ))) :=
  HomotopyEquivalence.ofContractibleTotals
    (equivToPath (movingSource a) (movingTarget (Γ := Γ)))
    (filling Γ) (filling_lawful Γ)
    (basedEquivalencesFilling a) (basedEquivalencesFilling_lawful a)
    (basedPathsFilling a) (basedPathsFilling_lawful a)
    (equivalenceTotal a) (basedPathTotalContractible a)

private def uaPathIso {Γ Δ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) :
    reindex (paths a b) σ ≅ paths (σ ≫ a) (σ ≫ b) :=
  pathReindexIso (reindex (family Γ) (projection (interval Γ))) (term a) (term b) σ


private theorem ua_conjugate_sections {Γ Δ Θ : Context.{u+1}}
    (a b : Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (s : Term (reindex (equivalences (σ ≫ a) (σ ≫ b)) τ)) :
    Term.map
      (Functor.whiskerLeft τ.mapElements
        (EquivalenceFamilies.equivReindexIso (liftedDecode a) (liftedDecode b) σ).inv ≫
        Functor.whiskerLeft (τ ≫ σ).mapElements (equivToPath a b) ≫
        Functor.whiskerLeft τ.mapElements (uaPathIso a b σ).hom) s =
      Term.map (Functor.whiskerLeft τ.mapElements (equivToPath (σ ≫ a) (σ ≫ b))) s := by
  let Je := EquivalenceFamilies.equivReindexIso (liftedDecode a) (liftedDecode b) σ
  let q := Term.map (Functor.whiskerLeft τ.mapElements Je.inv) s
  let S := EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) (τ ≫ σ)
  let T := EquivalenceFamilies.equivReindexSections (liftedDecode (σ ≫ a)) (liftedDecode (σ ≫ b)) τ
  have hJ := EquivalenceFamilies.equivReindexIso_hom_reindex_sections
    (liftedDecode a) (liftedDecode b) σ τ q
  have hround : Term.map (Functor.whiskerLeft τ.mapElements Je.hom) q = s :=
    Term.map_iso_roundtrip (Functor.isoWhiskerLeft τ.mapElements Je).symm s
  have hd : S.symm q = T.symm s := by
    have h : T (S.symm q) = s := hJ.symm.trans hround
    exact (T.symm_apply_apply _).symm.trans (congrArg T.symm h)
  have h₀ := equivToPath_reindex_beta (a := a) (b := b) (τ ≫ σ) q
  have h₁ := equivToPath_reindex_beta (a := σ ≫ a) (b := σ ≫ b) τ s
  apply (Term.map_injective_of_iso (uaPathIso (σ ≫ a) (σ ≫ b) τ))
  change Term.map (uaPathIso a b (τ ≫ σ)).hom
      (Term.map (Functor.whiskerLeft (τ ≫ σ).mapElements (equivToPath a b)) q) = _
  have hu := @congrArg
    (Σ f : liftedDecode (τ ≫ σ ≫ a) ⟶ liftedDecode (τ ≫ σ ≫ b), HomotopyEquivalence f)
    (Term (paths (τ ≫ σ ≫ a) (τ ≫ σ ≫ b)))
    (S.symm q) (T.symm s) (fun d => ua (τ ≫ σ ≫ a) (τ ≫ σ ≫ b) d.1 d.2) hd
  exact h₀.trans (hu.trans h₁.symm)

/-- Substitution preserves the complete selected ua map. -/
theorem equivToPath_conjugate_reindex {Γ Δ : Context.{u+1}}
    (a b : Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) :
    (EquivalenceFamilies.equivReindexIso (liftedDecode a) (liftedDecode b) σ).inv ≫
      Functor.whiskerLeft σ.mapElements (equivToPath a b) ≫
      (uaPathIso a b σ).hom = equivToPath (σ ≫ a) (σ ≫ b) := by
  let C := equivalences (σ ≫ a) (σ ≫ b)
  have h := ua_conjugate_sections a b σ (projection C) (generic C)
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro p
  exact congrArg (fun t => t.val (extendObj C x p)) h

/-- The chosen Glue ua map has native contractible homotopy fibers. -/
noncomputable def uaEquivalence {Γ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u}) :
    HomotopyEquivalence (equivToPath a b) := by
  let τ := pair (A := family Γ) (𝟙 Γ) (term b)
  let Jp := uaPathIso (movingSource a) (movingTarget (Γ := Γ)) τ
  let Je := EquivalenceFamilies.equivReindexIso
    (liftedDecode (movingSource a)) (liftedDecode (movingTarget (Γ := Γ))) τ
  have E := ((movingUaEquivalence a).reindex τ).conjugateIso Je.symm Jp
  exact (equivToPath_conjugate_reindex (movingSource a) (movingTarget (Γ := Γ)) τ) ▸ E

end SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
