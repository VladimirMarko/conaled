import SquareKit.Internal.Cubical.HomotopyEquivalenceSubstitution

/-! Substitution retains the selected native contractions supplied by an isomorphism. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem genericFiberPath_intro {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ total B) (a : Term (reindex A (σ ≫ projection B)))
    (p : Term (homogeneousPath (reindex B (σ ≫ projection B))
      (Term.map (Functor.whiskerLeft (σ ≫ projection B).mapElements f) a)
      ((generic B).reindex σ))) :
    genericFiberPath f σ (genericFiberIntro f σ a p) = p :=
  Term.map_iso_roundtrip (genericFiberPathIso f σ a).symm p

theorem genericFiberTerm_ext {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ total B)
    (z w : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f)
      (generic B)) σ))
    (ha : genericFiberFst f σ z = genericFiberFst f σ w)
    (hp : HEq (genericFiberPath f σ z) (genericFiberPath f σ w)) : z = w :=
  (genericFiberIntro_eta f σ z).symm.trans
    ((genericFiberIntro_congr f σ _ _ ha _ _ hp).trans (genericFiberIntro_eta f σ w))

theorem genericFiberIntro_input_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) (ρ : Θ ⟶ total (reindex B σ))
    (a : Term (reindex A (ρ ≫ liftSub B σ ≫ projection B)))
    (p : Term (homogeneousPath (reindex B (ρ ≫ liftSub B σ ≫ projection B))
      (Term.map (Functor.whiskerLeft (ρ ≫ liftSub B σ ≫ projection B).mapElements f) a)
      ((generic B).reindex (ρ ≫ liftSub B σ)))) :
    Term.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom)
      (genericFiberIntro f (ρ ≫ liftSub B σ) a p) =
    genericFiberIntro (A := reindex A σ) (B := reindex B σ)
      (Functor.whiskerLeft σ.mapElements f) ρ a p := by
  let z := genericFiberIntro f (ρ ≫ liftSub B σ) a p
  let w := Term.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso f σ).hom) z
  have hp : genericFiberPath (A := reindex A σ) (B := reindex B σ)
      (Functor.whiskerLeft σ.mapElements f) ρ w = p :=
    (genericFiberPath_input_reindex f σ ρ z).trans (genericFiberPath_intro (A := A) (B := B) f (ρ ≫ liftSub B σ) a p)
  let g := Functor.whiskerLeft σ.mapElements f
  have hq := genericFiberPath_intro (A := reindex A σ) (B := reindex B σ) g ρ a p
  exact genericFiberTerm_ext (A := reindex A σ) (B := reindex B σ) g ρ w
    (genericFiberIntro g ρ a p) rfl (heq_of_eq (hp.trans hq.symm))

theorem isoFiberCenter_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (e : A ≅ B) (σ : Δ ⟶ Γ) :
    Term.map (genericFiberReindexIso e.hom σ).hom ((isoFiberCenter e).reindex (liftSub B σ)) =
      isoFiberCenter (Functor.isoWhiskerLeft σ.mapElements e) := by
  let i := Functor.isoWhiskerLeft (projection B).mapElements e
  let a := Term.map i.inv (generic B)
  let p := pathLam ((generic B).reindex (projection (interval (total B))))
    (Term.map_iso_roundtrip i.symm (generic B)).symm rfl
  let τ := liftSub B σ
  have h := genericFiberIntro_reindex e.hom (𝟙 (total B)) a p τ
  have k := genericFiberIntro_input_reindex e.hom σ (𝟙 (total (reindex B σ)))
    (a.reindex τ) (homogeneousReindex p τ)
  exact (congrArg (Term.map (genericFiberReindexIso e.hom σ).hom) h.symm).trans k

def isoFiberContractionAlong {Γ Δ : Context.{u}} {A B : Family Γ}
    (e : A ≅ B) (σ : Δ ⟶ total B)
    (z : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B)) σ)) :
    Term (reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B)) (projection (interval Δ) ≫ σ)) := by
  let p := genericFiberPath e.hom σ z
  let q := (pathApp p).reindex (reverseInterval Δ)
  let i := Functor.isoWhiskerLeft (projection (interval Δ) ≫ σ ≫ projection B).mapElements e
  let a := Term.map i.inv q
  let t := homogeneousTail p
  exact genericFiberIntro e.hom (projection (interval Δ) ≫ σ) a
    (pathLam (pathApp t)
      ((pathApp_zero t).trans (Term.map_iso_roundtrip i.symm q).symm)
      (pathApp_one t))

theorem isoFiberContractionSection_eq {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) :
    isoFiberContractionSection e =
      isoFiberContractionAlong e (projection (homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B))) (generic (homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B))) := rfl

theorem isoFiberContractionAlong_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (e : A ≅ B) (σ : Δ ⟶ total B)
    (z : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom)
      (generic B)) σ)) (τ : Θ ⟶ Δ) :
    (isoFiberContractionAlong e σ z).reindex (liftSub (interval Δ) τ) =
      isoFiberContractionAlong e (τ ≫ σ) (z.reindex τ) := by
  let p := genericFiberPath e.hom σ z
  let q := (pathApp p).reindex (reverseInterval Δ)
  let i := Functor.isoWhiskerLeft (projection (interval Δ) ≫ σ ≫ projection B).mapElements e
  let a := Term.map i.inv q
  let t := homogeneousTail p
  let r := pathLam (pathApp t)
    ((pathApp_zero t).trans (Term.map_iso_roundtrip i.symm q).symm) (pathApp_one t)
  exact (genericFiberIntro_reindex e.hom (projection (interval Δ) ≫ σ) a r
    (liftSub (interval Δ) τ)).symm

theorem isoFiberContractionAlong_input_reindex {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (e : A ≅ B) (σ : Δ ⟶ Γ) (ρ : Θ ⟶ total (reindex B σ))
    (z : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom)
      (generic B)) (ρ ≫ liftSub B σ))) :
    Term.map (Functor.whiskerLeft (projection (interval Θ) ≫ ρ).mapElements
      (genericFiberReindexIso e.hom σ).hom)
      (isoFiberContractionAlong e (ρ ≫ liftSub B σ) z) =
    isoFiberContractionAlong (Functor.isoWhiskerLeft σ.mapElements e) ρ
      (Term.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso e.hom σ).hom) z) := by
  let p := genericFiberPath e.hom (ρ ≫ liftSub B σ) z
  let q := (pathApp p).reindex (reverseInterval Θ)
  let i := Functor.isoWhiskerLeft
    (projection (interval Θ) ≫ ρ ≫ liftSub B σ ≫ projection B).mapElements e
  let a := Term.map i.inv q
  let t := homogeneousTail p
  let r := pathLam (pathApp t)
    ((pathApp_zero t).trans (Term.map_iso_roundtrip i.symm q).symm) (pathApp_one t)
  exact genericFiberIntro_input_reindex e.hom σ (projection (interval Θ) ≫ ρ) a r

theorem HomotopyEquivalence.ofIso_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (e : A ≅ B) (σ : Δ ⟶ Γ) :
    (HomotopyEquivalence.ofIso e).reindex σ =
      HomotopyEquivalence.ofIso (Functor.isoWhiskerLeft σ.mapElements e) := by
  apply HomotopyEquivalence.ext
  apply HomotopyContractible.ext_pathApp
  · exact isoFiberCenter_reindex e σ
  · let H := homotopyFiber (Functor.whiskerLeft (projection B).mapElements e.hom) (generic B)
    let e' := Functor.isoWhiskerLeft σ.mapElements e
    let H' := homotopyFiber (Functor.whiskerLeft (projection (Presheaf.reindex B σ)).mapElements e'.hom)
      (generic (Presheaf.reindex B σ))
    let τ := liftSub B σ
    let i := genericFiberReindexIso e.hom σ
    let ρ := projection H'
    let j := Functor.isoWhiskerLeft ρ.mapElements i
    let z := Term.map j.inv (generic H')
    let ν := pair (A := H) (ρ ≫ τ) z
    let m := Functor.whiskerLeft (projection (interval (total H')) ≫ ρ).mapElements i.hom
    have h₁ := isoFiberContractionAlong_reindex e (projection H) (generic H) ν
    have h₂ := isoFiberContractionAlong_input_reindex e σ ρ z
    have h₃ := congrArg (isoFiberContractionAlong e' ρ)
      (Term.map_iso_roundtrip j.symm (generic H'))
    exact (congrArg (Term.map m) h₁).trans (h₂.trans h₃)

end SquareKit.Cubical.Presheaf
