import SquareKit.Internal.Cubical.HomotopyIsoSubstitution
import SquareKit.Internal.Cubical.EquivalenceFamilies

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace EquivalenceIsoTransport
variable {Γ : Context.{u}} {A A' B B' : Family Γ}
  (i : A' ≅ A) (j : B ≅ B') (f : A ⟶ B)

abbrev conjugate := i.hom ≫ f ≫ j.hom
abbrev fiber (f : A ⟶ B) := homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)

def targetSub : total B' ⟶ total B where
  app _ := TypeCat.ofHom (fun z => ⟨z.1,j.inv.app (Γ.elementsMk _ z.1) z.2⟩)
  naturality x y g := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Sigma.ext
    · rfl
    · let k : Γ.elementsMk x z.1 ⟶ Γ.elementsMk y (Γ.map g z.1) :=
        Functor.Elements.homMk g rfl
      change HEq (j.inv.app _ (B'.map k z.2)) (B.map k (j.inv.app _ z.2))
      exact heq_of_eq (j.inv.naturality_apply k z.2)

variable {Δ : Context.{u}} (σ : Δ ⟶ total B')

abbrev oldFiber := reindex (fiber f) (targetSub j)

noncomputable def forwardPath (z : Term (reindex (oldFiber j f) σ)) :
    Term (homogeneousPath (reindex B' (σ ≫ projection B'))
      (Term.map (Functor.whiskerLeft (σ ≫ projection B').mapElements (conjugate i j f))
        (Term.map (Functor.whiskerLeft (σ ≫ projection B').mapElements i.inv)
          (genericFiberFst f (σ ≫ targetSub j) z)))
      ((generic B').reindex σ)) := by
  let p := genericFiberPath f (σ ≫ targetSub j) z
  let q := homogeneousPathMap (Functor.whiskerLeft (σ ≫ projection B').mapElements j.hom) p
  refine pathLam (pathApp q) ((pathApp_zero q).trans ?_) ((pathApp_one q).trans ?_)
  · apply Term.ext
    intro x
    exact congrArg (fun t => j.hom.app ((σ ≫ projection B').mapElements.obj x)
      (f.app ((σ ≫ projection B').mapElements.obj x) t))
      (congrArg (fun m => m.app ((σ ≫ projection B').mapElements.obj x)
        ((genericFiberFst f (σ ≫ targetSub j) z).val x)) i.inv_hom_id).symm
  · apply Term.ext
    intro x
    exact congrArg (fun m => m.app ((σ ≫ projection B').mapElements.obj x)
      (((generic B').reindex σ).val x)) j.inv_hom_id

noncomputable def forward (z : Term (reindex (oldFiber j f) σ)) :
    Term (reindex (fiber (conjugate i j f)) σ) :=
  genericFiberIntro (conjugate i j f) σ
    (Term.map (Functor.whiskerLeft (σ ≫ projection B').mapElements i.inv)
      (genericFiberFst f (σ ≫ targetSub j) z)) (forwardPath i j f σ z)

noncomputable def backwardPath (z : Term (reindex (fiber (conjugate i j f)) σ)) :
    Term (homogeneousPath (reindex B (σ ≫ projection B'))
      (Term.map (Functor.whiskerLeft (σ ≫ projection B').mapElements f)
        (Term.map (Functor.whiskerLeft (σ ≫ projection B').mapElements i.hom)
          (genericFiberFst (conjugate i j f) σ z)))
      ((generic B).reindex (σ ≫ targetSub j))) := by
  let p := genericFiberPath (conjugate i j f) σ z
  let q := homogeneousPathMap (Functor.whiskerLeft (σ ≫ projection B').mapElements j.inv) p
  refine pathLam (pathApp q) ((pathApp_zero q).trans ?_) (pathApp_one q)
  apply Term.ext
  intro x
  exact congrArg (fun m => m.app ((σ ≫ projection B').mapElements.obj x)
    (f.app ((σ ≫ projection B').mapElements.obj x)
      (i.hom.app ((σ ≫ projection B').mapElements.obj x)
        ((genericFiberFst (conjugate i j f) σ z).val x)))) j.hom_inv_id

noncomputable def backward (z : Term (reindex (fiber (conjugate i j f)) σ)) :
    Term (reindex (oldFiber j f) σ) :=
  genericFiberIntro f (σ ≫ targetSub j)
    (Term.map (Functor.whiskerLeft (σ ≫ projection B').mapElements i.hom)
      (genericFiberFst (conjugate i j f) σ z)) (backwardPath i j f σ z)

private theorem fiberPath_reindex {Θ : Context.{u}} (f : A ⟶ B)
    (ρ : Δ ⟶ total B) (z : Term (reindex (fiber f) ρ)) (τ : Θ ⟶ Δ) :
    pathApp (genericFiberPath f (τ ≫ ρ) (z.reindex τ)) =
      (pathApp (genericFiberPath f ρ z)).reindex (liftSub (interval Δ) τ) := by
  apply Term.ext
  intro x
  rfl

theorem forward_natural {Θ : Context.{u}} (τ : Θ ⟶ Δ)
    (z : Term (reindex (oldFiber j f) σ)) :
    forward i j f (τ ≫ σ) (z.reindex τ) = (forward i j f σ z).reindex τ := by
  let p := forwardPath i j f σ z
  have hp : HEq (homogeneousReindex p τ) (forwardPath i j f (τ ≫ σ) (z.reindex τ)) := by
    apply pathTerm_hext
    exact (congrArg (Term.map (Functor.whiskerLeft
      (projection (interval Θ) ≫ τ ≫ σ ≫ projection B').mapElements j.hom))
      (fiberPath_reindex f (σ ≫ targetSub j) z τ)).symm
  exact ((genericFiberIntro_reindex (conjugate i j f) σ _ p τ).symm.trans
    (genericFiberIntro_congr (conjugate i j f) (τ ≫ σ) _ _ rfl _ _ hp)).symm

theorem backward_natural {Θ : Context.{u}} (τ : Θ ⟶ Δ)
    (z : Term (reindex (fiber (conjugate i j f)) σ)) :
    backward i j f (τ ≫ σ) (z.reindex τ) = (backward i j f σ z).reindex τ := by
  let p := backwardPath i j f σ z
  have hp : HEq (homogeneousReindex p τ) (backwardPath i j f (τ ≫ σ) (z.reindex τ)) := by
    apply pathTerm_hext
    exact (congrArg (Term.map (Functor.whiskerLeft
      (projection (interval Θ) ≫ τ ≫ σ ≫ projection B').mapElements j.inv))
      (fiberPath_reindex (conjugate i j f) σ z τ)).symm
  exact ((genericFiberIntro_reindex f (σ ≫ targetSub j) _ p τ).symm.trans
    (genericFiberIntro_congr f (τ ≫ σ ≫ targetSub j) _ _ rfl _ _ hp)).symm


theorem backward_forward (z : Term (reindex (oldFiber j f) σ)) :
    backward i j f σ (forward i j f σ z) = z := by
  apply genericFiberTerm_ext f (σ ≫ targetSub j)
  · exact Term.map_iso_roundtrip (Functor.isoWhiskerLeft (σ ≫ projection B').mapElements i).symm
      (genericFiberFst f (σ ≫ targetSub j) z)
  · apply pathTerm_hext
    have h := genericFiberPath_intro (conjugate i j f) σ
      (Term.map (Functor.whiskerLeft (σ ≫ projection B').mapElements i.inv)
        (genericFiberFst f (σ ≫ targetSub j) z)) (forwardPath i j f σ z)
    have hh := congrArg (fun p => Term.map
      (Functor.whiskerLeft (projection (interval Δ) ≫ σ ≫ projection B').mapElements j.inv)
      (pathApp p)) h
    have hb := genericFiberPath_intro f (σ ≫ targetSub j)
      (Term.map (Functor.whiskerLeft (σ ≫ projection B').mapElements i.hom)
        (genericFiberFst (conjugate i j f) σ (forward i j f σ z)))
      (backwardPath i j f σ (forward i j f σ z))
    exact (congrArg pathApp hb).trans (hh.trans
      (Term.map_iso_roundtrip
        (Functor.isoWhiskerLeft (projection (interval Δ) ≫ σ ≫ projection B').mapElements j)
        (pathApp (genericFiberPath f (σ ≫ targetSub j) z))))

theorem forward_backward (z : Term (reindex (fiber (conjugate i j f)) σ)) :
    forward i j f σ (backward i j f σ z) = z := by
  apply genericFiberTerm_ext (conjugate i j f) σ
  · exact Term.map_iso_roundtrip (Functor.isoWhiskerLeft (σ ≫ projection B').mapElements i)
      (genericFiberFst (conjugate i j f) σ z)
  · apply pathTerm_hext
    have h := genericFiberPath_intro f (σ ≫ targetSub j)
      (Term.map (Functor.whiskerLeft (σ ≫ projection B').mapElements i.hom)
        (genericFiberFst (conjugate i j f) σ z)) (backwardPath i j f σ z)
    have hh := congrArg (fun p => Term.map
      (Functor.whiskerLeft (projection (interval Δ) ≫ σ ≫ projection B').mapElements j.hom)
      (pathApp p)) h
    have hb := genericFiberPath_intro (conjugate i j f) σ
      (Term.map (Functor.whiskerLeft (σ ≫ projection B').mapElements i.inv)
        (genericFiberFst f (σ ≫ targetSub j) (backward i j f σ z)))
      (forwardPath i j f σ (backward i j f σ z))
    exact (congrArg pathApp hb).trans (hh.trans
      (Term.map_iso_roundtrip
        (Functor.isoWhiskerLeft (projection (interval Δ) ≫ σ ≫ projection B').mapElements j).symm
        (pathApp (genericFiberPath (conjugate i j f) σ z))))

private def mapOfSections {Ω : Context.{u}} {C D : Family Ω}
    (Φ : ∀ {Λ : Context.{u}} (ρ : Λ ⟶ Ω), Term (reindex C ρ) → Term (reindex D ρ)) : C ⟶ D where
  app x := TypeCat.ofHom (fun c => (Φ (projection C) (generic C)).val (extendObj C x c))
  naturality x y k := by
    apply ConcreteCategory.hom_ext
    intro c
    exact (Φ (projection C) (generic C)).property (extendHom C k c) |>.symm

private theorem mapOfSections_apply {Ω : Context.{u}} {C D : Family Ω}
    (Φ : ∀ {Λ : Context.{u}} (ρ : Λ ⟶ Ω), Term (reindex C ρ) → Term (reindex D ρ))
    (hn : ∀ {Λ Ψ : Context.{u}} (ρ : Λ ⟶ Ω) (τ : Ψ ⟶ Λ) (z : Term (reindex C ρ)),
      Φ (τ ≫ ρ) (z.reindex τ) = (Φ ρ z).reindex τ)
    {Λ : Context.{u}} (ρ : Λ ⟶ Ω) (z : Term (reindex C ρ)) :
    Term.map (Functor.whiskerLeft ρ.mapElements (mapOfSections Φ)) z = Φ ρ z :=
  (hn (projection C) (pair ρ z) (generic C)).symm

noncomputable def fiberIso : oldFiber j f ≅ fiber (conjugate i j f) where
  hom := mapOfSections (forward i j f)
  inv := mapOfSections (backward i j f)
  hom_inv_id := by
    apply NatTrans.ext
    funext x
    apply ConcreteCategory.hom_ext
    intro z
    let ρ := projection (oldFiber j f)
    let s := generic (oldFiber j f)
    have hf := mapOfSections_apply (forward i j f) (fun ρ τ z => forward_natural i j f ρ τ z) ρ s
    have hb := mapOfSections_apply (backward i j f) (fun ρ τ z => backward_natural i j f ρ τ z) ρ
      (forward i j f ρ s)
    have he := (congrArg (Term.map (Functor.whiskerLeft ρ.mapElements (mapOfSections (backward i j f)))) hf).trans
      (hb.trans (backward_forward i j f ρ s))
    exact congrArg (fun t => t.val (extendObj (oldFiber j f) x z)) he
  inv_hom_id := by
    apply NatTrans.ext
    funext x
    apply ConcreteCategory.hom_ext
    intro z
    let ρ := projection (fiber (conjugate i j f))
    let s := generic (fiber (conjugate i j f))
    have hb := mapOfSections_apply (backward i j f) (fun ρ τ z => backward_natural i j f ρ τ z) ρ s
    have hf := mapOfSections_apply (forward i j f) (fun ρ τ z => forward_natural i j f ρ τ z) ρ
      (backward i j f ρ s)
    have he := (congrArg (Term.map (Functor.whiskerLeft ρ.mapElements (mapOfSections (forward i j f)))) hb).trans
      (hf.trans (forward_backward i j f ρ s))
    exact congrArg (fun t => t.val (extendObj (fiber (conjugate i j f)) x z)) he

end EquivalenceIsoTransport

/-- Transport a genuine equivalence across explicit source and target isomorphisms,
retaining its selected generic-fiber contraction through the constructed fiber iso. -/
noncomputable def HomotopyEquivalence.conjugateIso {Γ : Context.{u}} {A A' B B' : Family Γ}
    {f : A ⟶ B} (E : HomotopyEquivalence f) (i : A' ≅ A) (j : B ≅ B') :
    HomotopyEquivalence (i.hom ≫ f ≫ j.hom) where
  fibers := (E.fibers.reindex (EquivalenceIsoTransport.targetSub j)).transport
    (EquivalenceIsoTransport.fiberIso i j f)

end SquareKit.Cubical.Presheaf
