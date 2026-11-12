import SquareKit.Internal.Cubical.GlueFillingSubstitution

/-! Fiber extensions for the elimination map of Glue. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.Glue
open CategoryTheory
universe u

private theorem fiberIntro_path {Γ Δ : Context.{u}} {B D : Family Γ} (f : B ⟶ D)
    (σ : Δ ⟶ total D) (b : Term (reindex B (σ ≫ projection D)))
    (q : Term (homogeneousPath (reindex D (σ ≫ projection D))
      (Term.map (Functor.whiskerLeft (σ ≫ projection D).mapElements f) b)
      ((generic D).reindex σ))) :
    genericFiberPath f σ (genericFiberIntro f σ b q) = q :=
  Term.map_iso_roundtrip (genericFiberPathIso f σ b).symm q

private theorem reverse_pathApp_twice {Ω : Context.{u}} {B : Family Ω} {a b : Term B}
    (q : Term (homogeneousPath B a b)) :
    (pathApp (homogeneousReverse q)).reindex (reverseInterval Ω) = pathApp q := by
  apply Term.ext
  intro x
  let y := (projection (interval Ω)).mapElements.obj x
  have hr : Cube.comp (Cube.comp x.val.2.down Cube.reversal) Cube.reversal = x.val.2.down :=
    (@Category.assoc Cube _ x.obj.unop ⟨1⟩ ⟨1⟩ ⟨1⟩ x.val.2.down Cube.reversal Cube.reversal).trans
      ((congrArg (Cube.comp x.val.2.down) Cube.reversal_twice).trans
        (@Category.comp_id Cube _ x.obj.unop ⟨1⟩ x.val.2.down))
  exact congrArg (fun r => (show B.obj y from (q.val y).val.val (𝟙 y) (ULift.up r))) hr

private theorem fiberIntro_reindex_eq {Γ Δ Ξ : Context.{u}} {B D : Family Γ}
    (f : B ⟶ D) (σ : Δ ⟶ total D) (a : Term (reindex B (σ ≫ projection D)))
    (p : Term (homogeneousPath (reindex D (σ ≫ projection D))
      (Term.map (Functor.whiskerLeft (σ ≫ projection D).mapElements f) a)
      ((generic D).reindex σ))) (τ : Ξ ⟶ Δ)
    (z : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection D).mapElements f)
      (generic D)) (τ ≫ σ)))
    (ha : a.reindex τ = genericFiberFst f (τ ≫ σ) z)
    (hp : (pathApp p).reindex (liftSub (interval Δ) τ) = pathApp (genericFiberPath f (τ ≫ σ) z)) :
    (genericFiberIntro f σ a p).reindex τ = z := by
  let q := homogeneousReindex p τ
  have hq : HEq q (genericFiberPath f (τ ≫ σ) z) :=
    pathTerm_hext q (genericFiberPath f (τ ≫ σ) z) hp
  have hc := genericFiberIntro_congr f (τ ≫ σ) (a.reindex τ) (genericFiberFst f (τ ≫ σ) z)
    ha q (genericFiberPath f (τ ≫ σ) z) hq
  exact (genericFiberIntro_reindex f σ a p τ).symm.trans
    (hc.trans (genericFiberIntro_eta f (τ ≫ σ) z))

namespace UnglueFiber
variable {Γ Δ : Context.{u}} (φ : Cofibration Γ) (A : Family Γ)
  (T : Family (restrictContext φ)) (e : T ⟶ reindex A (restrictInclusion φ))
  (σ : Δ ⟶ total A)

abbrev C := family φ A T e
abbrev f := unglue φ A T e
abbrev Fiber := homotopyFiber (Functor.whiskerLeft (projection A).mapElements (f φ A T e))
  (generic A)
abbrev face := φ.reindex (σ ≫ projection A)
abbrev target := (generic A).reindex σ

variable {ψ : Cofibration Δ} (s : PartialSection (reindex (Fiber φ A T e) σ) ψ)

def partialDomain := genericFiberFst (f φ A T e) (restrictInclusion ψ ≫ σ) s.toRestricted

def partialPath := genericFiberPath (f φ A T e) (restrictInclusion ψ ≫ σ) s.toRestricted

def partialTube : PartialSection (reindex A (projection (interval Δ) ≫ σ ≫ projection A))
    (ψ.reindex (projection (interval Δ))) :=
  restrictedPathTube ψ (target A σ)
    (Term.map (Functor.whiskerLeft (restrictInclusion ψ ≫ σ ≫ projection A).mapElements
      (f φ A T e)) (partialDomain φ A T e σ s))
    (homogeneousReverse (partialPath φ A T e σ s))

def intersectionToPartial : restrictContext (ψ.reindex (restrictInclusion (face φ A σ))) ⟶
    restrictContext ψ where
  app _ := TypeCat.ofHom (fun z => ⟨z.val.val,z.property⟩)
  naturality _ _ _ := rfl

/-- Restrict a partial homotopy fiber to the gluing face. -/
def facePartial : PartialSection
    (reindex (homotopyFiber (Functor.whiskerLeft (projection (reindex A (restrictInclusion φ))).mapElements e)
      (generic (reindex A (restrictInclusion φ))))
      (AmbientExtension.target φ A (σ ≫ projection A) (target A σ)))
    (ψ.reindex (restrictInclusion (face φ A σ))) := by
  let θ := face φ A σ
  let χ := ψ.reindex (restrictInclusion θ)
  let r := intersectionToPartial φ A σ (ψ := ψ)
  let g := (partialDomain φ A T e σ s).reindex r
  let p := restrictInclusion χ ≫ restrictInclusion θ ≫ σ ≫ projection A
  let c := Term.map (Functor.whiskerLeft p.mapElements (familyIso φ A T e).hom ≫
    compatibleReindexMap φ A T e p) g
  let t : Term (reindex T (restrictInclusion χ ≫ restrictSubstitution φ (σ ≫ projection A))) :=
    { val := fun x => (c.val x).face (𝟙 _) x.val.val.property
      property := by
        intro x y k
        have h := congrArg (fun z => z.face (𝟙 _) y.val.val.property) (c.property k)
        change (c.val x).face (k ≫ 𝟙 _) y.val.val.property = _ at h
        exact ((c.val x).naturality (𝟙 _) k x.val.val.property).trans (by
          simpa only [Category.id_comp, Category.comp_id] using h) }
  have ht : Term.map (Functor.whiskerLeft
      (restrictInclusion χ ≫ restrictSubstitution φ (σ ≫ projection A)).mapElements e) t =
      Term.map (Functor.whiskerLeft p.mapElements (f φ A T e)) g := by
    apply Term.ext
    intro x
    exact ((c.val x).compatible (𝟙 _) x.val.val.property).trans
      (ConcreteCategory.congr_hom ((reindex A p).map_id x) _)
  let q := homogeneousReindex (partialPath φ A T e σ s) r
  exact PartialSection.ofRestricted (genericFiberIntro e
    (restrictInclusion χ ≫ AmbientExtension.target φ A (σ ≫ projection A) (target A σ)) t
    (pathLam (pathApp q) ((pathApp_zero q).trans ht.symm) (pathApp_one q)))

variable (E : HomotopyEquivalence e) (F : Filling T) (hF : F.Lawful)
  (G : Filling A) (hG : G.Lawful)

noncomputable def faceFiber :=
  E.extendAlong F hF (G.reindex (restrictInclusion φ)) (hG.reindex _)
    (AmbientExtension.target φ A (σ ≫ projection A) (target A σ))
    (facePartial φ A T e σ s)

noncomputable def faceDomain :=
  genericFiberFst e (AmbientExtension.target φ A (σ ≫ projection A) (target A σ))
    (faceFiber φ A T e σ s E F hF G hG)

noncomputable def facePath :=
  homogeneousReverse (genericFiberPath e
    (AmbientExtension.target φ A (σ ≫ projection A) (target A σ))
    (faceFiber φ A T e σ s E F hF G hG))

noncomputable def faceTube :=
  restrictedPathTube (face φ A σ) (target A σ)
    (Term.map (Functor.whiskerLeft (restrictSubstitution φ (σ ≫ projection A)).mapElements e)
      (faceDomain φ A T e σ s E F hF G hG))
    (facePath φ A T e σ s E F hF G hG)

theorem faceFiber_boundary :
    (faceFiber φ A T e σ s E F hF G hG).reindex
      (restrictInclusion (ψ.reindex (restrictInclusion (face φ A σ)))) =
    (facePartial φ A T e σ s).toRestricted := by
  apply Term.ext
  intro x
  exact E.extendAlong_boundary F hF (G.reindex (restrictInclusion φ)) (hG.reindex _)
    _ _ ((restrictInclusion _).mapElements.obj x) x.val.property

theorem facePartial_path :
    pathApp (genericFiberPath e
      (restrictInclusion (ψ.reindex (restrictInclusion (face φ A σ))) ≫
        AmbientExtension.target φ A (σ ≫ projection A) (target A σ))
      (facePartial φ A T e σ s).toRestricted) =
    (pathApp (partialPath φ A T e σ s)).reindex
      (liftSub (interval (restrictContext ψ)) (intersectionToPartial φ A σ)) := by
  dsimp only [facePartial]
  exact congrArg pathApp (fiberIntro_path e _ _ _)

theorem tubes_compatible :
    (faceTube φ A T e σ s E F hF G hG).Compatible (partialTube φ A T e σ s) := by
  let χ := ψ.reindex (restrictInclusion (face φ A σ))
  have hp := congrArg (fun z => pathApp (genericFiberPath e
    (restrictInclusion χ ≫ AmbientExtension.target φ A (σ ≫ projection A) (target A σ)) z))
    (faceFiber_boundary φ A T e σ s E F hF G hG)
  have h := hp.trans (facePartial_path φ A T e σ s)
  intro x hx hy
  let y := (restrictContext χ).elementsMk x.obj ⟨⟨x.val.1,hx⟩,hy⟩
  exact congrArg (fun t => t.val
    (extendObj (interval (restrictContext χ)) y
      (ULift.up (Cube.comp x.val.2.down Cube.reversal)))) h

noncomputable def box : OpenBox (reindex A (projection (interval Δ) ≫ σ ≫ projection A))
    ((face φ A σ).join ψ) where
  tube := (faceTube φ A T e σ s E F hF G hG).glue (partialTube φ A T e σ s)
    (tubes_compatible φ A T e σ s E F hF G hG)
  base := target A σ
  boundary x hx := by
    rcases (Cofibration.full_join _ _ x).mp hx with hφ | hψ
    · exact (glueValue_left (faceTube φ A T e σ s E F hF G hG)
        (partialTube φ A T e σ s) ((endpointSub Δ false).mapElements.obj x) hx hφ).trans
        (restrictedPathTube_zero _ _ _ _ x hφ)
    · exact (glueValue_right (faceTube φ A T e σ s E F hF G hG)
        (partialTube φ A T e σ s) (tubes_compatible φ A T e σ s E F hF G hG)
        ((endpointSub Δ false).mapElements.obj x) hx hψ).trans
        (restrictedPathTube_zero _ _ _ _ x hψ)

noncomputable def filled := G.fill (projection (interval Δ) ≫ σ ≫ projection A)
  ((face φ A σ).join ψ) (box φ A T e σ s E F hF G hG)

noncomputable def ambient := (filled φ A T e σ s E F hF G hG).reindex (endpointSub Δ true)

theorem filled_face (x : (total (interval Δ)).Elements)
    (hx : ((face φ A σ).reindex (projection (interval Δ))).full x) :
    (filled φ A T e σ s E F hF G hG).val x =
    (faceTube φ A T e σ s E F hF G hG).val x hx := by
  have hu := (Cofibration.full_join (face φ A σ) ψ
    ((projection (interval Δ)).mapElements.obj x)).mpr (Or.inl hx)
  exact ((hG.fills _ _ (box φ A T e σ s E F hF G hG)).2 x hu).trans
    (glueValue_left _ _ x hu hx)

theorem filled_partial (x : (total (interval Δ)).Elements)
    (hx : (ψ.reindex (projection (interval Δ))).full x) :
    (filled φ A T e σ s E F hF G hG).val x =
    (partialTube φ A T e σ s).val x hx := by
  have hu := (Cofibration.full_join (face φ A σ) ψ
    ((projection (interval Δ)).mapElements.obj x)).mpr (Or.inr hx)
  exact ((hG.fills _ _ (box φ A T e σ s E F hF G hG)).2 x hu).trans
    (glueValue_right _ _ (tubes_compatible φ A T e σ s E F hF G hG) x hu hx)

theorem ambient_face :
    Term.map (Functor.whiskerLeft (restrictSubstitution φ (σ ≫ projection A)).mapElements e)
      (faceDomain φ A T e σ s E F hF G hG) =
    (ambient φ A T e σ s E F hF G hG).reindex (restrictInclusion (face φ A σ)) := by
  apply Term.ext
  intro x
  exact ((filled_face φ A T e σ s E F hF G hG
    ((endpointSub Δ true).mapElements.obj ((restrictInclusion _).mapElements.obj x)) x.val.property).trans
    (restrictedPathTube_one _ _ _ _ ((restrictInclusion _).mapElements.obj x) x.val.property)).symm

noncomputable def domainCompatible :=
  compatibleIntro (face φ A σ) (reindex A (σ ≫ projection A))
    (reindex T (restrictSubstitution φ (σ ≫ projection A)))
    (Functor.whiskerLeft (restrictSubstitution φ (σ ≫ projection A)).mapElements e)
    (faceDomain φ A T e σ s E F hF G hG) (ambient φ A T e σ s E F hF G hG)
    (ambient_face φ A T e σ s E F hF G hG)

noncomputable def domain :=
  Term.map (Functor.whiskerLeft (σ ≫ projection A).mapElements (familyIso φ A T e).inv)
    (Term.map (compatibleReindexIso φ A T e (σ ≫ projection A)).inv
      (domainCompatible φ A T e σ s E F hF G hG))

theorem domain_image :
    Term.map (Functor.whiskerLeft (σ ≫ projection A).mapElements (f φ A T e))
      (domain φ A T e σ s E F hF G hG) = ambient φ A T e σ s E F hF G hG := by
  apply Term.ext
  intro x
  exact congrArg (fun z => z.ambient)
    (congrArg (fun η => η.app ((σ ≫ projection A).mapElements.obj x)
      ((compatibleReindexIso φ A T e (σ ≫ projection A)).inv.app x
        ((domainCompatible φ A T e σ s E F hF G hG).val x)))
      (familyIso φ A T e).inv_hom_id)

noncomputable def resultPath : Term (homogeneousPath (reindex A (σ ≫ projection A))
    (Term.map (Functor.whiskerLeft (σ ≫ projection A).mapElements (f φ A T e))
      (domain φ A T e σ s E F hF G hG)) (target A σ)) :=
  pathLam (pathApp (homogeneousReverse (pathLam (filled φ A T e σ s E F hF G hG)
    (hG.fills _ _ (box φ A T e σ s E F hF G hG)).1 rfl)))
    ((pathApp_zero _).trans (domain_image φ A T e σ s E F hF G hG).symm)
    (pathApp_one _)

noncomputable def extension := genericFiberIntro (f φ A T e) σ
  (domain φ A T e σ s E F hF G hG) (resultPath φ A T e σ s E F hF G hG)

theorem faceDomain_boundary (x : (restrictContext (face φ A σ)).Elements)
    (hx : (ψ.reindex (restrictInclusion (face φ A σ))).full x) :
    (faceDomain φ A T e σ s E F hF G hG).val x =
    ((familyIso φ A T e).hom.app ((σ ≫ projection A).mapElements.obj
      ((restrictInclusion (face φ A σ)).mapElements.obj x))
      (s.val ((restrictInclusion (face φ A σ)).mapElements.obj x) hx).1).face (𝟙 _) x.val.property := by
  exact congrArg Sigma.fst (E.extendAlong_boundary F hF
    (G.reindex (restrictInclusion φ)) (hG.reindex _) _ (facePartial φ A T e σ s) x hx)

theorem domainCompatible_boundary (x : Δ.Elements) (hx : ψ.full x) :
    (domainCompatible φ A T e σ s E F hF G hG).val x =
    (compatibleReindexMap φ A T e (σ ≫ projection A)).app x
      ((familyIso φ A T e).hom.app ((σ ≫ projection A).mapElements.obj x) (s.val x hx).1) := by
  apply CompatibleElement.ext
  · exact (filled_partial φ A T e σ s E F hF G hG
      ((endpointSub Δ true).mapElements.obj x) hx).trans
      (restrictedPathTube_one _ _ _ _ x hx)
  · intro y k hy
    have h := faceDomain_boundary φ A T e σ s E F hF G hG
      (faceObj (face φ A σ) y hy) (ψ.full_natural k hx)
    have hs := congrArg (fun z => ((familyIso φ A T e).hom.app
      ((σ ≫ projection A).mapElements.obj y) z).face (𝟙 _) hy)
      ((partialDomain φ A T e σ s).property (faceHom ψ k hx))
    have hn := congrArg (fun z => z.face (𝟙 _) hy)
      ((familyIso φ A T e).hom.naturality_apply ((σ ≫ projection A).mapElements.map k)
        (s.val x hx).1)
    apply h.trans
    apply hs.symm.trans
    change _ = ((familyIso φ A T e).hom.app ((σ ≫ projection A).mapElements.obj x)
      (s.val x hx).1).face ((σ ≫ projection A).mapElements.map k) hy
    change _ = ((familyIso φ A T e).hom.app ((σ ≫ projection A).mapElements.obj x)
      (s.val x hx).1).face (((σ ≫ projection A).mapElements.map k) ≫ 𝟙 _) hy at hn
    change ((familyIso φ A T e).hom.app ((σ ≫ projection A).mapElements.obj y)
      ((family φ A T e).map ((σ ≫ projection A).mapElements.map k) (s.val x hx).1)).face
      (𝟙 _) hy = _
    simpa only [Category.comp_id] using hn

theorem domain_boundary :
    (domain φ A T e σ s E F hF G hG).reindex (restrictInclusion ψ) =
    partialDomain φ A T e σ s := by
  apply Term.ext
  intro x
  let y := (restrictInclusion ψ).mapElements.obj x
  have h := congrArg (fun z => (familyIso φ A T e).inv.app
    ((σ ≫ projection A).mapElements.obj y)
    ((compatibleReindexIso φ A T e (σ ≫ projection A)).inv.app y z))
    (domainCompatible_boundary φ A T e σ s E F hF G hG y x.val.property)
  exact h.trans ((congrArg ((familyIso φ A T e).inv.app ((σ ≫ projection A).mapElements.obj y))
    (congrArg (fun η => η.app y ((familyIso φ A T e).hom.app
      ((σ ≫ projection A).mapElements.obj y) (s.val y x.val.property).1))
      (compatibleReindexIso φ A T e (σ ≫ projection A)).hom_inv_id)).trans
    (congrArg (fun η => η.app ((σ ≫ projection A).mapElements.obj y)
      (s.val y x.val.property).1) (familyIso φ A T e).hom_inv_id))

theorem filled_partial_section :
    (filled φ A T e σ s E F hF G hG).reindex (liftSub (interval Δ) (restrictInclusion ψ)) =
    pathApp (homogeneousReverse (partialPath φ A T e σ s)) := by
  apply Term.ext
  intro x
  exact filled_partial φ A T e σ s E F hF G hG
    ((liftSub (interval Δ) (restrictInclusion ψ)).mapElements.obj x) x.val.1.property

theorem resultPath_boundary :
    (pathApp (resultPath φ A T e σ s E F hF G hG)).reindex
      (liftSub (interval Δ) (restrictInclusion ψ)) = pathApp (partialPath φ A T e σ s) := by
  have h := congrArg (fun t => t.reindex (reverseInterval (restrictContext ψ)))
    (filled_partial_section φ A T e σ s E F hF G hG)
  exact h.trans (reverse_pathApp_twice (partialPath φ A T e σ s))

theorem extension_restricted :
    (extension φ A T e σ s E F hF G hG).reindex (restrictInclusion ψ) = s.toRestricted :=
  fiberIntro_reindex_eq (f φ A T e) σ (domain φ A T e σ s E F hF G hG)
    (resultPath φ A T e σ s E F hF G hG) (restrictInclusion ψ) s.toRestricted
    (domain_boundary φ A T e σ s E F hF G hG) (resultPath_boundary φ A T e σ s E F hF G hG)

theorem extension_boundary (x : Δ.Elements) (hx : ψ.full x) :
    (extension φ A T e σ s E F hF G hG).val x = s.val x hx :=
  congrArg (fun t => t.val ((restrictContext ψ).elementsMk x.obj ⟨x.val,hx⟩))
    (extension_restricted φ A T e σ s E F hF G hG)

end UnglueFiber

/-- Glue elimination has contractible native homotopy fibers. Both their center
and contraction are constructed from the supplied equivalence and lawful fillers. -/
noncomputable def unglueEquivalence {Γ : Context.{u}} (φ : Cofibration Γ) (A : Family Γ)
    (T : Family (restrictContext φ)) (e : T ⟶ reindex A (restrictInclusion φ))
    (E : HomotopyEquivalence e) (F : Filling T) (hF : F.Lawful)
    (G : Filling A) (hG : G.Lawful) : HomotopyEquivalence (unglue φ A T e) where
  fibers := HomotopyContractible.ofExtensions
    (fun σ _ s => UnglueFiber.extension φ A T e σ s E F hF G hG)
    (fun σ _ s x hx => UnglueFiber.extension_boundary φ A T e σ s E F hF G hG x hx)

end SquareKit.Cubical.Presheaf.Glue
