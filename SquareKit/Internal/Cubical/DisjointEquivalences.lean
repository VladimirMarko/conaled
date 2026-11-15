import SquareKit.Internal.Cubical.SmallFamilyGlue

/-! Native contractions and equivalences assemble over disjoint face covers. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace DisjointCover
variable {Γ : Context.{u}} (φ ψ : Cofibration Γ)
  (cover : ∀ x : Γ.Elements, φ.full x ∨ ψ.full x)
  (disjoint : ∀ x : Γ.Elements, φ.full x → ψ.full x → False)

noncomputable def assemble {A : Family Γ} (a : PartialSection A φ) (b : PartialSection A ψ) : Term A where
  val x := (a.glue b (fun x h k => (disjoint x h k).elim)).val x
    ((Cofibration.full_join φ ψ x).mpr (cover x))
  property f := (a.glue b (fun x h k => (disjoint x h k).elim)).property f _

theorem section_left {A : Family Γ} (a : PartialSection A φ) (b : PartialSection A ψ)
    (x : Γ.Elements) (hx : φ.full x) : (assemble φ ψ cover disjoint a b).val x = a.val x hx :=
  glueValue_left a b x ((Cofibration.full_join φ ψ x).mpr (cover x)) hx

theorem section_right {A : Family Γ} (a : PartialSection A φ) (b : PartialSection A ψ)
    (x : Γ.Elements) (hx : ψ.full x) : (assemble φ ψ cover disjoint a b).val x = b.val x hx :=
  glueValue_right a b (fun x h k => (disjoint x h k).elim) x
    ((Cofibration.full_join φ ψ x).mpr (cover x)) hx

variable {A : Family Γ}
  (a : HomotopyContractible (reindex A (restrictInclusion φ)))
  (b : HomotopyContractible (reindex A (restrictInclusion ψ)))

noncomputable def center : Term A :=
  assemble φ ψ cover disjoint (PartialSection.ofRestricted a.center) (PartialSection.ofRestricted b.center)

def contractionRestriction :
    restrictContext (φ.reindex (projection (interval (total A)) ≫ projection A)) ⟶
      total (interval (total (reindex A (restrictInclusion φ)))) where
  app _ := TypeCat.ofHom (fun z => ⟨⟨⟨z.val.1.1,z.property⟩,z.val.1.2⟩,z.val.2⟩)
  naturality _ _ _ := rfl

def contractionPartial : PartialSection
    (reindex A (projection (interval (total A)) ≫ projection A))
    (φ.reindex (projection (interval (total A)) ≫ projection A)) :=
  PartialSection.ofRestricted ((pathApp a.contraction).reindex (contractionRestriction φ))

theorem contractionPartial_zero (x : (total A).Elements) (hx : (φ.reindex (projection A)).full x) :
    (contractionPartial φ a).val ((endpointSub (total A) false).mapElements.obj x) hx =
    a.center.val ((restrictContext φ).elementsMk x.obj ⟨x.val.1,hx⟩) :=
  congrArg (fun t => t.val ((total (reindex A (restrictInclusion φ))).elementsMk x.obj
    ⟨⟨x.val.1,hx⟩,x.val.2⟩)) (pathApp_zero a.contraction)

theorem contractionPartial_one (x : (total A).Elements) (hx : (φ.reindex (projection A)).full x) :
    (contractionPartial φ a).val ((endpointSub (total A) true).mapElements.obj x) hx = x.val.2 :=
  congrArg (fun t => t.val ((total (reindex A (restrictInclusion φ))).elementsMk x.obj
    ⟨⟨x.val.1,hx⟩,x.val.2⟩)) (pathApp_one a.contraction)

noncomputable def contractionSection :=
  assemble (φ.reindex (projection (interval (total A)) ≫ projection A))
    (ψ.reindex (projection (interval (total A)) ≫ projection A))
    (fun x => cover ((projection (interval (total A)) ≫ projection A).mapElements.obj x))
    (fun x => disjoint ((projection (interval (total A)) ≫ projection A).mapElements.obj x))
    (contractionPartial φ a) (contractionPartial ψ b)

theorem contractionSection_left (x : (total (interval (total A))).Elements)
    (hx : (φ.reindex (projection (interval (total A)) ≫ projection A)).full x) :
    (contractionSection φ ψ cover disjoint a b).val x = (contractionPartial φ a).val x hx :=
  section_left _ _ _ _ _ _ x hx

theorem contractionSection_right (x : (total (interval (total A))).Elements)
    (hx : (ψ.reindex (projection (interval (total A)) ≫ projection A)).full x) :
    (contractionSection φ ψ cover disjoint a b).val x = (contractionPartial ψ b).val x hx :=
  section_right _ _ _ _ _ _ x hx

theorem contractionSection_zero :
    (contractionSection φ ψ cover disjoint a b).reindex (endpointSub (total A) false) =
    (center φ ψ cover disjoint a b).reindex (projection A) := by
  apply Term.ext
  intro x
  rcases cover ((projection A).mapElements.obj x) with hx | hx
  · exact (contractionSection_left φ ψ cover disjoint a b ((endpointSub (total A) false).mapElements.obj x) hx).trans
      ((contractionPartial_zero φ a x hx).trans
        (section_left φ ψ cover disjoint (PartialSection.ofRestricted a.center)
          (PartialSection.ofRestricted b.center) ((projection A).mapElements.obj x) hx).symm)
  · exact (contractionSection_right φ ψ cover disjoint a b ((endpointSub (total A) false).mapElements.obj x) hx).trans
      ((contractionPartial_zero ψ b x hx).trans
        (section_right φ ψ cover disjoint (PartialSection.ofRestricted a.center)
          (PartialSection.ofRestricted b.center) ((projection A).mapElements.obj x) hx).symm)

theorem contractionSection_one :
    (contractionSection φ ψ cover disjoint a b).reindex (endpointSub (total A) true) = generic A := by
  apply Term.ext
  intro x
  rcases cover ((projection A).mapElements.obj x) with hx | hx
  · exact (contractionSection_left φ ψ cover disjoint a b ((endpointSub (total A) true).mapElements.obj x) hx).trans
      (contractionPartial_one φ a x hx)
  · exact (contractionSection_right φ ψ cover disjoint a b ((endpointSub (total A) true).mapElements.obj x) hx).trans
      (contractionPartial_one ψ b x hx)

noncomputable def contractible : HomotopyContractible A where
  center := center φ ψ cover disjoint a b
  contraction := pathLam (contractionSection φ ψ cover disjoint a b)
    (contractionSection_zero φ ψ cover disjoint a b) (contractionSection_one φ ψ cover disjoint a b)

/-- Restriction recovers the supplied center and whole contraction, not merely
existence of some contractibility witness. -/
theorem contractible_left : (contractible φ ψ cover disjoint a b).reindex (restrictInclusion φ) = a := by
  apply HomotopyContractible.ext
  · apply Term.ext
    intro x
    exact section_left φ ψ cover disjoint (PartialSection.ofRestricted a.center)
      (PartialSection.ofRestricted b.center) ((restrictInclusion φ).mapElements.obj x) x.val.property
  · apply pathTerm_hext
    apply Term.ext
    intro x
    exact contractionSection_left φ ψ cover disjoint a b
      ((liftSub (interval (total A)) (liftSub A (restrictInclusion φ))).mapElements.obj x)
      x.val.1.1.property

theorem contractible_right : (contractible φ ψ cover disjoint a b).reindex (restrictInclusion ψ) = b := by
  apply HomotopyContractible.ext
  · apply Term.ext
    intro x
    exact section_right φ ψ cover disjoint (PartialSection.ofRestricted a.center)
      (PartialSection.ofRestricted b.center) ((restrictInclusion ψ).mapElements.obj x) x.val.property
  · apply pathTerm_hext
    apply Term.ext
    intro x
    exact contractionSection_right φ ψ cover disjoint a b
      ((liftSub (interval (total A)) (liftSub A (restrictInclusion ψ))).mapElements.obj x)
      x.val.1.1.property

theorem contractible_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    (contractible φ ψ cover disjoint a b).reindex σ =
    contractible (φ.reindex σ) (ψ.reindex σ)
      (fun x => cover (σ.mapElements.obj x)) (fun x => disjoint (σ.mapElements.obj x))
      (a.reindex (restrictSubstitution φ σ)) (b.reindex (restrictSubstitution ψ σ)) := by
  apply HomotopyContractible.ext
  · apply Term.ext
    intro x
    rfl
  · apply pathTerm_hext
    apply Term.ext
    intro x
    rfl

end DisjointCover
namespace CodeSystem.Maps
variable {Γ : Context.{u}} {φ ψ : Cofibration Γ}
  {A B : Family (restrictContext (φ.join ψ))}
  (a : reindex A (includeLeft φ ψ) ⟶ reindex B (includeLeft φ ψ))
  (b : reindex A (includeRight φ ψ) ⟶ reindex B (includeRight φ ψ))
  (disjoint : ∀ x : Γ.Elements, φ.full x → ψ.full x → False)

include disjoint in
theorem disjointCompatible : Compatible a b := fun x h k _ => (disjoint (original x) h k).elim

abbrev targetBase (B : Family (restrictContext (φ.join ψ))) :=
  projection B ≫ restrictInclusion (φ.join ψ)

def leftTarget (B : Family (restrictContext (φ.join ψ))) :
    restrictContext (φ.reindex (targetBase B)) ⟶ total (reindex B (includeLeft φ ψ)) where
  app _ := TypeCat.ofHom (fun z => ⟨⟨z.val.1.val,z.property⟩,z.val.2⟩)
  naturality _ _ _ := rfl

def rightTarget (B : Family (restrictContext (φ.join ψ))) :
    restrictContext (ψ.reindex (targetBase B)) ⟶ total (reindex B (includeRight φ ψ)) where
  app _ := TypeCat.ofHom (fun z => ⟨⟨z.val.1.val,z.property⟩,z.val.2⟩)
  naturality _ _ _ := rfl

def leftEquivalence (ea : HomotopyEquivalence a) :
    HomotopyEquivalence (Functor.whiskerLeft (includeLeft φ ψ).mapElements
      (glue a b (disjointCompatible a b disjoint))) :=
  (glue_left a b (disjointCompatible a b disjoint)).symm ▸ ea

def rightEquivalence (eb : HomotopyEquivalence b) :
    HomotopyEquivalence (Functor.whiskerLeft (includeRight φ ψ).mapElements
      (glue a b (disjointCompatible a b disjoint))) :=
  (glue_right a b (disjointCompatible a b disjoint)).symm ▸ eb

/-- Each branch contributes its existing selected native fiber contraction. -/
noncomputable def disjointEquivalence (ea : HomotopyEquivalence a) (eb : HomotopyEquivalence b) :
    HomotopyEquivalence (glue a b (disjointCompatible a b disjoint)) where
  fibers := DisjointCover.contractible (φ.reindex (targetBase B)) (ψ.reindex (targetBase B))
    (fun x => (Cofibration.full_join φ ψ ((targetBase B).mapElements.obj x)).mp x.val.1.property)
    (fun x => disjoint ((targetBase B).mapElements.obj x))
    (((leftEquivalence a b disjoint ea).fibers.transport
      (genericFiberReindexIso (glue a b (disjointCompatible a b disjoint)) (includeLeft φ ψ)).symm).reindex
        (leftTarget B))
    (((rightEquivalence a b disjoint eb).fibers.transport
      (genericFiberReindexIso (glue a b (disjointCompatible a b disjoint)) (includeRight φ ψ)).symm).reindex
        (rightTarget B))

theorem disjointEquivalence_left_fibers (ea : HomotopyEquivalence a) (eb : HomotopyEquivalence b) :
    (disjointEquivalence a b disjoint ea eb).fibers.reindex
      (restrictInclusion (φ.reindex (targetBase B))) =
    ((leftEquivalence a b disjoint ea).fibers.transport
      (genericFiberReindexIso (glue a b (disjointCompatible a b disjoint)) (includeLeft φ ψ)).symm).reindex
        (leftTarget B) :=
  DisjointCover.contractible_left _ _ _ _ _ _

theorem disjointEquivalence_right_fibers (ea : HomotopyEquivalence a) (eb : HomotopyEquivalence b) :
    (disjointEquivalence a b disjoint ea eb).fibers.reindex
      (restrictInclusion (ψ.reindex (targetBase B))) =
    ((rightEquivalence a b disjoint eb).fibers.transport
      (genericFiberReindexIso (glue a b (disjointCompatible a b disjoint)) (includeRight φ ψ)).symm).reindex
        (rightTarget B) :=
  DisjointCover.contractible_right _ _ _ _ _ _

end CodeSystem.Maps
end SquareKit.Cubical.Presheaf
