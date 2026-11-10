import SquareKit.Internal.PathTransport.GeneratedCylinderFamilyLaws

/-! Recovery of the supplied primitive natural-isomorphism components. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

abbrev primitiveContext : Typed.CtxDeriv [Expr.base]
    (Typed.extendCode Typed.emptyCode.{u+1} (Typed.baseCode Typed.emptyCode)) :=
  .ext .empty (.base .empty)

def primitiveFunctor {C D : Grpd.{u,u}} (F : C ⥤ D) :
    Extend (constant C (Γ := Discrete PUnit.{u+1})) ⥤ Extend (constant D (Γ := Discrete PUnit.{u+1})) :=
  Grothendieck.map (whiskerRight
    (show constant C (Γ := Discrete PUnit.{u+1}) ⟶ constant D from
      { app := fun _ => F, naturality := fun {_ _} _ => rfl }) Grpd.forgetToCat)

theorem generatedPrimitive_map (S : Signature.{u}) :
    generatedContextMap S primitiveContext = primitiveFunctor S.base.map := by
  rw [generatedContextMap_extend, generatedFamilyMap_base, generatedContextMap_empty]
  rfl

def primitiveIso {C D : Grpd.{u,u}} {F G : C ⥤ D} (η : F ≅ G) :
    primitiveFunctor F ≅ primitiveFunctor G :=
  FamilyModification.totalIso (baseModification η (Discrete PUnit.{u+1}))

theorem primitiveIso_fiber {C D : Grpd.{u,u}} {F G : C ⥤ D} (η : F ≅ G) (c : C) :
    ((primitiveIso η).hom.app ⟨⟨PUnit.unit⟩, c⟩).fiber = η.hom.app c := by
  simp [primitiveIso, FamilyModification.totalIso, FamilyModification.totalComponent,
    baseModification, Grothendieck.ι, constant]

variable {C D : Grpd.{u,u}} (F : C ⥤ D) (P : C ⥤ Type u) {G : C ⥤ D} (η : F ≅ G)

theorem generatedEndpointIso_primitive :
    generatedEndpointIso F P η primitiveContext =
      eqToIso (generatedPrimitive_map (inclusionSignature F P)) ≪≫
        primitiveIso (endpointIso F η) ≪≫
        (eqToIso (generatedPrimitive_map (endpointSignature F P η))).symm := by
  let : (projectionSignature F P).base.map.IsEquivalence :=
    inferInstanceAs (projection F).IsEquivalence
  let := generatedContextMap_equivalence (projectionSignature F P)
    (fun _ => Function.bijective_id) primitiveContext
  unfold generatedEndpointIso
  apply selectedLift_unique
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    whiskerRight_app, eqToIso.hom, Iso.symm_hom, eqToIso.inv, eqToHom_app, Functor.map_comp, eqToHom_map]
  have hn := (eqToHom (generatedPrimitive_map (projectionSignature F P))).naturality
    ((primitiveIso (endpointIso F η)).hom.app x)
  have hn' := congrArg (fun f => f ≫ eqToHom (congrArg
    (fun J => J.obj ((primitiveFunctor (endpoint F η)).obj x))
      (generatedPrimitive_map (projectionSignature F P)).symm)) hn
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp, NatTrans.id_app] at hn'
  rw [hn']
  simp [primitiveFunctor, primitiveIso, FamilyModification.totalIso,
    FamilyModification.totalComponent, baseModification, endpointIso,
    Grothendieck.map, Grothendieck.ι, constant]

  rfl

variable (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q)
variable (h : α ≫ whiskerRight η.hom Q = β)

theorem contextComparison_primitive :
    contextComparison F P η Q α β h primitiveContext =
      eqToIso (generatedPrimitive_map (Signature.mk (Context.mk C D F) P Q α)) ≪≫
        primitiveIso η ≪≫
        (eqToIso (generatedPrimitive_map (Signature.mk (Context.mk C D G) P Q β))).symm := by
  cases h
  rw [contextComparison_formula]
  simp only [generatedComparison, generatedEndpointIso_primitive]
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    whiskerRight_app, eqToIso.hom, Iso.symm_hom, eqToIso.inv, eqToHom_app,
    Functor.map_comp, eqToHom_map]
  have hn := (eqToHom (generatedPrimitive_map (evaluationSignature F P Q α))).naturality
    ((primitiveIso (endpointIso F η)).hom.app x)
  simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp, Category.comp_id] at hn
  rw [hn]
  simp [primitiveFunctor, primitiveIso, FamilyModification.totalIso,
    FamilyModification.totalComponent, baseModification, endpointIso,
    Grothendieck.map, Grothendieck.ι, constant]
  fapply Grothendieck.ext
  · rfl
  · simp [evaluationSignature, evaluation, inclusion, endpoint, Grpd.forgetToCat]
    change (𝟙 _) ≫ η.hom.app x.fiber ≫ G.map (𝟙 x.fiber) = _
    simp

/-- Normalize only the generated endpoint functors, retaining the chosen arrow. -/
def normalizedPrimitiveComparison : primitiveFunctor F ≅ primitiveFunctor G :=
  (eqToIso (generatedPrimitive_map (Signature.mk (Context.mk C D F) P Q α))).symm ≪≫
    contextComparison F P η Q α β h primitiveContext ≪≫
    eqToIso (generatedPrimitive_map (Signature.mk (Context.mk C D G) P Q β))

theorem normalizedPrimitiveComparison_eq :
    normalizedPrimitiveComparison F P η Q α β h = primitiveIso η := by
  simp [normalizedPrimitiveComparison, contextComparison_primitive]
  ext x
  simp
  change (𝟙 ((primitiveFunctor F).obj x)) ≫ (primitiveIso η).hom.app x ≫
    (𝟙 ((primitiveFunctor G).obj x)) = _
  simp

theorem normalizedPrimitiveComparison_fiber (c : C) :
    ((normalizedPrimitiveComparison F P η Q α β h).hom.app ⟨⟨PUnit.unit⟩, c⟩).fiber =
      η.hom.app c := by
  rw [normalizedPrimitiveComparison_eq, primitiveIso_fiber]

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
