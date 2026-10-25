import SquareKit.Internal.PresheafRepresentation
import SquareKit.Internal.FiniteModelCategory
import SquareKit.Internal.PartitionSection
import SquareKit.SliceExtensive

/-! The existing formed presheaf is the actual parameter-plus-terminal object
in the presheaf slice. Its injections retain the selected witness and base point. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
namespace SquareKit.Internal.PresheafSetting
open CategoryTheory CategoryTheory.Limits Opposite
universe v
variable {J : Type v} [SmallCategory J] {X : Jᵒᵖ ⥤ Type}
variable (T : Presentation X)

def parameterDisplay : Over X := Over.mk T.ι

def formedLeft : parameterDisplay T ⟶ Over.mk (projection T) :=
  Over.homMk { app j := ↾fun x => ⟨x.val, Sum.inl ⟨x.property⟩⟩ } rfl

def formedRight : Over.mk (𝟙 X) ⟶ Over.mk (projection T) :=
  Over.homMk { app j := ↾fun x => ⟨x, Sum.inr ()⟩ } rfl

/-- The eliminator keeps the original left witness and right singleton separate. -/
def formedDesc {Z : Over X} (l : parameterDisplay T ⟶ Z) (r : Over.mk (𝟙 X) ⟶ Z) :
    Over.mk (projection T) ⟶ Z :=
  Over.homMk {
    app j := ↾fun x => match x.2 with
      | .inl h => l.left.app j ⟨x.1, h.down⟩
      | .inr _ => r.left.app j x.1
    naturality j k f := by
      ext x
      rcases x with ⟨x, h | h⟩
      · exact NatTrans.naturality_apply l.left f ⟨x, h.down⟩
      · exact NatTrans.naturality_apply r.left f x }
    (by
      ext j x
      rcases x with ⟨x, h | h⟩
      · exact congrArg (fun t => t.app j ⟨x, h.down⟩) (Over.w l)
      · exact congrArg (fun t => t.app j x) (Over.w r))

/-- The formation object satisfies the categorical coproduct universal property in the slice. -/
def formedCoproduct : IsColimit (BinaryCofan.mk (formedLeft T) (formedRight T)) :=
  BinaryCofan.IsColimit.mk _ (fun l r => formedDesc T l r)
    (fun l r => by ext j x; rfl)
    (fun l r => by ext j x; rfl)
    (by
      intro Z l r m hl hr
      apply Over.OverMorphism.ext
      ext j x
      rcases x with ⟨x, h | h⟩
      · exact congrArg (fun t => t.left.app j ⟨x, h.down⟩) hl
      · exact congrArg (fun t => t.left.app j x) hr)

/-- The chosen formed object is isomorphic to the classifier's parameter-plus-terminal object. -/
def formedClassifierIso : Over.mk (projection T) ≅ parameterDisplay T ⨿ ⊤_ (Over X) :=
  (formedCoproduct T).coconePointUniqueUpToIso (coprodIsCoprod (parameterDisplay T) (Over.mk (𝟙 X))) ≪≫
    coprod.mapIso (Iso.refl _) (Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal)
/-- The formed left injection is exactly the classifier's parameter injection. -/
@[reassoc (attr := simp)] theorem formedLeft_classifier :
    formedLeft T ≫ (formedClassifierIso T).hom = coprod.inl := by
  have hi := (formedCoproduct T).comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (parameterDisplay T) (Over.mk (𝟙 X))) ⟨WalkingPair.left⟩
  change formedLeft T ≫ _ = coprod.inl at hi
  change formedLeft T ≫ _ ≫ coprod.map (𝟙 _) _ = _
  rw [← Category.assoc, hi, coprod.inl_map, Category.id_comp]

/-- The formed right injection is the classifier's terminal injection. -/
@[reassoc (attr := simp)] theorem formedRight_classifier :
    formedRight T ≫ (formedClassifierIso T).hom =
      (Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal).hom ≫ coprod.inr := by
  have hi := (formedCoproduct T).comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (parameterDisplay T) (Over.mk (𝟙 X))) ⟨WalkingPair.right⟩
  change formedRight T ≫ _ = coprod.inr at hi
  change formedRight T ≫ _ ≫ coprod.map (𝟙 _) _ = _
  rw [← Category.assoc, hi, coprod.inr_map]

/-- The parameter subobject is viewed as a subterminal of the slice. -/
def parameterTerminal : parameterDisplay T ⟶ ⊤_ (Over X) :=
  (Over.homMk T.ι (by exact Category.comp_id _) : parameterDisplay T ⟶ Over.mk (𝟙 X)) ≫ (Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal).hom

instance : Mono (parameterTerminal T) := by
  unfold parameterTerminal
  have : Mono (Over.homMk T.ι (by exact Category.comp_id _) : parameterDisplay T ⟶ Over.mk (𝟙 X)) := by
    apply Over.mono_of_mono_left
  infer_instance

/-- The previous representation theorem becomes the literal section type of the new classifier object. -/
def modelClassifierSectionEquiv : Model T ≃ (⊤_ (Over X) ⟶ parameterDisplay T ⨿ ⊤_ (Over X)) :=
  (modelOverEquiv T (𝟙 X)).trans {
    toFun k := (Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal).inv ≫ k ≫ (formedClassifierIso T).hom
    invFun s := (Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal).hom ≫ s ≫ (formedClassifierIso T).inv
    left_inv k := by simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    right_inv s := by simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] }

/-- The original model category is discrete because its predicate-preserving maps force equality. -/
def modelDiscreteEquivalence : Model T ≌ Discrete (Model T) :=
  (modelComplementaryEquivalence T).trans
    ((ComplementaryModel.discreteEquivalence T).trans
      (Discrete.equivalence (modelComplementaryEquiv T).symm))

/-- The old presheaf models and the classifier's categorical predicate models agree on morphisms. -/
def modelPartitionEquivalence : Model T ≌ PartitionSection.Model (parameterTerminal T) :=
  (modelDiscreteEquivalence T).trans
    ((Discrete.equivalence (modelClassifierSectionEquiv T)).trans
      (PartitionSection.sectionEquivalence (parameterTerminal T)).symm)

/-- The comparison retains the previous graph/classifying map, with only the explicit object isomorphism. -/
theorem modelClassifierSection_graph (M : Model T) :
    modelClassifierSectionEquiv T M =
      (Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal).inv ≫
        classify T (𝟙 X) M ≫ (formedClassifierIso T).hom := rfl
end SquareKit.Internal.PresheafSetting
