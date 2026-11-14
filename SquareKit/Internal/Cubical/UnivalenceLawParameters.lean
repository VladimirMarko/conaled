import SquareKit.Internal.Cubical.NativeUnivalence

/-! Parameter contexts for choosing compositional univalence laws naturally. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.UnivalenceLawParameters
open CategoryTheory NativeUnivalence
universe u

section GenericClassifier
variable {Ξ Γ Δ : Context.{u+1}} (a b : Ξ ⟶ smallFamilyCodes.{u})

noncomputable def classifyAlong (σ : Γ ⟶ Ξ)
    (f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ b)) (E : HomotopyEquivalence f) :
    Γ ⟶ total (equivalences a b) :=
  pair σ (EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ ⟨f,E⟩)

theorem classifyAlong_comp (σ : Γ ⟶ Ξ)
    (f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ b)) (E : HomotopyEquivalence f) (τ : Δ ⟶ Γ) :
    τ ≫ classifyAlong a b σ f E =
      classifyAlong a b (τ ≫ σ) (Functor.whiskerLeft τ.mapElements f) (E.reindex τ) :=
  congrArg (pair (A := equivalences a b) (τ ≫ σ))
    (EquivalenceFamilies.equivReindexSections_comp (liftedDecode a) (liftedDecode b) σ τ f E).symm

theorem genericEquivalence_beta (σ : Γ ⟶ Ξ)
    (f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ b)) (E : HomotopyEquivalence f) :
    (⟨Functor.whiskerLeft (classifyAlong a b σ f E).mapElements (genericEquivalence a b).1,
      (genericEquivalence a b).2.reindex (classifyAlong a b σ f E)⟩ :
      Σ g : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ b), HomotopyEquivalence g) = ⟨f,E⟩ := by
  let S := EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ
  let T := EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b)
    (projection (equivalences a b))
  let τ := classifyAlong a b σ f E
  have h := EquivalenceFamilies.equivReindexSections_comp (liftedDecode a) (liftedDecode b)
    (projection (equivalences a b)) τ (genericEquivalence a b).1 (genericEquivalence a b).2
  apply S.injective
  exact h.trans (congrArg (fun t => t.reindex τ) (T.apply_symm_apply (generic (equivalences a b))))

end GenericClassifier

abbrev codes := smallFamilyCodes.{u}
abbrev pairs : Context.{u+1} := total (family codes.{u})
def first : pairs.{u} ⟶ codes := projection (family codes)
def second : pairs.{u} ⟶ codes := code (generic (family codes))

def classifyPair {Γ : Context.{u+1}} (a b : Γ ⟶ codes) : Γ ⟶ pairs :=
  pair a (term b)

@[simp] theorem classifyPair_first {Γ : Context.{u+1}} (a b : Γ ⟶ codes) :
    classifyPair a b ≫ first = a := rfl
@[simp] theorem classifyPair_second {Γ : Context.{u+1}} (a b : Γ ⟶ codes) :
    classifyPair a b ≫ second = b := rfl
@[simp] theorem classifyPair_comp {Γ Δ : Context.{u+1}} (a b : Γ ⟶ codes) (σ : Δ ⟶ Γ) :
    σ ≫ classifyPair a b = classifyPair (σ ≫ a) (σ ≫ b) := rfl

abbrev equivalenceContext : Context.{u+1} := total (equivalences first.{u} second)
def sourceCode : equivalenceContext.{u} ⟶ codes := projection (equivalences first second) ≫ first
def targetCode : equivalenceContext.{u} ⟶ codes := projection (equivalences first second) ≫ second

noncomputable def universalEquivalence :
    Σ f : liftedDecode sourceCode.{u} ⟶ liftedDecode targetCode, HomotopyEquivalence f :=
  genericEquivalence first second

noncomputable def classifyEquivalence {Γ : Context.{u+1}} (a b : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) : Γ ⟶ equivalenceContext :=
  pair (classifyPair a b)
    (EquivalenceFamilies.equivReindexSections (liftedDecode first) (liftedDecode second)
      (classifyPair a b) ⟨f,E⟩)

@[simp] theorem classifyEquivalence_source {Γ : Context.{u+1}} (a b : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) :
    classifyEquivalence a b f E ≫ sourceCode = a := rfl
@[simp] theorem classifyEquivalence_target {Γ : Context.{u+1}} (a b : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) :
    classifyEquivalence a b f E ≫ targetCode = b := rfl

theorem classifyEquivalence_comp {Γ Δ : Context.{u+1}} (a b : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    σ ≫ classifyEquivalence a b f E =
      classifyEquivalence (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ) := by
  have h := EquivalenceFamilies.equivReindexSections_comp (liftedDecode first) (liftedDecode second)
    (classifyPair a b) σ f E
  exact congrArg (pair (A := equivalences first second) (classifyPair (σ ≫ a) (σ ≫ b))) h.symm

/-- Classification recovers the map and its complete chosen contraction data. -/
theorem universalEquivalence_beta {Γ : Context.{u+1}} (a b : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) :
    (⟨Functor.whiskerLeft (classifyEquivalence a b f E).mapElements universalEquivalence.1,
      universalEquivalence.2.reindex (classifyEquivalence a b f E)⟩ :
        Σ g : liftedDecode a ⟶ liftedDecode b, HomotopyEquivalence g) = ⟨f,E⟩ :=
  genericEquivalence_beta first second (classifyPair a b) f E

/-- A full first equivalence, followed by an independently varying third code. -/
abbrev firstStage : Context.{u+1} := total (family equivalenceContext.{u})
def stageProjection : firstStage.{u} ⟶ equivalenceContext := projection (family equivalenceContext)
def stageSource : firstStage.{u} ⟶ codes := stageProjection ≫ sourceCode
def stageMiddle : firstStage.{u} ⟶ codes := stageProjection ≫ targetCode
def stageTarget : firstStage.{u} ⟶ codes := code (generic (family equivalenceContext))

noncomputable def classifyStage {Γ : Context.{u+1}} (a b c : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) : Γ ⟶ firstStage :=
  pair (classifyEquivalence a b f E) (term c)

theorem classifyStage_comp {Γ Δ : Context.{u+1}} (a b c : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    σ ≫ classifyStage a b c f E = classifyStage (σ ≫ a) (σ ≫ b) (σ ≫ c)
      (Functor.whiskerLeft σ.mapElements f) (E.reindex σ) := by
  exact congrArg (fun (k : Δ ⟶ equivalenceContext) => pair (A := family equivalenceContext) k (term (σ ≫ c)))
    (classifyEquivalence_comp a b f E σ)

abbrev compositionContext : Context.{u+1} := total (equivalences stageMiddle.{u} stageTarget)
def compositionProjection : compositionContext.{u} ⟶ firstStage :=
  projection (equivalences stageMiddle stageTarget)
def compositionSource : compositionContext.{u} ⟶ codes := compositionProjection ≫ stageSource
def compositionMiddle : compositionContext.{u} ⟶ codes := compositionProjection ≫ stageMiddle
def compositionTarget : compositionContext.{u} ⟶ codes := compositionProjection ≫ stageTarget

noncomputable def firstEquivalence :
    Σ f : liftedDecode compositionSource.{u} ⟶ liftedDecode compositionMiddle, HomotopyEquivalence f :=
  ⟨Functor.whiskerLeft (compositionProjection ≫ stageProjection).mapElements universalEquivalence.1,
    universalEquivalence.2.reindex (compositionProjection ≫ stageProjection)⟩

noncomputable def secondEquivalence :
    Σ g : liftedDecode compositionMiddle.{u} ⟶ liftedDecode compositionTarget, HomotopyEquivalence g :=
  genericEquivalence stageMiddle stageTarget

noncomputable def classifyComposition {Γ : Context.{u+1}} (a b c : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) : Γ ⟶ compositionContext :=
  classifyAlong stageMiddle stageTarget (classifyStage a b c f E) g D

theorem classifyComposition_comp {Γ Δ : Context.{u+1}} (a b c : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) (σ : Δ ⟶ Γ) :
    σ ≫ classifyComposition a b c f E g D =
      classifyComposition (σ ≫ a) (σ ≫ b) (σ ≫ c)
        (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
        (Functor.whiskerLeft σ.mapElements g) (D.reindex σ) := by
  unfold classifyComposition
  erw [classifyAlong_comp]
  congr 1
  exact classifyStage_comp a b c f E σ

theorem firstEquivalence_beta {Γ : Context.{u+1}} (a b c : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) :
    (⟨Functor.whiskerLeft (classifyComposition a b c f E g D).mapElements firstEquivalence.1,
      firstEquivalence.2.reindex (classifyComposition a b c f E g D)⟩ :
      Σ k : liftedDecode a ⟶ liftedDecode b, HomotopyEquivalence k) = ⟨f,E⟩ := by
  dsimp only [firstEquivalence]
  erw [HomotopyEquivalence.reindex_comp]
  exact universalEquivalence_beta a b f E

theorem secondEquivalence_beta {Γ : Context.{u+1}} (a b c : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) :
    (⟨Functor.whiskerLeft (classifyComposition a b c f E g D).mapElements secondEquivalence.1,
      secondEquivalence.2.reindex (classifyComposition a b c f E g D)⟩ :
      Σ k : liftedDecode b ⟶ liftedDecode c, HomotopyEquivalence k) = ⟨g,D⟩ :=
  genericEquivalence_beta stageMiddle stageTarget (classifyStage a b c f E) g D

end SquareKit.Cubical.Presheaf.SmallUniverse.UnivalenceLawParameters
