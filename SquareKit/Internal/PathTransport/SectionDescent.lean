import SquareKit.Internal.PathTransport.SectionNormalization
import SquareKit.GrothendieckEquivalence

/-! Transport sections along equivalences of contexts and their total families. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.SectionDescent
open CategoryTheory CategoryTheory.Functor ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v' w z
variable {Γ : Type u} [Category.{v} Γ] {Δ : Type u'} [Category.{v'} Δ]
variable {A : Γ ⥤ Grpd.{z,w}} {B : Δ ⥤ Grpd.{z,w}}
variable (e : Γ ≌ Δ) (E : Extend A ≌ Extend B)
variable (hE : E.functor ⋙ weaken B = weaken A ⋙ e.functor)
variable (s : Section B)

/-- Pull back the full section functor, retaining its arrow action. -/
def raw : Γ ⥤ Extend A := e.functor ⋙ s.lift ⋙ E.inverse

def rawRecovery : raw e E s ⋙ E.functor ≅ e.functor ⋙ s.lift :=
  isoWhiskerLeft (e.functor ⋙ s.lift) E.counitIso

/-- The total comparison determines the base comparison by full faithfulness. -/
def baseComparison : raw e E s ⋙ weaken A ≅ 𝟭 Γ :=
  fullyFaithfulCancelRight e.functor
    ((eqToIso (by
      change raw e E s ⋙ (weaken A ⋙ e.functor) = _
      rw [← hE]
      rfl)) ≪≫ isoWhiskerRight (rawRecovery e E s) (weaken B))

/-- A section is constructed from local section data and the supplied
comparisons; no global reconstructed section is an input. -/
def descend : Section A :=
  Section.ofOver (normalize (raw e E s) (baseComparison e E hE s))
    (normalize_over _ _)

/-- Recovery retains a natural isomorphism of the complete section functors. -/
def recovery : (descend e E hE s).lift ⋙ E.functor ≅ e.functor ⋙ s.lift :=
  isoWhiskerRight
    ((eqToIso (Section.ofOver_lift _ _)) ≪≫ normalizeComparison (raw e E s) (baseComparison e E hE s))
    E.functor ≪≫ rawRecovery e E s

section Fibers
variable (β : A ⟶ e.functor ⋙ B) [hβ : ∀ γ, (β.app γ).IsEquivalence]

/-- A base equivalence and equivalences in every fiber supply the required
context-extension equivalence. -/
def totalEquivalence : Extend A ≌ Extend B := by
  letI (γ : Γ) : ((whiskerRight β Grpd.forgetToCat).app γ).toFunctor.IsEquivalence :=
    inferInstanceAs (β.app γ).IsEquivalence
  exact GrothendieckEquivalence.extendEquivalence e (B ⋙ Grpd.forgetToCat)
    (whiskerRight β Grpd.forgetToCat)

theorem totalEquivalence_projection :
    (totalEquivalence e β).functor ⋙ weaken B = weaken A ⋙ e.functor := rfl

def descendFibers : Section A :=
  descend e (totalEquivalence e β) (totalEquivalence_projection e β) s

def recoverFibers : (descendFibers e s β).lift ⋙ (totalEquivalence e β).functor ≅
    e.functor ⋙ s.lift := recovery e (totalEquivalence e β) (totalEquivalence_projection e β) s

@[simp] theorem totalEquivalence_map_base {x y : Extend A} (f : x ⟶ y) :
    ((totalEquivalence e β).functor.map f).base = e.functor.map f.base := rfl

theorem baseComparison_map_inv (γ : Γ) :
    e.functor.map ((baseComparison e (totalEquivalence e β) (totalEquivalence_projection e β) s).inv.app γ) =
      ((rawRecovery e (totalEquivalence e β) s).inv.app γ).base := by
  simp [baseComparison, weaken, Grothendieck.forget]

/-- Recovery is vertical over the compared base context. -/
theorem recoverFibers_base (γ : Γ) :
    ((recoverFibers e s β).hom.app γ).base = 𝟙 (e.functor.obj γ) := by
  simp only [recoverFibers, recovery, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, Functor.map_comp, Grothendieck.comp_base,
    totalEquivalence_map_base]
  simp only [eqToIso.hom, eqToHom_app, Grothendieck.base_eqToHom,
    eqToHom_refl]
  change (e.functor.map (𝟙 γ) ≫
    e.functor.map ((baseComparison e (totalEquivalence e β) (totalEquivalence_projection e β) s).inv.app γ)) ≫
    ((rawRecovery e (totalEquivalence e β) s).hom.app γ).base = _
  rw [e.functor.map_id, Category.id_comp, baseComparison_map_inv]
  rw [← Grothendieck.comp_base]
  simp
  rfl

@[simp] theorem recoverFibers_inv_base (γ : Γ) :
    ((recoverFibers e s β).inv.app γ).base = 𝟙 (e.functor.obj γ) := by
  have h := congrArg Grothendieck.Hom.base ((recoverFibers e s β).hom_inv_id_app γ)
  simp only [Grothendieck.comp_base, recoverFibers_base, Grothendieck.id_base] at h
  change 𝟙 (e.functor.obj γ) ≫ ((recoverFibers e s β).inv.app γ).base =
    𝟙 (e.functor.obj γ) at h
  simpa only [Category.id_comp] using h

variable (t : Section B)

/-- All natural transformations are transported, including their arrow
naturality; this equivalence does not discard selected transformations. -/
def transformationEquiv :
    ((descendFibers e s β).lift ⟶ (descendFibers e t β).lift) ≃
      (e.functor ⋙ s.lift ⟶ e.functor ⋙ t.lift) :=
  (GrothendieckEquivalence.identityEquiv
    ((whiskeringRight Γ (Extend A) (Extend B)).obj (totalEquivalence e β).functor) _ _).trans
      (Iso.homCongr (recoverFibers e s β) (recoverFibers e t β))

@[simp] theorem transformationEquiv_base
    (η : (descendFibers e s β).lift ⟶ (descendFibers e t β).lift) (γ : Γ) :
    ((transformationEquiv e s β t η).app γ).base = e.functor.map (η.app γ).base := by
  change ((recoverFibers e s β).inv.app γ ≫
    ((totalEquivalence e β).functor.map (η.app γ) ≫
      (recoverFibers e t β).hom.app γ)).base = _
  simp only [Grothendieck.comp_base, recoverFibers_inv_base, recoverFibers_base,
    totalEquivalence_map_base]
  change 𝟙 (e.functor.obj γ) ≫ e.functor.map (η.app γ).base ≫
    𝟙 (e.functor.obj γ) = e.functor.map (η.app γ).base
  simp only [Category.id_comp]
  exact Category.comp_id (e.functor.map (η.app γ).base)

/-- Full faithfulness restricts to transformations vertical over the base. -/
def verticalTransformationEquiv :
    {η : (descendFibers e s β).lift ⟶ (descendFibers e t β).lift //
      ∀ γ, (η.app γ).base = 𝟙 γ} ≃
    {η : e.functor ⋙ s.lift ⟶ e.functor ⋙ t.lift //
      ∀ γ, (η.app γ).base = 𝟙 (e.functor.obj γ)} :=
  (transformationEquiv e s β t).subtypeEquiv (by
    intro η
    simp only [transformationEquiv_base]
    constructor
    · intro h γ
      exact (congrArg e.functor.map (h γ)).trans (e.functor.map_id γ)
    · intro h γ
      apply e.functor.map_injective
      exact (h γ).trans (e.functor.map_id γ).symm)

/-- Pullback along the base equivalence retains exactly the vertical natural
transformations of the supplied sections. -/
def pullbackVerticalEquiv :
    {η : s.lift ⟶ t.lift // ∀ δ, (η.app δ).base = 𝟙 δ} ≃
    {η : e.functor ⋙ s.lift ⟶ e.functor ⋙ t.lift //
      ∀ γ, (η.app γ).base = 𝟙 (e.functor.obj γ)} :=
  (GrothendieckEquivalence.identityEquiv
    ((whiskeringLeft Γ Δ (Extend B)).obj e.functor) s.lift t.lift).subtypeEquiv (by
    intro η
    constructor
    · intro h γ
      exact h (e.functor.obj γ)
    · intro h δ
      let ρ : 𝟭 Δ ⟶ 𝟭 Δ := whiskerRight η (weaken B)
      have hρ : whiskerLeft e.functor ρ = whiskerLeft e.functor (𝟙 (𝟭 Δ)) := by
        ext γ
        exact h γ
      have he : ρ = 𝟙 (𝟭 Δ) :=
        ((whiskeringLeft Γ Δ Δ).obj e.functor).map_injective hρ
      exact congrArg (fun τ => τ.app δ) he)

/-- Descent is fully faithful on selected vertical transformations between
complete sections, before or after restricting their base along the equivalence. -/
def sectionVerticalEquiv :
    {η : (descendFibers e s β).lift ⟶ (descendFibers e t β).lift //
      ∀ γ, (η.app γ).base = 𝟙 γ} ≃
    {η : s.lift ⟶ t.lift // ∀ δ, (η.app δ).base = 𝟙 δ} :=
  (verticalTransformationEquiv e s β t).trans (pullbackVerticalEquiv e s t).symm

end Fibers
end SquareKit.Internal.PathTransport.GroupoidModel.SectionDescent
