import SquareKit.Internal.PathTransport.SectionDescent

/-! Section descent and vertical recovery for total equivalences whose base
comparison is a natural isomorphism. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.SectionDescent.Normalized
open CategoryTheory CategoryTheory.Functor ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v' w z
variable {Γ : Type u} [Category.{v} Γ] {Δ : Type u'} [Category.{v'} Δ]
variable {A : Γ ⥤ Grpd.{z,w}} {B : Δ ⥤ Grpd.{z,w}}
variable (e : Γ ≌ Δ) (E : Extend A ≌ Extend B)
variable (α : E.functor ⋙ weaken B ≅ weaken A ⋙ e.functor)

def totalEquivalence : Extend A ≌ Extend B := by
  let : (normalize E.functor α).IsEquivalence :=
    Functor.isEquivalence_of_iso (normalizeComparison E.functor α).symm
  exact (normalize E.functor α).asEquivalence

theorem totalEquivalence_projection :
    (totalEquivalence e E α).functor ⋙ weaken B = weaken A ⋙ e.functor :=
  normalize_over E.functor α

def totalComparison : (totalEquivalence e E α).functor ≅ E.functor :=
  normalizeComparison E.functor α

/-- A strict projection equation recovers the supplied total functor. -/
theorem totalEquivalence_of_eq
    (hE : E.functor ⋙ weaken B = weaken A ⋙ e.functor) :
    (totalEquivalence e E (eqToIso hE)).functor = E.functor :=
  normalize_eqToIso E.functor hE

@[simp] theorem totalEquivalence_map_base {x y : Extend A} (f : x ⟶ y) :
    ((totalEquivalence e E α).functor.map f).base = e.functor.map f.base :=
  normalize_map_base E.functor α f

variable (s : Section B)

def descended : Section A :=
  descend e (totalEquivalence e E α) (totalEquivalence_projection e E α) s

def recovered : (descended e E α s).lift ⋙ (totalEquivalence e E α).functor ≅
    e.functor ⋙ s.lift :=
  recovery e (totalEquivalence e E α) (totalEquivalence_projection e E α) s

theorem baseComparison_map_inv (γ : Γ) :
    e.functor.map ((baseComparison e (totalEquivalence e E α) (totalEquivalence_projection e E α) s).inv.app γ) =
      ((rawRecovery e (totalEquivalence e E α) s).inv.app γ).base := by
  simp [baseComparison, weaken, Grothendieck.forget]

/-- Recovery is vertical over the compared base context. -/
theorem recovered_base (γ : Γ) :
    ((recovered e E α s).hom.app γ).base = 𝟙 (e.functor.obj γ) := by
  simp only [recovered, SectionDescent.recovery, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, Functor.map_comp, Grothendieck.comp_base,
    totalEquivalence_map_base]
  simp only [eqToIso.hom, eqToHom_app, Grothendieck.base_eqToHom,
    eqToHom_refl]
  change (e.functor.map (𝟙 γ) ≫
    e.functor.map ((baseComparison e (totalEquivalence e E α) (totalEquivalence_projection e E α) s).inv.app γ)) ≫
    ((rawRecovery e (totalEquivalence e E α) s).hom.app γ).base = _
  rw [e.functor.map_id, Category.id_comp, baseComparison_map_inv]
  rw [← Grothendieck.comp_base]
  simp
  rfl

@[simp] theorem recovered_inv_base (γ : Γ) :
    ((recovered e E α s).inv.app γ).base = 𝟙 (e.functor.obj γ) := by
  have h := congrArg Grothendieck.Hom.base ((recovered e E α s).hom_inv_id_app γ)
  simp only [Grothendieck.comp_base, recovered_base, Grothendieck.id_base] at h
  change 𝟙 (e.functor.obj γ) ≫ ((recovered e E α s).inv.app γ).base =
    𝟙 (e.functor.obj γ) at h
  simpa only [Category.id_comp] using h

/-- Recovery also compares with the original, unnormalized total equivalence. -/
def recoveredOriginal : (descended e E α s).lift ⋙ E.functor ≅
    e.functor ⋙ s.lift :=
  isoWhiskerLeft (descended e E α s).lift (totalComparison e E α).symm ≪≫
    recovered e E α s

theorem recoveredOriginal_base (γ : Γ) :
    ((recoveredOriginal e E α s).hom.app γ).base =
      α.hom.app ((descended e E α s).lift.obj γ) := by
  change (((totalComparison e E α).inv.app ((descended e E α s).lift.obj γ)) ≫
    (recovered e E α s).hom.app γ).base = _
  rw [Grothendieck.comp_base, recovered_base]
  exact Category.comp_id _

variable (t : Section B)

/-- All natural transformations are transported, including their arrow
naturality; this equivalence does not discard selected transformations. -/
def transformationEquiv :
    ((descended e E α s).lift ⟶ (descended e E α t).lift) ≃
      (e.functor ⋙ s.lift ⟶ e.functor ⋙ t.lift) :=
  (GrothendieckEquivalence.identityEquiv
    ((whiskeringRight Γ (Extend A) (Extend B)).obj (totalEquivalence e E α).functor) _ _).trans
      (Iso.homCongr (recovered e E α s) (recovered e E α t))

@[simp] theorem transformationEquiv_base
    (η : (descended e E α s).lift ⟶ (descended e E α t).lift) (γ : Γ) :
    ((transformationEquiv e E α s t η).app γ).base = e.functor.map (η.app γ).base := by
  change ((recovered e E α s).inv.app γ ≫
    ((totalEquivalence e E α).functor.map (η.app γ) ≫
      (recovered e E α t).hom.app γ)).base = _
  simp only [Grothendieck.comp_base, recovered_inv_base, recovered_base,
    totalEquivalence_map_base]
  change 𝟙 (e.functor.obj γ) ≫ e.functor.map (η.app γ).base ≫
    𝟙 (e.functor.obj γ) = e.functor.map (η.app γ).base
  simp only [Category.id_comp]
  exact Category.comp_id (e.functor.map (η.app γ).base)

/-- Full faithfulness restricts to transformations vertical over the base. -/
def verticalTransformationEquiv :
    {η : (descended e E α s).lift ⟶ (descended e E α t).lift //
      ∀ γ, (η.app γ).base = 𝟙 γ} ≃
    {η : e.functor ⋙ s.lift ⟶ e.functor ⋙ t.lift //
      ∀ γ, (η.app γ).base = 𝟙 (e.functor.obj γ)} :=
  (transformationEquiv e E α s t).subtypeEquiv (by
    intro η
    simp only [transformationEquiv_base]
    constructor
    · intro h γ
      exact (congrArg e.functor.map (h γ)).trans (e.functor.map_id γ)
    · intro h γ
      apply e.functor.map_injective
      exact (h γ).trans (e.functor.map_id γ).symm)

/-- Descent preserves and reflects all selected vertical transformations. -/
def sectionVerticalEquiv :
    {η : (descended e E α s).lift ⟶ (descended e E α t).lift //
      ∀ γ, (η.app γ).base = 𝟙 γ} ≃
    {η : s.lift ⟶ t.lift // ∀ δ, (η.app δ).base = 𝟙 δ} :=
  (verticalTransformationEquiv e E α s t).trans (pullbackVerticalEquiv e s t).symm

end SquareKit.Internal.PathTransport.GroupoidModel.SectionDescent.Normalized
