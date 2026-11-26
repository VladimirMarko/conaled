import SquareKit.Internal.ClassifierDisplayComparison
import SquareKit.SplitSheafPi

/-! Selected sheaf dependent products in classified display sections.
Operations are transported through the proved term/section equivalence. This
does not assert agreement with an independently selected native constructor. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace SquareKit.ClassifierSheafPi
open CategoryTheory SplitSheaf CoherentFamilyClassification
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ Δ Ξ Ω : Sheaf J (Type (max u v))}

abbrev classify (A : Ty Γ) := (code Γ.obj.Elements (Type (max u v))).obj A.family

/-- Classification retains formation after substitution, including the result
family reindexed along the argument display map. -/
theorem pi_reindex (A : Ty Γ) (B : Ty (extension A)) (σ : Δ ⟶ Γ) :
    (reindex σ.hom.mapElements).obj (classify (SplitSheafPi.pi A B)) =
      classify (SplitSheafPi.pi (tySub A σ) (tySub B (lift A σ))) := by
  change classify (tySub (SplitSheafPi.pi A B) σ) = _
  exact congrArg classify (SplitSheafPi.substitution A B σ)

/-- The classified output has the same actual display pullback. -/
theorem display_pullback (A : Ty Γ) (B : Ty (extension A)) (σ : Δ ⟶ Γ) :
    IsPullback (SplitPresheaf.lift (SplitSheafPi.pi A B).family σ.hom)
      (SplitPresheaf.p (SplitPresheaf.tySub (SplitSheafPi.pi A B).family σ.hom))
      (ClassifierDisplayComparison.projection Γ.obj (classify (SplitSheafPi.pi A B))) σ.hom :=
  ClassifierDisplayComparison.extension_pullback (classify (SplitSheafPi.pi A B)) σ.hom

/-- A section of the actual classified display above a specified substitution. -/
abbrev Section (A : Ty Γ) (σ : Δ ⟶ Γ) :=
  {k : Δ.obj ⟶ ClassifierDisplayComparison.extension Γ.obj (classify A) //
    k ≫ ClassifierDisplayComparison.projection Γ.obj (classify A) = σ.hom}

/-- Comprehension derives recovery of all sections, including dependent values. -/
def sections (A : Ty Γ) (σ : Δ ⟶ Γ) : Tm (tySub A σ) ≃ Section A σ where
  toFun t := ⟨(ClassifierDisplayComparison.comprehension (classify A)).symm ⟨σ.hom, t⟩, rfl⟩
  invFun k := readTerm A (σ := σ) ⟨k.val⟩ (by apply ObjectProperty.hom_ext; exact k.property)
  left_inv _ := rfl
  right_inv k := by
    apply Subtype.ext
    exact congrArg (fun f : Δ ⟶ extension A => f.hom) (pair_read A ⟨k.val⟩
      (show (⟨k.val⟩ : Δ ⟶ extension A) ≫ p A = σ from by
        apply ObjectProperty.hom_ext; exact k.property))

def sub {A : Ty Γ} {σ : Δ ⟶ Γ} (t : Section A σ) (τ : Ξ ⟶ Δ) :
    Section A (τ ≫ σ) := ⟨τ.hom ≫ t.val, by rw [Category.assoc, t.property]; rfl⟩

@[simp] theorem sections_sub (A : Ty Γ) (σ : Δ ⟶ Γ)
    (t : Tm (tySub A σ)) (τ : Ξ ⟶ Δ) :
    sections A (τ ≫ σ) (tmSub t τ) = sub (sections A σ t) τ := rfl

@[simp] theorem sub_id {A : Ty Γ} {σ : Δ ⟶ Γ} (t : Section A σ) : sub t (𝟙 Δ) = t := rfl
theorem sub_comp {A : Ty Γ} {σ : Δ ⟶ Γ} (t : Section A σ)
    (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ) : sub (sub t τ) υ = sub t (υ ≫ τ) := rfl

/-- Every code morphism acts on sections; no invertibility is required. -/
def map {A B : Ty Γ} (f : classify A ⟶ classify B) {σ : Δ ⟶ Γ}
    (t : Section A σ) : Section B σ :=
  ⟨t.val ≫ ((ClassifierDisplayComparison.equivalence Γ.obj).functor.map f).left,
    by
      change t.val ≫ (((ClassifierDisplayComparison.equivalence Γ.obj).functor.map f).left ≫
        ClassifierDisplayComparison.projection Γ.obj (classify B)) = σ.hom
      erw [ClassifierDisplayComparison.map_projection, t.property]⟩

@[simp] theorem map_id {A : Ty Γ} {σ : Δ ⟶ Γ} (t : Section A σ) : map (𝟙 _) t = t := by
  apply Subtype.ext
  simp only [map]
  rfl

theorem map_comp {A B D : Ty Γ} (f : classify A ⟶ classify B)
    (g : classify B ⟶ classify D) {σ : Δ ⟶ Γ} (t : Section A σ) :
    map g (map f t) = map (f ≫ g) t := by
  apply Subtype.ext
  simp only [map, Functor.map_comp]
  rfl

theorem map_sub {A B : Ty Γ} (f : classify A ⟶ classify B)
    {σ : Δ ⟶ Γ} (t : Section A σ) (τ : Ξ ⟶ Δ) :
    map f (sub t τ) = sub (map f t) τ := rfl

/-- Lambda at an arbitrary base substitution, with the result display fixed. -/
def lam (A : Ty Γ) (B : Ty (extension A)) (σ : Δ ⟶ Γ)
    (t : Section B (lift A σ)) : Section (SplitSheafPi.pi A B) σ :=
  sections _ σ (SplitSheafPi.lamAt A B σ ((sections B (lift A σ)).symm t))

def unlam (A : Ty Γ) (B : Ty (extension A)) (σ : Δ ⟶ Γ)
    (t : Section (SplitSheafPi.pi A B) σ) : Section B (lift A σ) :=
  sections B _ (SplitSheafPi.unlamAt A B σ ((sections _ σ).symm t))

@[simp] theorem beta (A : Ty Γ) (B : Ty (extension A)) (σ : Δ ⟶ Γ)
    (t : Section B (lift A σ)) : unlam A B σ (lam A B σ t) = t := by
  simp [lam, unlam]

@[simp] theorem eta (A : Ty Γ) (B : Ty (extension A)) (σ : Δ ⟶ Γ)
    (t : Section (SplitSheafPi.pi A B) σ) : lam A B σ (unlam A B σ t) = t := by
  simp [lam, unlam]

theorem lam_sections (A : Ty Γ) (B : Ty (extension A)) (σ : Δ ⟶ Γ)
    (t : Tm (tySub B (lift A σ))) :
    lam A B σ (sections B _ t) = sections _ σ (SplitSheafPi.lamAt A B σ t) := by
  simp [lam]

theorem lam_sub (A : Ty Γ) (B : Ty (extension A)) (σ : Δ ⟶ Γ)
    (t : Section B (lift A σ)) (τ : Ξ ⟶ Δ) :
    lam A B (τ ≫ σ) (sub t (lift (tySub A σ) τ)) = sub (lam A B σ t) τ := by
  obtain ⟨s, rfl⟩ := (sections B (lift A σ)).surjective t
  change lam A B (τ ≫ σ) (sections B _ (tmSub s (lift (tySub A σ) τ))) = _
  erw [lam_sections, lam_sections, ← sections_sub, SplitSheafPi.lamAt_natural]

theorem lam_sub_twice (A : Ty Γ) (B : Ty (extension A)) (σ : Δ ⟶ Γ)
    (t : Section B (lift A σ)) (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ) :
    lam A B (υ ≫ τ ≫ σ)
      (sub (sub t (lift (tySub A σ) τ)) (lift (tySub A (τ ≫ σ)) υ)) =
    sub (sub (lam A B σ t) τ) υ := by
  erw [lam_sub, lam_sub]

/-- Application lands above the actual argument pairing, retaining dependence. -/
def app (A : Ty Γ) (B : Ty (extension A)) (σ : Δ ⟶ Γ)
    (t : Section (SplitSheafPi.pi A B) σ) (a : Tm (tySub A σ)) :
    Section B (pair A σ a) :=
  sub (unlam A B σ t) (pair (tySub A σ) (𝟙 Δ) a)

@[simp] theorem app_beta (A : Ty Γ) (B : Ty (extension A)) (σ : Δ ⟶ Γ)
    (t : Section B (lift A σ)) (a : Tm (tySub A σ)) :
    app A B σ (lam A B σ t) a = sub t (pair (tySub A σ) (𝟙 Δ) a) := by
  unfold app
  rw [beta]

/-- The classified application recovers the existing dependent application. -/
theorem app_sections (A : Ty Γ) (B : Ty (extension A)) (σ : Δ ⟶ Γ)
    (t : Tm (tySub (SplitSheafPi.pi A B) σ)) (a : Tm (tySub A σ)) :
    app A B σ (sections _ σ t) a = sections B (pair A σ a)
      (SplitSheafPi.app (tySub A σ) (B := tySub B (lift A σ))
        (transport (SplitSheafPi.substitution A B σ) t) a) := by
  simp only [app, unlam, Equiv.symm_apply_apply]
  rfl

theorem unlam_sub (A : Ty Γ) (B : Ty (extension A)) (σ : Δ ⟶ Γ)
    (t : Section (SplitSheafPi.pi A B) σ) (τ : Ξ ⟶ Δ) :
    unlam A B (τ ≫ σ) (sub t τ) = sub (unlam A B σ t) (lift (tySub A σ) τ) := by
  have h := congrArg (unlam A B (τ ≫ σ)) (lam_sub A B σ (unlam A B σ t) τ)
  simp only [eta] at h
  exact h.symm.trans (beta A B (τ ≫ σ) _)

theorem app_sub (A : Ty Γ) (B : Ty (extension A)) (σ : Δ ⟶ Γ)
    (t : Section (SplitSheafPi.pi A B) σ) (a : Tm (tySub A σ)) (τ : Ξ ⟶ Δ) :
    app A B (τ ≫ σ) (sub t τ) (tmSub a τ) = sub (app A B σ t a) τ := by
  unfold app
  rw [unlam_sub]
  rfl

theorem app_sub_twice (A : Ty Γ) (B : Ty (extension A)) (σ : Δ ⟶ Γ)
    (t : Section (SplitSheafPi.pi A B) σ) (a : Tm (tySub A σ))
    (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ) :
    app A B (υ ≫ τ ≫ σ) (sub (sub t τ) υ) (tmSub (tmSub a τ) υ) =
      sub (sub (app A B σ t a) τ) υ := by
  erw [app_sub, app_sub]
  rfl

end SquareKit.ClassifierSheafPi
