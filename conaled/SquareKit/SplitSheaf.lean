import SquareKit.SplitPresheaf
import SquareKit.SheafSlice
import SquareKit.FamilyCoherence

/-! Experimental split sheaf families and semantic comprehension. Substitution
is strict on section-indexed functors; gluing is required of their total space.
This interface does not define rule-restricted source syntax. -/
noncomputable section
namespace SquareKit.SplitSheaf
open CategoryTheory Limits Opposite ElementFamilies
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ Δ Ξ Ω : Sheaf J (Type w)}

/-- Only families whose total presheaf is a sheaf are accepted. -/
@[ext] structure Ty (Γ : Sheaf J (Type w)) where
  family : SplitPresheaf.Ty Γ.obj
  isSheaf : Presheaf.IsSheaf J (SplitPresheaf.Ext family)

abbrev Ext (A : Ty Γ) : Sheaf J (Type w) := ⟨SplitPresheaf.Ext A.family, A.isSheaf⟩
abbrev p (A : Ty Γ) : Ext A ⟶ Γ := ⟨SplitPresheaf.p A.family⟩
abbrev Tm (A : Ty Γ) := SplitPresheaf.Tm A.family

/-- The reindexed total is isomorphic to an ordinary sheaf pullback, so its
sheaf certificate is constructed, not an assumption on substitution. -/
def subPresheafIso (A : Ty Γ) (σ : Δ ⟶ Γ) :
    SplitPresheaf.Ext (SplitPresheaf.tySub A.family σ.hom) ≅ (pullback (p A) σ).obj :=
  (SplitPresheaf.extension_pullback A.family σ.hom).isoPullback ≪≫
    ((IsPullback.of_hasPullback (p A) σ).map (sheafToPresheaf J (Type w))).isoPullback.symm

def tySub (A : Ty Γ) (σ : Δ ⟶ Γ) : Ty Δ where
  family := SplitPresheaf.tySub A.family σ.hom
  isSheaf := (Presheaf.isSheaf_of_iso_iff (J := J) (subPresheafIso A σ)).2 (pullback (p A) σ).property

@[simp] theorem tySub_id (A : Ty Γ) : tySub A (𝟙 Γ) = A := rfl
@[simp] theorem tySub_comp (A : Ty Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) :
    tySub (tySub A σ) τ = tySub A (τ ≫ σ) := rfl

def tmSub {A : Ty Γ} (t : Tm A) (σ : Δ ⟶ Γ) : Tm (tySub A σ) := SplitPresheaf.tmSub t σ.hom
@[simp] theorem tmSub_id {A : Ty Γ} (t : Tm A) : tmSub t (𝟙 Γ) = t := rfl
@[simp] theorem tmSub_comp {A : Ty Γ} (t : Tm A) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) :
    tmSub (tmSub t σ) τ = tmSub t (τ ≫ σ) := rfl

def transport {A B : Ty Γ} (h : A = B) (t : Tm A) : Tm B := h ▸ t
@[simp] theorem transport_rfl {A : Ty Γ} (t : Tm A) : transport rfl t = t := rfl
theorem transport_trans {A B D : Ty Γ} (h : A = B) (k : B = D) (t : Tm A) :
    transport k (transport h t) = transport (h.trans k) t := by cases h; cases k; rfl

abbrev q (A : Ty Γ) : Tm (tySub A (p A)) := SplitPresheaf.q A.family
def pair (A : Ty Γ) (σ : Δ ⟶ Γ) (t : Tm (tySub A σ)) : Δ ⟶ Ext A := ⟨SplitPresheaf.pair A.family σ.hom t⟩
def lift (A : Ty Γ) (σ : Δ ⟶ Γ) : Ext (tySub A σ) ⟶ Ext A := ⟨SplitPresheaf.lift A.family σ.hom⟩

@[simp] theorem pair_p (A : Ty Γ) (σ : Δ ⟶ Γ) (t : Tm (tySub A σ)) : pair A σ t ≫ p A = σ := rfl
@[simp] theorem pair_q (A : Ty Γ) (σ : Δ ⟶ Γ) (t : Tm (tySub A σ)) : tmSub (q A) (pair A σ t) = t := rfl
theorem pair_eta (A : Ty Γ) (k : Δ ⟶ Ext A) : pair A (k ≫ p A) (tmSub (q A) k) = k := rfl
theorem pair_natural (A : Ty Γ) (σ : Δ ⟶ Γ) (t : Tm (tySub A σ)) (τ : Ξ ⟶ Δ) :
    pair A (τ ≫ σ) (tmSub t τ) = τ ≫ pair A σ t := rfl
@[simp] theorem lift_p (A : Ty Γ) (σ : Δ ⟶ Γ) : lift A σ ≫ p A = p (tySub A σ) ≫ σ := rfl
@[simp] theorem lift_id (A : Ty Γ) : lift A (𝟙 Γ) = 𝟙 (Ext A) := rfl
@[simp] theorem lift_comp (A : Ty Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) :
    lift (tySub A σ) τ ≫ lift A σ = lift A (τ ≫ σ) := rfl

theorem tmSub_triple {A : Ty Γ} (t : Tm A) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) (υ : Ω ⟶ Ξ) :
    tmSub (tmSub (tmSub t σ) τ) υ = tmSub t (υ ≫ (τ ≫ σ)) := rfl

theorem extension_pullback (A : Ty Γ) (σ : Δ ⟶ Γ) :
    IsPullback (lift A σ) (p (tySub A σ)) (p A) σ :=
  IsPullback.of_map (sheafToPresheaf J (Type w)) rfl (SplitPresheaf.extension_pullback A.family σ.hom)

def substitutionIso (A : Ty Γ) (σ : Δ ⟶ Γ) : Ext (tySub A σ) ≅ pullback (p A) σ :=
  (extension_pullback A σ).isoPullback
@[simp, reassoc] theorem substitution_value (A : Ty Γ) (σ : Δ ⟶ Γ) :
    (substitutionIso A σ).hom ≫ Family.comparison (p A) σ = lift A σ :=
  (extension_pullback A σ).isoPullback_hom_fst
@[simp, reassoc] theorem substitution_display (A : Ty Γ) (σ : Δ ⟶ Γ) :
    (substitutionIso A σ).hom ≫ Family.reindex (p A) σ = p (tySub A σ) :=
  (extension_pullback A σ).isoPullback_hom_snd

/-- Read a dependent term from any map satisfying its display equation. -/
def readTerm (A : Ty Γ) {σ : Δ ⟶ Γ} (k : Δ ⟶ Ext A) (h : k ≫ p A = σ) : Tm (tySub A σ) :=
  transport (congrArg (tySub A) h) (tmSub (q A) k)

theorem pair_read (A : Ty Γ) {σ : Δ ⟶ Γ} (k : Δ ⟶ Ext A) (h : k ≫ p A = σ) :
    pair A σ (readTerm A k h) = k := by cases h; rfl

def terms (A : Ty Γ) : Tm A ≃ Family.Term (p A) where
  toFun t := ⟨pair A (𝟙 Γ) t, rfl⟩
  invFun t := readTerm A t.val t.property
  left_inv _t := rfl
  right_inv t := Subtype.ext (pair_read A t.val t.property)

theorem term_substitution (A : Ty Γ) (σ : Δ ⟶ Γ) (t : Tm A) :
    (terms (tySub A σ) (tmSub t σ)).val ≫ (substitutionIso A σ).hom =
      (Family.termSub (p A) σ (terms A t)).val := by
  apply pullback.hom_ext <;> simp [Category.assoc, terms, Family.termSub, Family.pair]
  all_goals rfl

theorem variable_comparison (A : Ty Γ) :
    (terms (tySub A (p A)) (q A)).val ≫ (substitutionIso A (p A)).hom =
      (Family.variableTerm (p A)).val := by
  apply pullback.hom_ext <;> simp [Category.assoc, terms, Family.variableTerm, Family.pair]
  all_goals rfl

theorem pairing_comparison (A : Ty Γ) (σ : Δ ⟶ Γ) (t : Tm (tySub A σ)) :
    (terms (tySub A σ) t).val ≫ (substitutionIso A σ).hom =
      Family.pair (p A) σ (pair A σ t) (𝟙 Δ) (by simp) := by
  apply pullback.hom_ext <;> simp [Category.assoc, terms, Family.pair]
  all_goals rfl

/-- Identity and composition comparisons are those of the existing Family API. -/
theorem substitution_identity (A : Ty Γ) :
    (substitutionIso A (𝟙 Γ)).hom ≫ (Family.identityIso (p A)).hom = 𝟙 (Ext A) := by
  change (substitutionIso A (𝟙 Γ)).hom ≫ Family.comparison (p A) (𝟙 Γ) = _
  rw [substitution_value, lift_id]

theorem substitution_composition (A : Ty Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) :
    (substitutionIso (tySub A σ) τ).hom ≫
      Family.map (p (tySub A σ)) (Family.reindex (p A) σ) τ
        (substitutionIso A σ).hom (substitution_display A σ) ≫
      (Family.compositionIso (p A) σ τ).hom = (substitutionIso A (τ ≫ σ)).hom := by
  apply pullback.hom_ext <;> simp only [Category.assoc, Family.compositionIso_comparison,
    Family.compositionIso_display, Family.map_comparison_assoc, Family.map_display, substitution_value]
  · rw [← Category.assoc, substitution_value, lift_comp]
    exact (substitution_value A (τ ≫ σ)).symm
  · exact (substitution_display (tySub A σ) τ).trans (substitution_display A (τ ≫ σ)).symm

/-- Arbitrary ordinary displays give split families by their actual fibers. -/
def ofDisplay {B : Sheaf J (Type w)} (d : B ⟶ Γ) : Ty Γ where
  family := ElementFamilies.fibers Γ.obj (SheafSlice.underlying Γ (Over.mk d))
  isSheaf := (SheafSlice.totalSheaf Γ ((SheafSlice.forward Γ).obj (Over.mk d))).property

/-- This is the reconstruction from the actual element-site sheaf equivalence. -/
def displayIso {B : Sheaf J (Type w)} (d : B ⟶ Γ) : Ext (ofDisplay d) ≅ B :=
  (Over.forget Γ).mapIso (SheafSlice.reconstruction Γ (Over.mk d))

theorem displayIso_projection {B : Sheaf J (Type w)} (d : B ⟶ Γ) :
    (displayIso d).hom ≫ d = p (ofDisplay d) := SheafSlice.reconstruction_display Γ (Over.mk d)

/-- Conversely, every accepted split family supplies an element-site sheaf. -/
def elementSheaf (A : Ty Γ) : SheafSlice.ElementSheaves Γ :=
  ⟨ElementSheaf.presheaf Γ.obj A.family,
    (Presheaf.isSheaf_of_iso_iff
      (Functor.isoWhiskerLeft (opOpEquivalence Γ.obj.Elements).functor
        (ElementFamilies.fiberTotalIso Γ.obj A.family))).1
      ((SheafSlice.forward Γ).obj (Over.mk (p A))).property⟩

end SquareKit.SplitSheaf
