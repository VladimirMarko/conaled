import SquareKit.SplitSheafPi
import SquareKit.SheafDependentProduct

/-! Experimental comparison of split dependent functions with the constructed
ordinary dependent product. All pullbacks are the existing ordinary choices. -/
noncomputable section
namespace SquareKit.SplitSheafPi
open CategoryTheory Limits SplitSheaf
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ Δ Ξ : Sheaf J (Type (max u v))}

/-- Maps over a context are precisely the corresponding split terms. -/
def overTerms (A : Ty Γ) (X : Over Γ) : (X ⟶ Over.mk (p A)) ≃ Tm (tySub A X.hom) where
  toFun k := readTerm A k.left (Over.w k)
  invFun t := Over.homMk (pair A X.hom t) (pair_p A X.hom t)
  left_inv k := by apply Over.OverMorphism.ext; exact pair_read A k.left (Over.w k)
  right_inv t := rfl

theorem readTerm_sub (A : Ty Γ) {σ : Δ ⟶ Γ} (k : Δ ⟶ Ext A) (h : k ≫ p A = σ) (τ : Ξ ⟶ Δ) :
    readTerm A (σ := τ ≫ σ) (τ ≫ k) (by rw [Category.assoc, h]) = tmSub (readTerm A k h) τ := by
  cases h
  rfl

theorem readTerm_congr (A : Ty Γ) {σ : Δ ⟶ Γ} {k l : Δ ⟶ Ext A} (h : k = l)
    (hk : k ≫ p A = σ) (hl : l ≫ p A = σ) : readTerm A k hk = readTerm A l hl := by
  cases h
  rfl

/-- The split extension and the ordinary argument pullback are the same pullback. -/
def argumentIso (A : Ty Γ) (σ : Δ ⟶ Γ) :
    Over.mk (lift A σ) ≅ (Over.pullback (p A)).obj (Over.mk σ) :=
  Over.isoMk (extension_pullback A σ).flip.isoPullback
    (extension_pullback A σ).flip.isoPullback_hom_snd

@[simp, reassoc] theorem argument_fst (A : Ty Γ) (σ : Δ ⟶ Γ) :
    (argumentIso A σ).hom.left ≫ pullback.fst σ (p A) = p (tySub A σ) :=
  (extension_pullback A σ).flip.isoPullback_hom_fst
@[simp, reassoc] theorem argument_snd (A : Ty Γ) (σ : Δ ⟶ Γ) :
    (argumentIso A σ).hom.left ≫ pullback.snd σ (p A) = lift A σ :=
  (extension_pullback A σ).flip.isoPullback_hom_snd

def inputTerms (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) :
    ((Over.pullback (p A)).obj (Over.mk σ) ⟶ Over.mk (p B)) ≃ Tm (tySub B (lift A σ)) :=
  (Iso.homCongr (argumentIso A σ).symm (Iso.refl _)).trans (overTerms B (Over.mk (lift A σ)))

def transportEquiv {A B : Ty Γ} (h : A = B) : Tm A ≃ Tm B where
  toFun := transport h
  invFun := transport h.symm
  left_inv t := by cases h; rfl
  right_inv t := by cases h; rfl

/-- The constructed split Π represents the ordinary pullback Hom functor. -/
def homEquiv (A : Ty Γ) (B : Ty (Ext A)) (X : Over Γ) :
    ((Over.pullback (p A)).obj X ⟶ Over.mk (p B)) ≃ (X ⟶ Over.mk (p (pi A B))) :=
  (inputTerms A B X.hom).trans
    ((terms (tySub A X.hom) (tySub B (lift A X.hom))).trans
      ((transportEquiv (substitution A B X.hom).symm).trans (overTerms (pi A B) X).symm))


theorem homEquiv_left (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ)
    (k : (Over.pullback (p A)).obj (Over.mk σ) ⟶ Over.mk (p B)) :
    (homEquiv A B (Over.mk σ) k).left = pair (pi A B) σ (lamAt A B σ (inputTerms A B σ k)) := rfl

theorem argument_natural (A : Ty Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) :
    (argumentIso A (τ ≫ σ)).hom.left ≫
        ((Over.pullback (p A)).map (Over.homMk τ rfl : Over.mk (τ ≫ σ) ⟶ Over.mk σ)).left =
      lift (tySub A σ) τ ≫ (argumentIso A σ).hom.left := by
  apply pullback.hom_ext
  · change (_ ≫ pullback.lift _ _ _) ≫ pullback.fst σ (p A) = _
    erw [Category.assoc, pullback.lift_fst, argument_fst_assoc, Category.assoc, argument_fst, lift_p]
    rfl
  · change (_ ≫ pullback.lift _ _ _) ≫ pullback.snd σ (p A) = _
    erw [Category.assoc, pullback.lift_snd, argument_snd, Category.assoc, argument_snd, lift_comp]

theorem inputTerms_eq (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ)
    (k : (Over.pullback (p A)).obj (Over.mk σ) ⟶ Over.mk (p B)) :
    inputTerms A B σ k = readTerm B (σ := lift A σ) ((argumentIso A σ).hom.left ≫ k.left)
      (by erw [Category.assoc, Over.w k]; exact argument_snd A σ) := rfl

theorem inputTerms_natural (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ)
    (k : (Over.pullback (p A)).obj (Over.mk σ) ⟶ Over.mk (p B)) :
    inputTerms A B (τ ≫ σ) ((Over.pullback (p A)).map (Over.homMk τ rfl : Over.mk (τ ≫ σ) ⟶ Over.mk σ) ≫ k) =
      tmSub (inputTerms A B σ k) (lift (tySub A σ) τ) := by
  rw [inputTerms_eq, inputTerms_eq]
  have hm := congrArg (fun f => f ≫ k.left) (argument_natural A σ τ)
  simp only [Category.assoc] at hm
  have hl : (lift (tySub A σ) τ ≫ (argumentIso A σ).hom.left ≫ k.left) ≫ p B = lift A (τ ≫ σ) := by
    erw [Category.assoc, Category.assoc, Over.w k, argument_snd, lift_comp]
  exact (readTerm_congr B hm _ hl).trans (readTerm_sub B (σ := lift A σ)
    ((argumentIso A σ).hom.left ≫ k.left)
    (by erw [Category.assoc, Over.w k]; exact argument_snd A σ)
    (lift (tySub A σ) τ))

theorem homEquiv_natural_aux (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ)
    (k : (Over.pullback (p A)).obj (Over.mk σ) ⟶ Over.mk (p B)) :
    homEquiv A B (Over.mk (τ ≫ σ)) ((Over.pullback (p A)).map (Over.homMk τ rfl : Over.mk (τ ≫ σ) ⟶ Over.mk σ) ≫ k) =
      (Over.homMk τ rfl : Over.mk (τ ≫ σ) ⟶ Over.mk σ) ≫ homEquiv A B (Over.mk σ) k := by
  apply Over.OverMorphism.ext
  change pair (pi A B) (τ ≫ σ)
    (lamAt A B (τ ≫ σ) (inputTerms A B (τ ≫ σ) ((Over.pullback (p A)).map
      (Over.homMk τ rfl : Over.mk (τ ≫ σ) ⟶ Over.mk σ) ≫ k))) =
    τ ≫ pair (pi A B) σ (lamAt A B σ (inputTerms A B σ k))
  rw [inputTerms_natural, ← lamAt_natural]
  exact pair_natural _ _ _ _


theorem homEquiv_natural_mk (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) (σ' : Ξ ⟶ Γ)
    (τ : Ξ ⟶ Δ) (h : τ ≫ σ = σ')
    (k : (Over.pullback (p A)).obj (Over.mk σ) ⟶ Over.mk (p B)) :
    homEquiv A B (Over.mk σ') ((Over.pullback (p A)).map (Over.homMk τ h : Over.mk σ' ⟶ Over.mk σ) ≫ k) =
      (Over.homMk τ h : Over.mk σ' ⟶ Over.mk σ) ≫ homEquiv A B (Over.mk σ) k := by
  cases h
  exact homEquiv_natural_aux A B σ τ k

theorem homEquiv_natural (A : Ty Γ) (B : Ty (Ext A)) {X Y : Over Γ} (g : Y ⟶ X)
    (k : (Over.pullback (p A)).obj X ⟶ Over.mk (p B)) :
    homEquiv A B Y ((Over.pullback (p A)).map g ≫ k) = g ≫ homEquiv A B X k :=
  homEquiv_natural_mk A B X.hom Y.hom g.left (Over.w g) k

theorem homEquiv_symm_natural (A : Ty Γ) (B : Ty (Ext A)) {X Y : Over Γ} (g : Y ⟶ X)
    (k : X ⟶ Over.mk (p (pi A B))) :
    (homEquiv A B Y).symm (g ≫ k) = (Over.pullback (p A)).map g ≫ (homEquiv A B X).symm k := by
  apply (homEquiv A B Y).injective
  rw [Equiv.apply_symm_apply, homEquiv_natural, Equiv.apply_symm_apply]

/-- Representing-object comparison, natural in every parameter context. -/
def yonedaComparison (A : Ty Γ) (B : Ty (Ext A)) :
    yoneda.obj (Over.mk (p (pi A B))) ≅
      yoneda.obj ((SheafDependentProduct.pi (p A)).obj (Over.mk (p B))) :=
  NatIso.ofComponents (fun X => Equiv.toIso
    ((homEquiv A B X.unop).symm.trans (SheafDependentProduct.homEquiv (p A) X.unop (Over.mk (p B)))))
    (fun f => by
      apply ConcreteCategory.hom_ext
      intro k
      change SheafDependentProduct.curry (p A) ((homEquiv A B _).symm (f.unop ≫ k)) = _
      rw [homEquiv_symm_natural, SheafDependentProduct.parameter_natural]
      rfl)

def displayIso (A : Ty Γ) (B : Ty (Ext A)) :
    Over.mk (p (pi A B)) ≅ (SheafDependentProduct.pi (p A)).obj (Over.mk (p B)) :=
  Yoneda.fullyFaithful.preimageIso (yonedaComparison A B)


theorem displayIso_apply (A : Ty Γ) (B : Ty (Ext A)) (X : Over Γ)
    (h : X ⟶ Over.mk (p (pi A B))) :
    h ≫ (displayIso A B).hom =
      SheafDependentProduct.curry (p A) ((homEquiv A B X).symm h) := by
  exact congrArg (fun α => α.app (Opposite.op X) h)
    (Yoneda.fullyFaithful.map_preimage (yonedaComparison A B).hom)

/-- Transposition agrees with the previously constructed dependent product. -/
theorem displayIso_curry (A : Ty Γ) (B : Ty (Ext A)) (X : Over Γ)
    (k : (Over.pullback (p A)).obj X ⟶ Over.mk (p B)) :
    homEquiv A B X k ≫ (displayIso A B).hom = SheafDependentProduct.curry (p A) k := by
  rw [displayIso_apply, Equiv.symm_apply_apply]

def evaluation (A : Ty Γ) (B : Ty (Ext A)) :
    (Over.pullback (p A)).obj (Over.mk (p (pi A B))) ⟶ Over.mk (p B) :=
  (homEquiv A B _).symm (𝟙 _)

/-- The comparison identifies actual counits, including the display equation. -/
theorem displayIso_evaluation (A : Ty Γ) (B : Ty (Ext A)) :
    (Over.pullback (p A)).map (displayIso A B).hom ≫ SheafDependentProduct.evaluation (p A) (Over.mk (p B)) =
      evaluation A B := by
  rw [← SheafDependentProduct.uncurry_evaluation]
  have h := displayIso_apply A B (Over.mk (p (pi A B))) (𝟙 _)
  rw [Category.id_comp] at h
  rw [h, SheafDependentProduct.beta]
  rfl

theorem evaluation_display (A : Ty Γ) (B : Ty (Ext A)) :
    (evaluation A B).left ≫ p B = Family.reindex (p (pi A B)) (p A) := Over.w (evaluation A B)


theorem uncurry_evaluation (A : Ty Γ) (B : Ty (Ext A)) {X : Over Γ}
    (k : X ⟶ Over.mk (p (pi A B))) :
    (homEquiv A B X).symm k = (Over.pullback (p A)).map k ≫ evaluation A B := by
  simpa only [Category.comp_id, evaluation] using homEquiv_symm_natural A B k (𝟙 _)

/-- Every map of dependent displays induces a map of dependent function displays. -/
def mapResult (A : Ty Γ) {B B' : Ty (Ext A)} (k : Over.mk (p B) ⟶ Over.mk (p B')) :
    Over.mk (p (pi A B)) ⟶ Over.mk (p (pi A B')) :=
  homEquiv A B' _ (evaluation A B ≫ k)

theorem result_natural (A : Ty Γ) {B B' : Ty (Ext A)} (k : Over.mk (p B) ⟶ Over.mk (p B'))
    {X : Over Γ} (h : (Over.pullback (p A)).obj X ⟶ Over.mk (p B)) :
    homEquiv A B' X (h ≫ k) = homEquiv A B X h ≫ mapResult A k := by
  unfold mapResult
  rw [← homEquiv_natural, ← Category.assoc, ← uncurry_evaluation, Equiv.symm_apply_apply]

/-- The display comparison is natural in the genuinely dependent result. -/
theorem displayIso_result (A : Ty Γ) {B B' : Ty (Ext A)} (k : Over.mk (p B) ⟶ Over.mk (p B')) :
    mapResult A k ≫ (displayIso A B').hom =
      (displayIso A B).hom ≫ (SheafDependentProduct.pi (p A)).map k := by
  unfold mapResult
  rw [displayIso_curry, SheafDependentProduct.family_natural]
  have h := displayIso_curry A B (Over.mk (p (pi A B))) (evaluation A B)
  change (homEquiv A B _ ((homEquiv A B _).symm (𝟙 _))) ≫ _ = _ at h
  rw [Equiv.apply_symm_apply, Category.id_comp] at h
  rw [← h]

end SquareKit.SplitSheafPi
