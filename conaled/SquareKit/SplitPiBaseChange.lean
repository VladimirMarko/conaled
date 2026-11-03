import SquareKit.SplitPiComparison

/-! Experimental comparison of strict Π substitution with canonical base change. -/
noncomputable section
namespace SquareKit.SplitSheafPi
open CategoryTheory Limits SplitSheaf
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ Δ Ξ : Sheaf J (Type (max u v))}

/-- Existing split/display adapter, regarded in the ordinary slice. -/
def displaySubIso (A : Ty Γ) (σ : Δ ⟶ Γ) :
    Over.mk (p (tySub A σ)) ≅ (Over.pullback σ).obj (Over.mk (p A)) :=
  Over.isoMk (substitutionIso A σ) (substitution_display A σ)

def typeIso {A B : Ty Γ} (h : A = B) : Over.mk (p A) ≅ Over.mk (p B) :=
  eqToIso (congrArg (fun A => Over.mk (p A)) h)

/-- This is built from the equality-level formation law, not from Beck–Chevalley. -/
def splitBaseChange (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) :
    (Over.pullback σ).obj (Over.mk (p (pi A B))) ≅
      Over.mk (p (pi (tySub A σ) (tySub B (lift A σ)))) :=
  (displaySubIso (pi A B) σ).symm ≪≫ typeIso (substitution A B σ)

/-- The actual square to which ordinary Beck–Chevalley applies. -/
abbrev square (A : Ty Γ) (σ : Δ ⟶ Γ) := (extension_pullback A σ).flip

/-- The canonical mate, with only the already constructed display adapters. -/
def canonicalBaseChange (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) :
    (Over.pullback σ).obj (Over.mk (p (pi A B))) ≅
      Over.mk (p (pi (tySub A σ) (tySub B (lift A σ)))) :=
  (Over.pullback σ).mapIso (displayIso A B) ≪≫
    (SheafDependentProduct.baseChange (p A) (square A σ)).app (Over.mk (p B)) ≪≫
    (SheafDependentProduct.pi (p (tySub A σ))).mapIso (displaySubIso B (lift A σ)).symm ≪≫
    (displayIso (tySub A σ) (tySub B (lift A σ))).symm


theorem typeIso_terms {A B : Ty Γ} (h : A = B) :
    overTerms B (Over.mk (p A)) (typeIso h).hom =
      transport (congrArg (fun B => tySub B (p A)) h) (q A) := by cases h; rfl

theorem unlamAt_comp (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ)
    (t : Tm (tySub (pi A B) (τ ≫ σ))) :
    unlamAt (tySub A σ) (tySub B (lift A σ)) τ
      (transport (congrArg (fun T => tySub T τ) (substitution A B σ)) t) =
    unlamAt A B (τ ≫ σ) t := by
  unfold unlamAt
  erw [transport_trans]
  rfl

theorem inputTerms_uncurry (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ)
    (h : Over.mk σ ⟶ Over.mk (p (pi A B))) :
    inputTerms A B σ ((homEquiv A B (Over.mk σ)).symm h) =
      unlamAt A B σ (overTerms (pi A B) (Over.mk σ) h) :=
  (inputTerms A B σ).apply_symm_apply _

theorem typeIso_body (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) :
    inputTerms (tySub A σ) (tySub B (lift A σ)) (p (tySub (pi A B) σ))
      ((homEquiv (tySub A σ) (tySub B (lift A σ)) (Over.mk (p (tySub (pi A B) σ)))).symm
        (typeIso (substitution A B σ)).hom) =
    unlamAt A B (p (tySub (pi A B) σ) ≫ σ) (q (tySub (pi A B) σ)) := by
  rw [inputTerms_uncurry, typeIso_terms]
  exact unlamAt_comp A B σ _ _

theorem readTerm_lift (B : Ty Γ) (σ : Δ ⟶ Γ) {τ : Ξ ⟶ Δ}
    (k : Ξ ⟶ Ext (tySub B σ)) (h : k ≫ p (tySub B σ) = τ) :
    readTerm (tySub B σ) k h =
      readTerm B (σ := τ ≫ σ) (k ≫ lift B σ) (by rw [Category.assoc, lift_p, ← Category.assoc, h]) := by
  cases h
  rfl


@[simp, reassoc] theorem displaySub_value (A : Ty Γ) (σ : Δ ⟶ Γ) :
    (displaySubIso A σ).hom.left ≫ pullback.fst (p A) σ = lift A σ := substitution_value A σ
@[simp, reassoc] theorem displaySub_display (A : Ty Γ) (σ : Δ ⟶ Γ) :
    (displaySubIso A σ).hom.left ≫ pullback.snd (p A) σ = p (tySub A σ) := substitution_display A σ
@[simp, reassoc] theorem displaySub_inv_value (A : Ty Γ) (σ : Δ ⟶ Γ) :
    (displaySubIso A σ).inv.left ≫ lift A σ = pullback.fst (p A) σ := by
  change (substitutionIso A σ).inv ≫ lift A σ = _
  rw [Iso.inv_comp_eq]
  exact (substitution_value A σ).symm

def changedEvaluation (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) :
    (Over.pullback (p (tySub A σ))).obj (Over.mk (p (tySub (pi A B) σ))) ⟶
      Over.mk (p (tySub B (lift A σ))) :=
  (Over.pullback (p (tySub A σ))).map (displaySubIso (pi A B) σ).hom ≫
    (DependentBaseChange.pullbackComparison (square A σ)).app (Over.mk (p (pi A B))) ≫
    (Over.pullback (lift A σ)).map (evaluation A B) ≫ (displaySubIso B (lift A σ)).inv

@[reassoc] theorem pullbackMap_fst (f : Δ ⟶ Γ) {X Y : Over Γ} (k : X ⟶ Y) :
    ((Over.pullback f).map k).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ k.left :=
  pullback.lift_fst _ _ _
@[reassoc] theorem pullbackMap_snd (f : Δ ⟶ Γ) {X Y : Over Γ} (k : X ⟶ Y) :
    ((Over.pullback f).map k).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f :=
  pullback.lift_snd _ _ _

theorem argument_change (A S : Ty Γ) (σ : Δ ⟶ Γ) :
    (argumentIso (tySub A σ) (p (tySub S σ))).hom.left ≫
      ((Over.pullback (p (tySub A σ))).map (displaySubIso S σ).hom).left ≫
      ((DependentBaseChange.pullbackComparison (square A σ)).app (Over.mk (p S))).left ≫
      pullback.fst (Family.reindex (p S) (p A)) (lift A σ) =
    lift (tySub A (p S)) (lift S σ) ≫ (argumentIso A (p S)).hom.left := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    erw [DependentBaseChange.comparison_value (square A σ) (Over.mk (p S)),
      pullbackMap_fst_assoc (p (tySub A σ)) (displaySubIso S σ).hom,
      displaySub_value S σ, argument_fst_assoc, Category.assoc, argument_fst, lift_p]
    rfl
  · simp only [Category.assoc]
    erw [DependentBaseChange.comparison_argument (square A σ) (Over.mk (p S)),
      pullbackMap_snd_assoc (p (tySub A σ)) (displaySubIso S σ).hom,
      argument_snd_assoc, Category.assoc, argument_snd]
    rfl

theorem changedEvaluation_value (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) :
    (argumentIso (tySub A σ) (p (tySub (pi A B) σ))).hom.left ≫
      (changedEvaluation A B σ).left ≫ lift B (lift A σ) =
    lift (tySub A (p (pi A B))) (lift (pi A B) σ) ≫
      (argumentIso A (p (pi A B))).hom.left ≫ (evaluation A B).left := by
  change _ ≫ (_ ≫ _ ≫ _ ≫ _) ≫ _ = _
  simp only [Category.assoc, displaySub_inv_value]
  erw [pullbackMap_fst (lift A σ) (evaluation A B)]
  have h := congrArg (fun k => k ≫ (evaluation A B).left) (argument_change A (pi A B) σ)
  exact h


theorem changedEvaluation_body (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) :
    inputTerms (tySub A σ) (tySub B (lift A σ)) (p (tySub (pi A B) σ)) (changedEvaluation A B σ) =
      unlamAt A B (p (tySub (pi A B) σ) ≫ σ) (q (tySub (pi A B) σ)) := by
  rw [inputTerms_eq, readTerm_lift]
  have hm := changedEvaluation_value A B σ
  have hk : ((argumentIso A (p (pi A B))).hom.left ≫ (evaluation A B).left) ≫ p B =
      lift A (p (pi A B)) := by
    erw [Category.assoc, evaluation_display]
    exact argument_snd A _
  have hl : (lift (tySub A (p (pi A B))) (lift (pi A B) σ) ≫
      (argumentIso A (p (pi A B))).hom.left ≫ (evaluation A B).left) ≫ p B =
      lift (tySub A σ) (p (tySub (pi A B) σ)) ≫ lift A σ := by
    erw [Category.assoc, hk]
    rfl
  refine (readTerm_congr B hm _ hl).trans ?_
  have hs := readTerm_sub B ((argumentIso A (p (pi A B))).hom.left ≫ (evaluation A B).left) hk
    (lift (tySub A (p (pi A B))) (lift (pi A B) σ))
  refine hs.trans ?_
  have hb := inputTerms_uncurry A B (p (pi A B)) (𝟙 _)
  change inputTerms A B (p (pi A B)) (evaluation A B) = unlamAt A B (p (pi A B)) (q (pi A B)) at hb
  rw [inputTerms_eq] at hb
  exact (congrArg (fun t => tmSub t (lift (tySub A (p (pi A B))) (lift (pi A B) σ))) hb).trans
    (unlamAt_natural A B (p (pi A B)) (lift (pi A B) σ) (q (pi A B))).symm

/-- The equality-based split map has the expected base-changed transpose. -/
theorem split_transpose (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) :
    homEquiv (tySub A σ) (tySub B (lift A σ)) (Over.mk (p (tySub (pi A B) σ)))
      (changedEvaluation A B σ) = (typeIso (substitution A B σ)).hom := by
  apply (homEquiv (tySub A σ) (tySub B (lift A σ)) _).symm.injective
  rw [Equiv.symm_apply_apply]
  apply (inputTerms (tySub A σ) (tySub B (lift A σ)) _).injective
  rw [changedEvaluation_body, typeIso_body]


theorem canonical_transpose (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) :
    (displaySubIso (pi A B) σ).hom ≫ (canonicalBaseChange A B σ).hom =
      homEquiv (tySub A σ) (tySub B (lift A σ)) (Over.mk (p (tySub (pi A B) σ)))
        (changedEvaluation A B σ) := by
  apply (cancel_mono (displayIso (tySub A σ) (tySub B (lift A σ))).hom).mp
  simp only [canonicalBaseChange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [displayIso_curry]
  have hi := displayIso_apply A B (Over.mk (p (pi A B))) (𝟙 _)
  rw [Category.id_comp] at hi
  change (displayIso A B).hom = SheafDependentProduct.curry (p A) (evaluation A B) at hi
  rw [hi]
  have hb := SheafDependentProduct.baseChange_curry (p A) (square A σ)
    (Over.mk (p (pi A B))) (Over.mk (p B)) (evaluation A B)
  rw [← Category.assoc _ _ ((SheafDependentProduct.pi (p (tySub A σ))).map _)]
  erw [hb]
  have hn := SheafDependentProduct.family_natural (p (tySub A σ)) (displaySubIso B (lift A σ)).inv
    ((DependentBaseChange.pullbackComparison (square A σ)).app (Over.mk (p (pi A B))) ≫
      (Over.pullback (lift A σ)).map (evaluation A B))
  erw [← hn]
  exact (SheafDependentProduct.parameter_natural (p (tySub A σ)) (displaySubIso (pi A B) σ).hom
    ((DependentBaseChange.pullbackComparison (square A σ)).app (Over.mk (p (pi A B))) ≫
      (Over.pullback (lift A σ)).map (evaluation A B) ≫ (displaySubIso B (lift A σ)).inv)).symm

/-- Equality-level split substitution is the canonical Beck–Chevalley mate. -/
theorem baseChange_eq (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) :
    canonicalBaseChange A B σ = splitBaseChange A B σ := by
  apply Iso.ext
  apply (cancel_epi (displaySubIso (pi A B) σ).hom).mp
  rw [canonical_transpose, split_transpose]
  simp [splitBaseChange]


/-- The two-step adapter from the actual split total to ordinary iterated pullbacks. -/
def doubleSub (P : Ty Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) :
    Over.mk (p (tySub (tySub P σ) τ)) ≅ (Over.pullback τ).obj ((Over.pullback σ).obj (Over.mk (p P))) :=
  displaySubIso (tySub P σ) τ ≪≫ (Over.pullback τ).mapIso (displaySubIso P σ)

theorem transport_twice (P : Ty Γ) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ)
    {Q : Ty Δ} {R : Ty Ξ} (h : tySub P σ = Q) (k : tySub Q τ = R) :
    (doubleSub P σ τ).hom ≫
      (Over.pullback τ).map ((displaySubIso P σ).inv ≫ (typeIso h).hom) ≫
      (displaySubIso Q τ).inv ≫ (typeIso k).hom =
    (typeIso ((congrArg (fun Q => tySub Q τ) h).trans k)).hom := by
  cases h
  cases k
  change (doubleSub P σ τ).hom ≫ (Over.pullback τ).map ((displaySubIso P σ).inv ≫ 𝟙 _) ≫
    (displaySubIso (tySub P σ) τ).inv ≫ 𝟙 _ = 𝟙 _
  simp only [doubleSub, Iso.trans_hom, Functor.mapIso_hom, Category.comp_id, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, (Over.pullback τ).map_id, Category.id_comp]
  exact (displaySubIso (tySub P σ) τ).hom_inv_id

/-- Canonical base change obeys the identity coherence through the old adapter. -/
theorem baseChange_identity (A : Ty Γ) (B : Ty (Ext A)) :
    (displaySubIso (pi A B) (𝟙 Γ)).hom ≫ (canonicalBaseChange A B (𝟙 Γ)).hom = 𝟙 _ := by
  rw [baseChange_eq]
  change (displaySubIso (pi A B) (𝟙 Γ)).hom ≫ (displaySubIso (pi A B) (𝟙 Γ)).inv ≫ 𝟙 _ = 𝟙 _
  rw [Category.comp_id]
  exact (displaySubIso (pi A B) (𝟙 Γ)).hom_inv_id

/-- Both canonical mates compose to the direct equality transport, after the
existing ordinary pullback adapters. This is an equality of actual slice maps. -/
theorem baseChange_composition (A : Ty Γ) (B : Ty (Ext A)) (σ : Δ ⟶ Γ) (τ : Ξ ⟶ Δ) :
    (doubleSub (pi A B) σ τ).hom ≫ (Over.pullback τ).map (canonicalBaseChange A B σ).hom ≫
      (canonicalBaseChange (tySub A σ) (tySub B (lift A σ)) τ).hom =
    (displaySubIso (pi A B) (τ ≫ σ)).hom ≫ (canonicalBaseChange A B (τ ≫ σ)).hom := by
  rw [baseChange_eq, baseChange_eq, baseChange_eq]
  change (doubleSub (pi A B) σ τ).hom ≫
    (Over.pullback τ).map ((displaySubIso (pi A B) σ).inv ≫ (typeIso (substitution A B σ)).hom) ≫
    ((displaySubIso (pi (tySub A σ) (tySub B (lift A σ))) τ).inv ≫
      (typeIso (substitution (tySub A σ) (tySub B (lift A σ)) τ)).hom) = _
  refine (transport_twice (pi A B) σ τ (substitution A B σ)
    (substitution (tySub A σ) (tySub B (lift A σ)) τ)).trans ?_
  simp only [splitBaseChange, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  rfl

end SquareKit.SplitSheafPi
