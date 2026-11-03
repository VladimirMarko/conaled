import SquareKit.SheafDependentProduct
import Examples.SheafSliceFunctions

/-! Experimental dependent product over the false point of the Boolean sheaf.
An explicit representing display computes the fibers of the constructed
adjunction: Boolean values at false, and a single empty-index value at true. -/
noncomputable section
namespace Examples.FalsePointProduct
open CategoryTheory Limits Opposite SquareKit
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
open Examples.SheafFamilies

/-- Constant data is a sheaf on the connected diamond covers. -/
theorem constant_isSheaf (T : Type) : Presieve.IsSheaf topology ((Functor.const Diamondᵒᵖ).obj T) := by
  intro M S hS x hx
  have hw := hS W (fromW M) (by decide)
  refine ⟨(show T from @x W (fromW M) hw), ?_, ?_⟩
  · intro N f hf
    exact hx (𝟙 W) (fromW N) hw hf ((inferInstance : Subsingleton (Arrow W M)).elim _ _)
  · intro t ht
    exact ht (fromW M) hw

abbrev options : Sheaf topology Type :=
  ⟨(Functor.const Diamondᵒᵖ).obj (Option Bool), (isSheaf_iff_isSheaf_of_type _ _).2 (constant_isSheaf _)⟩

def optionBase : Option Bool → Bool | none => true | some _ => false
def optionDisplay : options ⟶ D := ⟨{ app _ := ↾optionBase }⟩
abbrev expected : Over D := Over.mk optionDisplay
abbrev input : Over SheafImage.terminal := Over.mk base
abbrev actual := (SheafDependentProduct.pi falsePoint).obj input

/-- The canonical section of the actual pullback, given an index over false. -/
def liftFalse (Z : Over D) (M : Diamondᵒᵖ) (z : Z.left.obj.obj M) (h : Z.hom.hom.app M z = false) :
    ((Over.pullback falsePoint).obj Z).left.obj.obj M :=
  (SheafFamily.sectionsEquiv Z.hom falsePoint M).symm ⟨(z,()),h⟩

@[simp] theorem liftFalse_fst (Z : Over D) (M : Diamondᵒᵖ) (z : Z.left.obj.obj M) (h) :
    (Family.comparison Z.hom falsePoint).hom.app M (liftFalse Z M z h) = z := by
  have e := SheafFamily.sectionsEquiv_fst Z.hom falsePoint M (liftFalse Z M z h)
  simpa only [liftFalse, Equiv.apply_symm_apply] using e.symm

/-- Actual pullback sections are determined by their parameter section, since
the index sheaf is terminal. -/
theorem pullback_ext (Z : Over D) (M : Diamondᵒᵖ)
    (a b : ((Over.pullback falsePoint).obj Z).left.obj.obj M)
    (h : (Family.comparison Z.hom falsePoint).hom.app M a =
      (Family.comparison Z.hom falsePoint).hom.app M b) : a = b := by
  apply (SheafFamily.sectionsEquiv Z.hom falsePoint M).injective
  apply Subtype.ext
  apply Prod.ext
  · exact (SheafFamily.sectionsEquiv_fst Z.hom falsePoint M a).trans
      (h.trans (SheafFamily.sectionsEquiv_fst Z.hom falsePoint M b).symm)
  · exact (inferInstance : Subsingleton Unit).elim _ _

theorem liftFalse_restrict (Z : Over D) {M N : Diamondᵒᵖ} (g : M ⟶ N)
    (z : Z.left.obj.obj M) (h : Z.hom.hom.app M z = false) :
    ((Over.pullback falsePoint).obj Z).left.obj.map g (liftFalse Z M z h) =
      liftFalse Z N (Z.left.obj.map g z) (by
        rw [NatTrans.naturality_apply, h]; rfl) := by
  apply pullback_ext
  have hn := NatTrans.naturality_apply (Family.comparison Z.hom falsePoint).hom g (liftFalse Z M z h)
  rw [liftFalse_fst] at hn
  exact hn.trans (liftFalse_fst Z N _ _).symm

/-- Explicit dependent curry into the candidate display. -/
def explicitValue {Z : Over D} (k : (Over.pullback falsePoint).obj Z ⟶ input)
    (M : Diamondᵒᵖ) (z : Z.left.obj.obj M) : Option Bool := by
  classical
  exact if h : Z.hom.hom.app M z = false then some (k.left.hom.app M (liftFalse Z M z h)) else none

theorem explicitValue_base {Z : Over D} (k : (Over.pullback falsePoint).obj Z ⟶ input)
    (M : Diamondᵒᵖ) (z : Z.left.obj.obj M) : optionBase (explicitValue k M z) = Z.hom.hom.app M z := by
  classical
  unfold explicitValue
  split_ifs with h
  · exact h.symm
  · cases hb : Z.hom.hom.app M z
    · exact (h hb).elim
    · rfl

def explicitCurry {Z : Over D} (k : (Over.pullback falsePoint).obj Z ⟶ input) : Z ⟶ expected :=
  Over.homMk ⟨{
    app M := ↾explicitValue k M
    naturality := by
      intro M N g
      apply ConcreteCategory.hom_ext
      intro z
      have hb := NatTrans.naturality_apply Z.hom.hom g z
      change Z.hom.hom.app N (Z.left.obj.map g z) = Z.hom.hom.app M z at hb
      classical
      change explicitValue k N (Z.left.obj.map g z) = explicitValue k M z
      unfold explicitValue
      split_ifs with hN hM hM
      · congr 1
        rw [← liftFalse_restrict]
        exact NatTrans.naturality_apply k.left.hom g _
      · exact (hM (hb.symm.trans hN)).elim
      · exact (hN (hb.trans hM)).elim
      · rfl }⟩ (by ext M z; exact explicitValue_base k M z)

/-- Evaluation reads a Boolean only where the false-point argument exists. -/
def explicitEvaluation : (Over.pullback falsePoint).obj expected ⟶ input :=
  Over.homMk ⟨{
    app M := ↾fun a => ((Family.comparison optionDisplay falsePoint).hom.app M a).getD false
    naturality := by
      intro M N g
      apply ConcreteCategory.hom_ext
      intro a
      have h := NatTrans.naturality_apply (Family.comparison optionDisplay falsePoint).hom g a
      exact congrArg (fun z : Option Bool => z.getD false) h }⟩ (by ext M z; rfl)

theorem index_false (Z : Over D) (M : Diamondᵒᵖ)
    (a : ((Over.pullback falsePoint).obj Z).left.obj.obj M) :
    Z.hom.hom.app M ((Family.comparison Z.hom falsePoint).hom.app M a) = false :=
  congrArg (fun k => k.hom.app M a) (pullback.condition (f := Z.hom) (g := falsePoint))

theorem map_value {Z Z' : Over D} (k : Z ⟶ Z') (M : Diamondᵒᵖ)
    (a : ((Over.pullback falsePoint).obj Z).left.obj.obj M) :
    (Family.comparison Z'.hom falsePoint).hom.app M
      (((Over.pullback falsePoint).map k).left.hom.app M a) =
        k.left.hom.app M ((Family.comparison Z.hom falsePoint).hom.app M a) := by
  have h : ((Over.pullback falsePoint).map k).left ≫ Family.comparison Z'.hom falsePoint =
      Family.comparison Z.hom falsePoint ≫ k.left := by simp [Over.pullback, Family.comparison]
  exact congrArg (fun n => n.hom.app M a) h

def explicitUncurry {Z : Over D} (k : Z ⟶ expected) : (Over.pullback falsePoint).obj Z ⟶ input :=
  (Over.pullback falsePoint).map k ≫ explicitEvaluation

theorem explicit_beta {Z : Over D} (k : (Over.pullback falsePoint).obj Z ⟶ input) :
    explicitUncurry (explicitCurry k) = k := by
  ext M a
  change ((Family.comparison optionDisplay falsePoint).hom.app M
    (((Over.pullback falsePoint).map (explicitCurry k)).left.hom.app M a)).getD false = _
  refine (congrArg (fun o : Option Bool => o.getD false) (map_value (explicitCurry k) M a)).trans ?_
  change (explicitValue k M ((Family.comparison Z.hom falsePoint).hom.app M a)).getD false = _
  rw [explicitValue, dite_eq_left (index_false Z M a)]
  change k.left.hom.app M (liftFalse Z M _ _) = k.left.hom.app M a
  congr 1
  apply pullback_ext
  exact liftFalse_fst Z M _ _

theorem explicit_eta {Z : Over D} (k : Z ⟶ expected) : explicitCurry (explicitUncurry k) = k := by
  ext M z
  change explicitValue (explicitUncurry k) M z = k.left.hom.app M z
  classical
  unfold explicitValue
  have hb := congrArg (fun n => n.hom.app M z) (Over.w k)
  change optionBase (k.left.hom.app M z) = Z.hom.hom.app M z at hb
  split_ifs with h
  · change some (((Family.comparison optionDisplay falsePoint).hom.app M
      (((Over.pullback falsePoint).map k).left.hom.app M (liftFalse Z M z h))).getD false) = _
    refine (congrArg (fun o : Option Bool => some (o.getD false)) (map_value k M (liftFalse Z M z h))).trans ?_
    rw [liftFalse_fst]
    cases hv : k.left.hom.app M z with
    | none => exact Bool.noConfusion ((hv ▸ hb).trans h)
    | some b => rfl
  · cases hv : k.left.hom.app M z with
    | none => rfl
    | some b => exact (h (hv ▸ hb).symm).elim

/-- Compare the constructed dependent product with the explicit representing display. -/
def comparison : expected ≅ actual where
  hom := SheafDependentProduct.curry falsePoint explicitEvaluation
  inv := explicitCurry (SheafDependentProduct.evaluation falsePoint input)
  hom_inv_id := by
    apply_fun explicitUncurry
    · change (Over.pullback falsePoint).map
        (SheafDependentProduct.curry falsePoint explicitEvaluation ≫
          explicitCurry (SheafDependentProduct.evaluation falsePoint input)) ≫ explicitEvaluation = _
      rw [Functor.map_comp, Category.assoc]
      change (Over.pullback falsePoint).map (SheafDependentProduct.curry falsePoint explicitEvaluation) ≫
        explicitUncurry (explicitCurry (SheafDependentProduct.evaluation falsePoint input)) = _
      rw [explicit_beta, ← SheafDependentProduct.uncurry_evaluation, SheafDependentProduct.beta]
      simp [explicitUncurry]
    · intro a b h
      have hh := congrArg explicitCurry h
      simpa only [explicit_eta] using hh
  inv_hom_id := by
    rw [← SheafDependentProduct.parameter_natural]
    change SheafDependentProduct.curry falsePoint
      (explicitUncurry (explicitCurry (SheafDependentProduct.evaluation falsePoint input))) = _
    rw [explicit_beta]
    change (SheafDependentProduct.adjunction falsePoint).homEquiv _ _
      ((SheafDependentProduct.adjunction falsePoint).counit.app input) = _
    rw [← Adjunction.homEquiv_symm_id]
    exact (SheafDependentProduct.homEquiv falsePoint actual input).apply_symm_apply _

abbrev Fiber (M : Diamond) (b : Bool) :=
  {a : actual.left.obj.obj (op M) // actual.hom.hom.app (op M) a = b}

/-- The comparison is over D, so it identifies actual fibers. -/
def fiberComparison (M : Diamond) (b : Bool) : {o : Option Bool // optionBase o = b} ≃ Fiber M b :=
  (((sheafToPresheaf _ _).mapIso ((SheafSlice.forward D).mapIso comparison)).app
    (op (ElementSite.point D.obj M b))).toEquiv

def falseFiberEquiv (M : Diamond) : Fiber M false ≃ Bool := (fiberComparison M false).symm.trans {
  toFun := fun o => o.val.getD false
  invFun := fun b => ⟨some b,rfl⟩
  left_inv := by
    rintro ⟨o,h⟩
    cases o with
    | none => exact Bool.noConfusion h
    | some b => rfl
  right_inv := fun _ => rfl }

def trueFiberEquiv (M : Diamond) : Fiber M true ≃ Unit := (fiberComparison M true).symm.trans {
  toFun := fun _ => ()
  invFun := fun _ => ⟨none,rfl⟩
  left_inv := by
    rintro ⟨o,h⟩
    cases o with
    | none => rfl
    | some b => exact Bool.noConfusion h
  right_inv := fun _ => rfl }

/-- Empty-index uniqueness: no argument at true is invented. -/
theorem true_unique (M : Diamond) (a b : Fiber M true) : a = b :=
  (trueFiberEquiv M).injective ((inferInstance : Subsingleton Unit).elim _ _)

/-- Actual evaluation agrees with the explicit representing display. -/
theorem comparison_evaluation :
    (Over.pullback falsePoint).map comparison.hom ≫ SheafDependentProduct.evaluation falsePoint input =
      explicitEvaluation := by
  change (Over.pullback falsePoint).map (SheafDependentProduct.curry falsePoint explicitEvaluation) ≫ _ = _
  rw [← SheafDependentProduct.uncurry_evaluation, SheafDependentProduct.beta]

/-- Evaluating at a genuine false argument reads the supplied Boolean. -/
theorem evaluate_false (M : Diamond) (b : Bool) :
    (SheafDependentProduct.evaluation falsePoint input).left.hom.app (op M)
      (((Over.pullback falsePoint).map comparison.hom).left.hom.app (op M)
        (liftFalse expected (op M) (some b) rfl)) = b := by
  have h := congrArg (fun k => k.left.hom.app (op M) (liftFalse expected (op M) (some b) rfl))
    comparison_evaluation
  change _ = ((Family.comparison optionDisplay falsePoint).hom.app (op M)
    (liftFalse expected (op M) (some b) rfl)).getD false at h
  exact h.trans (congrArg (fun o : Option Bool => o.getD false)
    (liftFalse_fst expected (op M) (some b) rfl))

end Examples.FalsePointProduct
