import SquareKit.SmoothOpenCoordinates

/-! Experimental naturality of ordinary smooth operations and principal-open
restrictions under the fully faithful sheaf embedding. -/
noncomputable section
open scoped ContDiff
namespace SquareKit.EuclideanOpen
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite Localization

/-- Every globally smooth operation is an ordinary map, without restricting the general Hom type. -/
def operation {n : ℕ} (f : Operation n) : full n ⟶ full 1 :=
  {toFun x := ⟨fun _ => f.val x.val,one_ne_zero⟩
   smooth _ := (OpenFunctions.representative_iff _ f.val (fun _ => rfl)).mpr f.property.contDiffOn}

theorem operation_coordinate {n : ℕ} (f : Operation n) :
    Localization.pullback (operation f) (principalBase 1 (generator 0)) = principalBase 1 f := by
  apply (toOpen_bijective (1 : Free n)).injective
  apply OpenFunctions.ext
  intro x
  rw [Localization.pullback_apply,toOpen_base]
  exact (toOpen_base (1 : Free n) (show Free n from f) x).symm

/-- The ordinary operation embeds as the already constructed scalar operation. -/
theorem operation_comparison {n : ℕ} (f : Operation n) :
    embedding.map (operation f) ≫ fullLineIso.hom =
      (fullPowerIso n).hom ≫ SmoothOpenSite.operation f := by
  ext A a
  change smoothMap a.unop (Localization.pullback (operation f) (principalBase 1 (generator 0))) =
    act f (fun i => smoothMap a.unop (principalBase 1 (generator i)))
  rw [operation_coordinate]
  exact congrArg (fun h : Hom (Free n) (Carrier A.unop.unop) => h f)
    (evaluate_unique ((smoothMap a.unop).comp (principalBase 1))).symm

/-- The intersection inclusion uses the existing product-localization algebra map. -/
def nested {n : ℕ} (f g : Free n) : (⟨n,f*g⟩ : Domain) ⟶ (⟨n,f⟩ : Domain) :=
  {toFun x := ⟨x.val,locus_product_subset f g x.property⟩
   smooth i := (OpenFunctions.representative_iff _ (fun x => x i) (fun _ => rfl)).mpr
     (contDiff_apply ℝ (fun _ : Fin n => ℝ) i).contDiffOn}

theorem nested_pullback {n : ℕ} (f g : Free n) :
    Localization.pullback (nested f g) = nestedMap f g := by
  apply Hom.ext
  intro a
  apply (toOpen_bijective (f*g)).injective
  apply OpenFunctions.ext
  intro x
  rw [Localization.pullback_apply]
  exact (congrArg (fun h : Hom (Principal f) (Localization.Functions (f*g)) => (h a).val x)
    (restriction_naturality f g)).symm

end SquareKit.EuclideanOpen
