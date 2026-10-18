import SquareKit.SmoothOpenEmbedding

/-! Experimental coordinate comparisons for full Euclidean domains and principal
open inclusions, natural for actual ordinary smooth maps. -/
noncomputable section
open scoped ContDiff
namespace SquareKit.EuclideanOpen
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite
open Localization OpenFunctions

abbrev full (n : ℕ) : Domain := ⟨n,1⟩

/-- Full Euclidean coordinates include the zero-dimensional space. -/
def fullPoints (n : ℕ) : Points (full n) ≃ (Fin n → ℝ) where
  toFun := Subtype.val
  invFun x := ⟨x,one_ne_zero⟩
  left_inv _ := rfl
  right_inv _ := rfl

def fullHomEquiv (n : ℕ) (A : Code) : (code (full n) ⟶ A) ≃ (Fin n → Carrier A) :=
  (pointEquiv (1 : Free n)).trans {
    toFun := Subtype.val
    invFun x := ⟨x,by change IsUnit ((evaluate x).toAlgHom 1); rw [map_one]; exact isUnit_one⟩
    left_inv _ := rfl
    right_inv _ := rfl }

def fullPowerIso (n : ℕ) : embedding.obj (full n) ≅ SmoothOpenSite.scalarPower n where
  hom := ⟨{app A := ↾fun h => fullHomEquiv n A.unop.unop h.unop}⟩
  inv := ⟨{app A := ↾fun x => ((fullHomEquiv n A.unop.unop).symm x).op
           naturality A B f := by
             ext x
             apply Quiver.Hom.unop_inj
             apply (fullHomEquiv n B.unop.unop).injective
             funext i
             symm
             change smoothMap f.unop.unop (smoothMap ((fullHomEquiv n A.unop.unop).symm x)
               (principalBase 1 (generator i))) = _
             have ha := congrFun ((fullHomEquiv n A.unop.unop).apply_symm_apply x) i
             have hb := congrFun ((fullHomEquiv n B.unop.unop).apply_symm_apply
               (fun j => smoothMap f.unop.unop (x j))) i
             exact (congrArg (smoothMap f.unop.unop) ha).trans hb.symm}⟩
  hom_inv_id := by ext A h; exact congrArg Quiver.Hom.op ((fullHomEquiv n A.unop.unop).symm_apply_apply h.unop)
  inv_hom_id := by ext A x; exact (fullHomEquiv n A.unop.unop).apply_symm_apply x

def fullLineIso : embedding.obj (full 1) ≅ SmoothOpenSite.scalar :=
  fullPowerIso 1 ≪≫ {
    hom := ⟨powerScalarIso.hom⟩
    inv := ⟨powerScalarIso.inv⟩
    hom_inv_id := by ext A x; funext i; fin_cases i; rfl
    inv_hom_id := by ext A x; rfl }

def inclusion (U : Domain) : U ⟶ full U.dimension :=
  {toFun x := ⟨x.val,one_ne_zero⟩
   smooth i := (OpenFunctions.representative_iff _ (fun x => x i) (fun _ => rfl)).mpr
     (contDiff_apply ℝ (fun _ : Fin U.dimension => ℝ) i).contDiffOn}

theorem inclusion_base (U : Domain) (a : Free U.dimension) :
    Localization.pullback (inclusion U) (principalBase 1 a) = principalBase U.defining a := by
  apply (toOpen_bijective U.defining).injective
  apply OpenFunctions.ext
  intro x
  rw [Localization.pullback_apply,toOpen_base,toOpen_base]
  rfl

/-- Under the full-space comparison, the inclusion is the existing localization map on coordinates. -/
theorem inclusion_coordinates (U : Domain) (A : Code) (a : code U ⟶ A) (i : Fin U.dimension) :
    ((embedding.map (inclusion U) ≫ (fullPowerIso U.dimension).hom).hom.app (op (op A)) a.op) i =
      smoothMap a (principalBase U.defining (generator i)) := by
  change smoothMap a (Localization.pullback (inclusion U) (principalBase 1 (generator i))) = _
  rw [inclusion_base]

/-- The model respects ordinary composition, including open-domain maps. -/
theorem composition {U V W : Domain} (f : U ⟶ V) (g : V ⟶ W) :
    embedding.map (f ≫ g) = embedding.map f ≫ embedding.map g := embedding.map_comp f g

end SquareKit.EuclideanOpen
