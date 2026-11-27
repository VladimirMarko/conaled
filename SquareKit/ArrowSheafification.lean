import SquareKit.LocallyConstantGroup
import SquareKit.SheafGroupoidAction
import SquareKit.SheafGroupoidStackification
import SquareKit.SheafGroupoidSections
import Mathlib.CategoryTheory.SingleObj

/-! Arrow correction for constant group presentations on topological opens.
The normalized input identifies empty-open labels before adding local gluing.
The sectionwise unit then feeds the existing represented-groupoid completion. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.ArrowSheafification
open CategoryTheory Opposite TopologicalSpace
open LocallyConstantSheaf
variable (X : TopCat.{0}) (G : Type) [Group G]
/-- Globally constant labels, including the unique function on an empty open. -/
def constants (U : Opens X) : Subgroup (LocallyConstant U G) where
  carrier := {f | ∀ x y, f x = f y}
  one_mem' := by intro x y; rfl
  mul_mem' := by intro a b ha hb x y; change a x * b x = a y * b y; rw [ha x y, hb x y]
  inv_mem' := by intro a ha x y; change (a x)⁻¹ = (a y)⁻¹; rw [ha x y]
/-- The group presheaf with empty-open identification already performed. -/
def normalized : (Opens X)ᵒᵖ ⥤ GrpCat where
  obj U := GrpCat.of (constants X G U.unop)
  map f := GrpCat.ofHom {
    toFun s := ⟨s.val.comap ⟨f.unop, (Opens.isOpenEmbedding_of_le f.unop.le).continuous⟩,
      fun x y => s.property (f.unop x) (f.unop y)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

def inclusion : normalized X G ⋙ forget GrpCat ⟶ SquareKit.LocallyConstantSheaf.data X G where
  app _ := ↾Subtype.val

instance inclusion_isLocallyInjective : Presheaf.IsLocallyInjective (SquareKit.LocallyConstantSheaf.site X) (inclusion X G) :=
  Presheaf.isLocallyInjective_of_injective _ _ (fun _ => Subtype.val_injective)

def normalize : (Functor.const (Opens X)ᵒᵖ).obj G ⟶ normalized X G ⋙ forget GrpCat where
  app U := ↾fun g => ⟨LocallyConstant.const U.unop g, fun _ _ => rfl⟩

theorem factor : normalize X G ≫ inclusion X G = unit X G := rfl

instance inclusion_isLocallySurjective : Presheaf.IsLocallySurjective (site X) (inclusion X G) := by
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac (site X) (factor X G)

/-- Local correction of normalized labels is the same locally constant sheaf. -/
def normalizedIso : (presheafToSheaf (site X) (Type 0)).obj
    (normalized X G ⋙ forget GrpCat) ≅ obj X G := by
  haveI : IsIso ((presheafToSheaf (site X) (Type 0)).map (inclusion X G)) :=
    ((site X).W_iff _).mp ((site X).W_of_isLocallyBijective (inclusion X G))
  exact asIso ((presheafToSheaf (site X) (Type 0)).map (inclusion X G)) ≪≫
    asIso ((sheafificationAdjunction (site X) (Type 0)).counit.app (obj X G))

/-- The normalized comparison also extends its specified input unit. -/
theorem normalizedIso_unit :
    toSheafify (site X) (normalized X G ⋙ forget GrpCat) ≫
      (normalizedIso X G).hom.hom = inclusion X G := by
  change toSheafify (site X) _ ≫ sheafifyMap (site X) (inclusion X G) ≫
    ((sheafificationAdjunction (site X) (Type 0)).counit.app (obj X G)).hom = _
  rw [sheafificationAdjunction_counit_app_val, ← Category.assoc, ← toSheafify_naturality,
    Category.assoc, toSheafify_sheafifyLift, Category.comp_id]

namespace Completion
variable (X : TopCat.{0}) (G : Type) [Group G]
def action : SheafActionQuotient.Action (LocallyConstantGroup.obj X G) (obj X PUnit) where
  act _ _ m := m
  one_act _ _ := rfl
  mul_act _ _ _ _ := rfl
  natural _ _ _ := rfl
abbrev operations := SheafGroupoidAction.operations (action X G)
variable (U : (Opens X)ᵒᵖ)
def point : (operations X G).Object ((SheafGroupoid.sectionParameter (site X)).obj U.unop) :=
  ⟨(SheafGroupoid.sectionEquiv (F := obj X PUnit)).symm (LocallyConstant.const U.unop PUnit.unit)⟩
def loop (g : LocallyConstant U.unop G) : point X G U ⟶ point X G U where
  map := SheafRelation.lift ((SheafGroupoid.sectionEquiv (F := obj X G)).symm g) (point X G U).map
  source := rfl
  target := rfl
theorem loop_mul (g h : LocallyConstant U.unop G) : loop X G U (h*g) = loop X G U g ≫ loop X G U h := by
  change loop X G U (h*g) = SheafGroupoid.Operations.Arrow.comp _ _ _
  apply SheafGroupoid.Operations.Arrow.ext
  have hl : (loop X G U (h*g)).map ≫ SheafGroupoidAction.label =
      (SheafGroupoid.Operations.Arrow.comp (operations X G) (loop X G U g) (loop X G U h)).map ≫ SheafGroupoidAction.label := by
    change (SheafGroupoid.sectionEquiv (F := obj X G)).symm (h*g) = _
    change _ = CategoryTheory.Limits.pullback.lift _ _ _ ≫ SheafTorsor.labelMul (G := LocallyConstantGroup.obj X G) _ _
    rw [SheafTorsor.labelMul_precomp]
    simp only [← Category.assoc, CategoryTheory.Limits.pullback.lift_fst,
      CategoryTheory.Limits.pullback.lift_snd]
    apply SheafGroupoid.sectionEquiv.injective
    change SheafGroupoid.sectionEquiv ((SheafGroupoid.sectionEquiv (F := obj X G)).symm (h*g)) =
      @HMul.hMul (LocallyConstant U.unop G) (LocallyConstant U.unop G)
        (LocallyConstant U.unop G) inferInstance
        (SheafGroupoid.sectionEquiv ((SheafGroupoid.sectionEquiv (F := obj X G)).symm h))
        (SheafGroupoid.sectionEquiv ((SheafGroupoid.sectionEquiv (F := obj X G)).symm g))
    simp
  ext V z
  apply Prod.ext
  · exact congrArg (fun f => f.hom.app V z) hl
  · exact (congrArg (fun f => f.hom.app V z)
      (SheafGroupoid.Operations.Arrow.comp (operations X G) (loop X G U g) (loop X G U h)).source).symm
/-- Every automorphism of the represented point has a unique locally constant label. -/
def loopEquiv : LocallyConstant U.unop G ≃ (point X G U ⟶ point X G U) where
  toFun := loop X G U
  invFun f := SheafGroupoid.sectionEquiv (f.map ≫ SheafGroupoidAction.label)
  left_inv g := by change SheafGroupoid.sectionEquiv ((SheafGroupoid.sectionEquiv (F := obj X G)).symm g) = g; simp
  right_inv f := by
    apply SheafGroupoid.Operations.Arrow.ext
    have hl := (SheafGroupoid.sectionEquiv (F := obj X G)).symm_apply_apply
      (f.map ≫ SheafGroupoidAction.label)
    ext V z
    apply Prod.ext
    · exact congrArg (fun k => k.hom.app V z) hl
    · exact (congrArg (fun k => k.hom.app V z) f.source).symm

theorem loop_one : loop X G U 1 = 𝟙 (point X G U) := by
  apply (loopEquiv X G U).symm.injective
  change SheafGroupoid.sectionEquiv ((loop X G U 1).map ≫ SheafGroupoidAction.label) =
    SheafGroupoid.sectionEquiv ((SheafGroupoid.Operations.Arrow.ident (operations X G) (point X G U)).map ≫ SheafGroupoidAction.label)
  change SheafGroupoid.sectionEquiv ((SheafGroupoid.sectionEquiv (F := obj X G)).symm (1 : LocallyConstant U.unop G)) = (1 : LocallyConstant U.unop G)
  simp

def labelFunctor : SingleObj (LocallyConstant U.unop G) ⥤
    (operations X G).Object ((SheafGroupoid.sectionParameter (site X)).obj U.unop) where
  obj _ := point X G U
  map g := loop X G U g
  map_id _ := loop_one X G U
  map_comp f g := loop_mul X G U f g

/-- The original constant labels, interpreted by the actual section representation. -/
def rawUnit : SingleObj G ⥤ (operations X G).Object
    ((SheafGroupoid.sectionParameter (site X)).obj U.unop) :=
  (SingleObj.mapHom G (LocallyConstant U.unop G)) (LocallyConstant.constMonoidHom) ⋙ labelFunctor X G U

/-- Arrow correction followed by effective descent through regular bundles. -/
def completedUnit := rawUnit X G U ⋙ SheafGroupoid.Bundle.regularFunctor (operations X G)

/-- The separated, not generally sheaf-valued, input uses the same represented output. -/
def normalizedUnit : SingleObj (constants X G U.unop) ⥤ (operations X G).Object
    ((SheafGroupoid.sectionParameter (site X)).obj U.unop) :=
  (SingleObj.mapHom _ _) (constants X G U.unop).subtype ⋙ labelFunctor X G U

/-- Label restriction is actual precomposition of the represented arrow. -/
theorem loop_restriction {V : (Opens X)ᵒᵖ} (k : U ⟶ V) (g : LocallyConstant U.unop G) :
    (loop X G V ((data X G).map k g)).map =
      (SheafGroupoid.sectionParameter (site X)).map k.unop ≫ (loop X G U g).map := by
  have hl : (SheafGroupoid.sectionEquiv (F := obj X G)).symm ((data X G).map k g) =
      (SheafGroupoid.sectionParameter (site X)).map k.unop ≫
        (SheafGroupoid.sectionEquiv (F := obj X G)).symm g := by
    apply SheafGroupoid.sectionEquiv.injective
    rw [SheafGroupoid.sectionEquiv_naturality]
    simp only [Equiv.apply_symm_apply]
  have hp : (point X G V).map =
      (SheafGroupoid.sectionParameter (site X)).map k.unop ≫ (point X G U).map := by
    apply SheafGroupoid.sectionEquiv.injective
    simp [point]
    rfl
  ext W z
  apply Prod.ext
  · exact congrArg (fun f => f.hom.app W z) hl
  · exact congrArg (fun f => f.hom.app W z) hp

/-- The subsequent completion commutes with the same change of parameter. -/
theorem completion_restriction {V : (Opens X)ᵒᵖ} (k : U ⟶ V) :
    SheafGroupoid.Bundle.regularFunctor (operations X G) ⋙
      SheafGroupoid.Bundle.restriction ((SheafGroupoid.sectionParameter (site X)).map k.unop) =
    (operations X G).restriction ((SheafGroupoid.sectionParameter (site X)).map k.unop) ⋙
      SheafGroupoid.Bundle.regularFunctor (operations X G) :=
  SheafGroupoid.Bundle.regularFunctor_restriction _ _

/-- Completion preserves each corrected isotropy label faithfully. -/
theorem completed_loop_injective : Function.Injective
    (fun g => (SheafGroupoid.Bundle.regularFunctor (operations X G)).map (loop X G U g)) := by
  intro g h e
  apply (loopEquiv X G U).injective
  exact (SheafGroupoid.Bundle.regularFullyFaithful (operations X G)).map_injective e

/-- Recovery uses the actual sheafification unit and its inverse before completion. -/
theorem recovered_loop (g : LocallyConstant U.unop G) :
    (SheafGroupoid.Bundle.regularFunctor (operations X G)).map
      (loop X G U ((LocallyConstantGroup.alreadySheaf X G).inv.app U
        ((toSheafify (site X) (data X G)).app U g))) =
    (SheafGroupoid.Bundle.regularFunctor (operations X G)).map (loop X G U g) := by
  congr 2
  exact congrFun (congrArg (fun f => f.app U) (LocallyConstantGroup.alreadySheaf X G).hom_inv_id) g
end Completion
end SquareKit.ArrowSheafification
