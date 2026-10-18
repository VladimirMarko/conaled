import SquareKit.SliceDependentProduct
import SquareKit.SheafSliceFunction
import SquareKit.AdjointComparison
import SquareKit.SheafProductBaseChange

/-! Experimental dependent products along every ordinary sheaf map. Slice
closure supplies internal sections; all adjunctions use ordinary pullbacks. -/
noncomputable section
namespace SquareKit.SheafDependentProduct
open CategoryTheory Limits MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A Γ : Sheaf J (Type (max u v))} (f : A ⟶ Γ)
local instance : CartesianMonoidalCategory (Over Γ) := Over.cartesianMonoidalCategory Γ
local instance : MonoidalClosed (Over Γ) := SheafSliceFunction.closed Γ

abbrev pi : Over A ⥤ Over Γ := SliceDependentProduct.pi f
abbrev adjunction : Over.pullback f ⊣ pi f := SliceDependentProduct.adjunction f
abbrev exponentiable := SliceDependentProduct.exponentiable f
abbrev homEquiv (X : Over Γ) (Y : Over A) := (adjunction f).homEquiv X Y

def curry {X : Over Γ} {Y : Over A} (k : (Over.pullback f).obj X ⟶ Y) : X ⟶ (pi f).obj Y :=
  homEquiv f X Y k

def uncurry {X : Over Γ} {Y : Over A} (k : X ⟶ (pi f).obj Y) : (Over.pullback f).obj X ⟶ Y :=
  (homEquiv f X Y).symm k

def evaluation (Y : Over A) : (Over.pullback f).obj ((pi f).obj Y) ⟶ Y :=
  (adjunction f).counit.app Y

@[simp] theorem beta {X : Over Γ} {Y : Over A} (k : (Over.pullback f).obj X ⟶ Y) :
    uncurry f (curry f k) = k := (homEquiv f X Y).symm_apply_apply k
@[simp] theorem eta {X : Over Γ} {Y : Over A} (k : X ⟶ (pi f).obj Y) :
    curry f (uncurry f k) = k := (homEquiv f X Y).apply_symm_apply k

theorem uncurry_evaluation {X : Over Γ} {Y : Over A} (k : X ⟶ (pi f).obj Y) :
    uncurry f k = (Over.pullback f).map k ≫ evaluation f Y :=
  (adjunction f).homEquiv_counit X Y k

theorem evaluation_display (Y : Over A) :
    (evaluation f Y).left ≫ Y.hom = Family.reindex ((pi f).obj Y).hom f :=
  Over.w (evaluation f Y)

theorem parameter_natural {X X' : Over Γ} {Y : Over A} (g : X' ⟶ X)
    (k : (Over.pullback f).obj X ⟶ Y) :
    curry f ((Over.pullback f).map g ≫ k) = g ≫ curry f k :=
  (adjunction f).homEquiv_naturality_left g k

theorem family_natural {X : Over Γ} {Y Y' : Over A} (g : Y ⟶ Y')
    (k : (Over.pullback f).obj X ⟶ Y) :
    curry f (k ≫ g) = curry f k ≫ (pi f).map g :=
  (adjunction f).homEquiv_naturality_right k g

/-- Compare any previously constructed adjunction for the same ordinary pullback. -/
def comparison {R : Over A ⥤ Over Γ} (a : Over.pullback f ⊣ R) : pi f ≅ R :=
  (adjunction f).rightAdjointUniq a

theorem comparison_curry {R : Over A ⥤ Over Γ} (a : Over.pullback f ⊣ R)
    {X : Over Γ} {Y : Over A} (k : (Over.pullback f).obj X ⟶ Y) :
    curry f k ≫ (comparison f a).hom.app Y = a.homEquiv X Y k :=
  AdjointComparison.curry (adjunction f) a k

theorem comparison_evaluation {R : Over A ⥤ Over Γ} (a : Over.pullback f ⊣ R) (Y : Over A) :
    (Over.pullback f).map ((comparison f a).hom.app Y) ≫ a.counit.app Y = evaluation f Y :=
  Adjunction.rightAdjointUniq_hom_app_counit (adjunction f) a Y

/-- Natural comparisons for every input family, including dependent ones. -/
abbrev terminalComparison (A : Sheaf J (Type (max u v))) :=
  comparison (SheafTerminalProduct.terminalMap A) (SheafTerminalProduct.adjunction A)
abbrev projectionComparison (A Γ : Sheaf J (Type (max u v))) :=
  comparison (SheafRelation.snd A Γ) (SheafProjectionProduct.adjunction A Γ)
abbrev terminal_curry (A : Sheaf J (Type (max u v)))
    {X : Over (𝟙_ (Sheaf J (Type (max u v))))} {Y : Over A} :=
  comparison_curry (SheafTerminalProduct.terminalMap A) (SheafTerminalProduct.adjunction A) (X := X) (Y := Y)
abbrev terminal_evaluation (A : Sheaf J (Type (max u v))) :=
  comparison_evaluation (SheafTerminalProduct.terminalMap A) (SheafTerminalProduct.adjunction A)
abbrev projection_curry (A Γ : Sheaf J (Type (max u v)))
    {X : Over Γ} {Y : Over (SheafRelation.product A Γ)} :=
  comparison_curry (SheafRelation.snd A Γ) (SheafProjectionProduct.adjunction A Γ) (X := X) (Y := Y)
abbrev projection_evaluation (A Γ : Sheaf J (Type (max u v))) :=
  comparison_evaluation (SheafRelation.snd A Γ) (SheafProjectionProduct.adjunction A Γ)

section BaseChange
variable {A' Γ' : Sheaf J (Type (max u v))} {f' : A' ⟶ Γ'} {g : Γ' ⟶ Γ} {g' : A' ⟶ A}
variable (h : IsPullback f' g' g f)

abbrev baseChange : pi f ⋙ Over.pullback g ≅ Over.pullback g' ⋙ pi f' :=
  DependentBaseChange.WithAdjunction.iso h (adjunction f) (adjunction f')
abbrev baseChange_evaluation := DependentBaseChange.WithAdjunction.evaluation h (adjunction f) (adjunction f')
abbrev baseChange_curry := DependentBaseChange.WithAdjunction.curry_baseChange h (adjunction f) (adjunction f')

/-- Canonical base change commutes with replacement by any previous right
adjoints, hence with terminal/projection base change in particular. -/
theorem baseChange_comparison {R : Over A ⥤ Over Γ} {R' : Over A' ⥤ Over Γ'}
    (a : Over.pullback f ⊣ R) (a' : Over.pullback f' ⊣ R') (Y : Over A) :
    (Over.pullback g).map ((comparison f a).hom.app Y) ≫
      (DependentBaseChange.WithAdjunction.mate h a a').app Y =
    (baseChange f h).hom.app Y ≫ (comparison f' a').hom.app ((Over.pullback g').obj Y) :=
  AdjointComparison.mate (adjunction f) a (adjunction f') a' (DependentBaseChange.pullbackComparison h) Y

end BaseChange
/-- The previous terminal-to-projection mate is recovered through the canonical
comparisons of both right adjoints. -/
abbrev terminalProjection_baseChange (A Γ : Sheaf J (Type (max u v))) :=
  baseChange_comparison (SheafTerminalProduct.terminalMap A)
    (SheafProjectionProduct.projectionSquare A Γ)
    (SheafTerminalProduct.adjunction A) (SheafProjectionProduct.adjunction A Γ)

end SquareKit.SheafDependentProduct
