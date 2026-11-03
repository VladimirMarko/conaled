import SquareKit.TerminalProduct
import SquareKit.TypeFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-! Experimental native Type specialization of terminal-map dependent products.
The comparison is with the existing DependentSquares Pi operations at the
terminal context; it makes no pointwise claim about general sheaves. -/
noncomputable section
namespace SquareKit.TypeTerminalProduct
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
universe u
variable {Γ : Type u} (A : Γ → Type u)

abbrev unit : Type u := PUnit
abbrev family := Over.mk (TypeFamily.display A)
abbrev object : Type u := ((TerminalProduct.pi Γ).obj (family A)).left

/-- Elements are maps from the actual terminal Type in the terminal slice. -/
def pointEquiv : object A ≃
    ((toOverUnit (Type u)).obj unit ⟶ (TerminalProduct.pi Γ).obj (family A)) where
  toFun a := Over.homMk (↾fun _ => a)
  invFun f := f.left PUnit.unit
  left_inv _ := rfl
  right_inv f := by
    apply Over.OverMorphism.ext
    apply ConcreteCategory.hom_ext
    intro x
    cases x
    rfl

/-- Pullback comparison acts on maps out of the pullback, in the needed direction. -/
def pullbackHomEquiv :
    ((Over.pullback (toUnit Γ)).obj ((toOverUnit (Type u)).obj unit) ⟶ family A) ≃
      ((toOver Γ).obj unit ⟶ family A) where
  toFun f := (TerminalProduct.pullbackComparison Γ).inv.app ((toOverUnit (Type u)).obj unit) ≫ f
  invFun f := (TerminalProduct.pullbackComparison Γ).hom.app ((toOverUnit (Type u)).obj unit) ≫ f
  left_inv f := by exact Iso.hom_inv_id_app_assoc (TerminalProduct.pullbackComparison Γ) ((toOverUnit (Type u)).obj unit) f
  right_inv f := by exact Iso.inv_hom_id_app_assoc (TerminalProduct.pullbackComparison Γ) ((toOverUnit (Type u)).obj unit) f

/-- Maps from 1 × Γ over Γ correspond to ordinary sections of the display. -/
def termEquiv : ((toOver Γ).obj unit ⟶ family A) ≃ Family.Term (TypeFamily.display A) where
  toFun f := ⟨(↾fun γ => (PUnit.unit, γ)) ≫ f.left, by
    have h := Over.w f
    apply ConcreteCategory.hom_ext
    intro γ
    exact congrArg (fun k => k (PUnit.unit,γ)) h⟩
  invFun t := Over.homMk ((↾fun x : unit × Γ => x.2) ≫ t.val) (by
    change (_ ≫ t.val) ≫ TypeFamily.display A = _
    rw [Category.assoc, t.property, Category.comp_id]
    rfl)
  left_inv f := by
    apply Over.OverMorphism.ext
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨⟩,γ⟩
    rfl
  right_inv t := by apply Subtype.ext; rfl

/-- Actual terminal-map product elements are native dependent functions. -/
def nativeEquiv : object A ≃ ((γ : Γ) → A γ) :=
  (pointEquiv A).trans
    (((TerminalProduct.homEquiv Γ ((toOverUnit (Type u)).obj unit) (family A)).symm).trans
      ((pullbackHomEquiv A).trans ((termEquiv A).trans (TypeFamily.terms A).symm)))

def lambda (f : (γ : Γ) → A γ) : object A := (nativeEquiv A).symm f
def evaluate (f : object A) (γ : Γ) : A γ := nativeEquiv A f γ

@[simp] theorem beta (f : (γ : Γ) → A γ) (γ : Γ) : evaluate A (lambda A f) γ = f γ :=
  congrFun ((nativeEquiv A).apply_symm_apply f) γ

@[simp] theorem eta (f : object A) : lambda A (evaluate A f) = f :=
  (nativeEquiv A).symm_apply_apply f

/-- Component evaluation is the actual pullback counit after its product comparison. -/
theorem evaluate_counit (f : object A) (γ : Γ) :
    ((TerminalProduct.adjunction Γ).counit.app (family A)).left
      (((TerminalProduct.pullbackComparison Γ).inv.app
        ((TerminalProduct.pi Γ).obj (family A))).left (f,γ)) =
      ⟨γ, evaluate A f γ⟩ := by
  let s := (termEquiv A) ((pullbackHomEquiv A)
    ((TerminalProduct.homEquiv Γ ((toOverUnit (Type u)).obj unit) (family A)).symm
      (pointEquiv A f)))
  have hs := (TypeFamily.terms A).apply_symm_apply s
  have hv := congrArg (fun t : Family.Term (TypeFamily.display A) => t.val γ) hs
  change (⟨γ, evaluate A f γ⟩ : Sigma A) = _ at hv
  have hn := (TerminalProduct.pullbackComparison Γ).inv.naturality (pointEquiv A f)
  have he := (TerminalProduct.adjunction Γ).homEquiv_counit _ _ (pointEquiv A f)
  have hc := congrArg (fun k => k.left (PUnit.unit,γ))
    (congrArg (fun k => k ≫ (TerminalProduct.adjunction Γ).counit.app (family A)) hn)
  have ht := congrArg (fun k =>
    ((TerminalProduct.pullbackComparison Γ).inv.app ((toOverUnit (Type u)).obj unit) ≫ k).left
      (PUnit.unit,γ)) he
  exact hc.trans (ht.symm.trans hv.symm)

/-- Terminal-context specialization of the original native Pi family. -/
abbrev contextFamily : DependentSquares.Ty unit := fun _ => Γ
abbrev valueFamily : DependentSquares.Ty (DependentSquares.Ext unit (contextFamily (Γ := Γ))) :=
  fun z => A z.2

/-- The native comparison lands in the original piTy at its sole context. -/
def piTyEquiv : object A ≃ DependentSquares.piTy (contextFamily (Γ := Γ)) (valueFamily A) PUnit.unit :=
  nativeEquiv A

theorem lambda_lam (b : DependentSquares.Tm (valueFamily A)) :
    piTyEquiv A (lambda A (fun γ => b ⟨PUnit.unit,γ⟩)) =
      DependentSquares.lam b PUnit.unit :=
  (nativeEquiv A).apply_symm_apply _

theorem evaluate_app (f : object A) (γ : Γ) :
    evaluate A f γ = DependentSquares.app
      (fun _ : unit => piTyEquiv A f) (fun _ => γ) PUnit.unit := rfl

theorem native_beta (b : DependentSquares.Tm (valueFamily A)) (a : DependentSquares.Tm (contextFamily (Γ := Γ))) :
    DependentSquares.app (DependentSquares.lam b) a =
      DependentSquares.tmSub b (DependentSquares.extend DependentSquares.idSub a) :=
  DependentSquares.pi_beta b a

theorem native_eta (f : DependentSquares.Tm (DependentSquares.piTy (contextFamily (Γ := Γ)) (valueFamily A))) :
    DependentSquares.lam (DependentSquares.etaBody f) = f :=
  DependentSquares.pi_eta_cwf f

end SquareKit.TypeTerminalProduct
