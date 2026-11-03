import SquareKit.SplitSheaf
import SquareKit.TypeFamily

/-! Experimental stagewise comparison with the native split Type model.
Natural terms give native terms at each stage; arbitrary stage functions need
not form a sheaf term. This is an external comparison, not source syntax. -/
namespace Examples.SplitNative
open CategoryTheory Opposite SquareKit
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ Δ : Sheaf J (Type w)}

def family (A : SplitSheaf.Ty Γ) (U : Cᵒᵖ) : Γ.obj.obj U → Type w :=
  fun x => A.family.obj (Γ.obj.elementsMk U x)
def term {A : SplitSheaf.Ty Γ} (t : SplitSheaf.Tm A) (U : Cᵒᵖ) : DependentSquares.Tm (family A U) :=
  fun x => t.val (Γ.obj.elementsMk U x)

theorem tySub (A : SplitSheaf.Ty Γ) (σ : Δ ⟶ Γ) (U : Cᵒᵖ) :
    family (SplitSheaf.tySub A σ) U = DependentSquares.tySub (family A U) (σ.hom.app U) := rfl

theorem tmSub {A : SplitSheaf.Ty Γ} (t : SplitSheaf.Tm A) (σ : Δ ⟶ Γ) (U : Cᵒᵖ) :
    term (SplitSheaf.tmSub t σ) U = DependentSquares.tmSub (term t U) (σ.hom.app U) := rfl

theorem extension (A : SplitSheaf.Ty Γ) (U : Cᵒᵖ) :
    (SplitSheaf.Ext A).obj.obj U = DependentSquares.Ext (Γ.obj.obj U) (family A U) := rfl

theorem projection (A : SplitSheaf.Ty Γ) (U : Cᵒᵖ) :
    (SplitSheaf.p A).hom.app U = (↾(DependentSquares.p (A := family A U))) := rfl

theorem generic_variable (A : SplitSheaf.Ty Γ) (U : Cᵒᵖ) :
    term (SplitSheaf.q A) U = DependentSquares.q (A := family A U) := rfl

theorem pairing (A : SplitSheaf.Ty Γ) (σ : Δ ⟶ Γ) (t : SplitSheaf.Tm (SplitSheaf.tySub A σ)) (U : Cᵒᵖ) :
    (SplitSheaf.pair A σ t).hom.app U = ↾(DependentSquares.extend (A := family A U) (σ.hom.app U) (term t U)) := rfl

theorem lifted (A : SplitSheaf.Ty Γ) (σ : Δ ⟶ Γ) (U : Cᵒᵖ) :
    (SplitSheaf.lift A σ).hom.app U = ↾(DependentSquares.lift (A := family A U) (σ.hom.app U)) := rfl

/-- The existing native universal-property comparison applies at each stage. -/
abbrev stage_pullback (A : SplitSheaf.Ty Γ) (σ : Δ ⟶ Γ) (U : Cᵒᵖ) :=
  TypeFamily.split_pullback (family A U) (σ.hom.app U)

end Examples.SplitNative
