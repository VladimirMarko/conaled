import SquareKit.Internal.SheafRepresentableClassification
import Examples.NonCubicalClassification

/-! Sheaf recovery and a counterexample to automatic code sheafness. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace Examples.SheafRepresentableClassification
open CategoryTheory SquareKit SquareKit.RepresentableClassification
open NonCubicalClassification

def sheafContext : Sheaf (⊥ : GrothendieckTopology Base) (Type 0) :=
  ⟨context, Presheaf.isSheaf_bot context⟩

def sheafFamily : SplitSheaf.Ty sheafContext :=
  ⟨family, Presheaf.isSheaf_bot _⟩

example : SplitPresheaf.extension (PresheafFamily.decodeSheaf sheafFamily).family ≅
    SplitPresheaf.extension family := (PresheafFamily.evaluation family).totalIso

/-- Every sheaf display can be classified and recovered over its original base. -/
example {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    {Γ B : Sheaf J (Type 0)} (d : B ⟶ Γ) :
    SplitSheaf.extension (PresheafFamily.decodeSheaf (SplitSheaf.ofDisplay d)) ≅ B :=
  PresheafFamily.decodeSheafIso (SplitSheaf.ofDisplay d) ≪≫ SplitSheaf.displayIso d

/-- Strict restriction laws alone do not entail even empty-cover descent. -/
def boolSystem : System.{0} Base where
  Data _ := ULift.{1} Bool
  restrict A _ := A
  restrict_id _ := rfl
  restrict_comp _ _ _ := rfl

theorem codes_not_sheaf : ¬ Presheaf.IsSheaf (⊤ : GrothendieckTopology Base) boolSystem.codes := by
  intro h
  let F : Sheaf (⊤ : GrothendieckTopology Base) (Type 1) := ⟨boolSystem.codes, h⟩
  let _ : Unique (ULift.{1} Bool) := Limits.Types.isTerminalEquivUnique _ (Sheaf.isTerminalOfBotCover F (SingleObj.star ℕ) (by simp))
  have h' : (ULift.up true : ULift.{1} Bool) = ULift.up false := Subsingleton.elim _ _
  have := congrArg ULift.down h'
  contradiction

end Examples.SheafRepresentableClassification
