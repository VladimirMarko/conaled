import SquareKit.ElementSiteComparison
import SquareKit.PrincipalSheafContext
import SquareKit.PrincipalSheafLocalEquivalence
import SquareKit.SheafActionQuotient
import SquareKit.SheafFamilyCover

/-! Direct restriction of sheaves, families and actions along a fully faithful dense subsite. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafSiteComparison
open CategoryTheory Opposite
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
variable [F.IsContinuous J K]

abbrev restriction := F.sheafPushforwardContinuous (Type u) J K
abbrev groupRestriction := F.sheafPushforwardContinuous GrpCat.{u} J K
abbrev sheaf (X : Sheaf K (Type u)) := (restriction J K F).obj X
abbrev group (G : Sheaf K GrpCat.{u}) := (groupRestriction J K F).obj G
abbrev map {X Y : Sheaf K (Type u)} (f : X ⟶ Y) := (restriction J K F).map f
abbrev elements (X : Sheaf K (Type u)) := Functor.Elements.precomp F.op X.obj

/-- Restriction retains the dependent fibers at every image object. -/
def family {X : Sheaf K (Type u)} (A : SplitSheaf.Ty X) : SplitSheaf.Ty (sheaf J K F X) where
  family := elements K F X ⋙ A.family
  isSheaf := (sheaf J K F (SplitSheaf.Ext A)).property

/-- The total space and its projection restrict componentwise. -/
theorem family_total {X : Sheaf K (Type u)} (A : SplitSheaf.Ty X) :
    SplitSheaf.Ext (family J K F A) = sheaf J K F (SplitSheaf.Ext A) := rfl

theorem family_projection {X : Sheaf K (Type u)} (A : SplitSheaf.Ty X) :
    SplitSheaf.p (family J K F A) = map J K F (SplitSheaf.p A) := rfl

/-- The restricted group has precisely the restriction of the underlying group sheaf. -/
theorem underlying_group (G : Sheaf K GrpCat.{u}) :
    SheafTorsor.groupSheaf (group J K F G) = sheaf J K F (SheafTorsor.groupSheaf G) := rfl

def action {G : Sheaf K GrpCat.{u}} {M : Sheaf K (Type u)}
    (a : SheafActionQuotient.Action G M) :
    SheafActionQuotient.Action (group J K F G) (sheaf J K F M) where
  act X := a.act (F.op.obj X)
  one_act X := a.one_act (F.op.obj X)
  mul_act X := a.mul_act (F.op.obj X)
  natural f := a.natural (F.op.map f)

/-- Every jointly locally surjective family remains covering after restriction. -/
theorem joint_cover [F.IsCocontinuous J K] {I : Type u} {X : Sheaf K (Type u)}
    {Y : I → Sheaf K (Type u)} (f : ∀ i, Y i ⟶ X)
    (hf : SheafFamilyCover.JointlyLocallySurjective f) :
    SheafFamilyCover.JointlyLocallySurjective (fun i => map J K F (f i)) := by
  intro U x
  exact F.cover_lift J K (hf x)

/-- Restricting a family commutes strictly with arbitrary parameter substitution. -/
theorem family_reindex {X Y : Sheaf K (Type u)} (A : SplitSheaf.Ty X) (f : Y ⟶ X) :
    family J K F (SplitSheaf.tySub A f) =
      SplitSheaf.tySub (family J K F A) (map J K F f) := rfl

end SquareKit.SheafSiteComparison
