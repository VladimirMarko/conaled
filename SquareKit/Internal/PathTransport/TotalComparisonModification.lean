import SquareKit.Internal.PathTransport.TotalFamilyModification
import SquareKit.Internal.PathTransport.ComparisonModification

/-! Coherent fiber comparison recovered from a total comparison with its
selected base component. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Grpd.{u,u}} {F G : C ⥤ D} (η : F ≅ G)
    {A : C ⥤ Grpd.{u,u}} {B : D ⥤ Grpd.{u,u}}

structure TotalModification (α : A ⟶ F ⋙ B) (β : A ⟶ G ⋙ B) where
  total : totalMap F α ≅ totalMap G β
  base : ∀ x, (total.hom.app x).base = η.hom.app x.base

namespace TotalModification
variable {η} {α : A ⟶ F ⋙ B} {β : A ⟶ G ⋙ B}

def vertical (m : TotalModification η α β) :
    TotalFamilyModification G (α ≫ whiskerRight η.hom B) β where
  total := (transportTotal η α).symm ≪≫ m.total
  base x := by
    simp [transportTotal, m.base, Grothendieck.preNatIso, Grothendieck.transportIso]

def modification (m : TotalModification η α β) : Modification η α β :=
  m.vertical.modification

/-- Extracting coherent fiber components and rebuilding comprehension preserves
all selected total arrows, not only their base components. -/
theorem modification_total (m : TotalModification η α β) :
    Modification.totalIso η m.modification = m.total := by
  simp only [Modification.totalIso, modification, TotalFamilyModification.modification_total]
  simp [vertical]


end TotalModification
end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
