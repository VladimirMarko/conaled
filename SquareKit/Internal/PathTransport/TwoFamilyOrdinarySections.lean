import SquareKit.Internal.PathTransport.TwoFamilyClosedComparisonComponent
import SquareKit.Internal.PathTransport.TwoLocallyDiscreteTarget
import SquareKit.Internal.PathTransport.TwoFamilyConstantProjection
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (Γ : Type u) [Bicategory.{u,u} Γ] [Strict Γ]
variable (C : Type u) [Groupoid.{u} C]
noncomputable def constantSectionFunctor (s : TwoFamily.Section (constantFamily Γ (discreteCategory C))) : Γ ⥤ C :=
 locallyDiscreteTargetFunctor (s.lift.comp (constantDiscreteProjection Γ C))
noncomputable def ordinarySectionComparison
 (s t : TwoFamily.Section (constantFamily Γ (discreteCategory C)))
 (β : Pseudofunctor.StrongTrans s.lift.toPseudofunctor t.lift.toPseudofunctor) :
 constantSectionFunctor Γ C s ⟶ constantSectionFunctor Γ C t :=
 locallyDiscreteTargetComparison (strongPostcomp β (constantDiscreteProjection Γ C))
theorem ordinarySectionComparison_app
 (s t : TwoFamily.Section (constantFamily Γ (discreteCategory C)))
 (β : Pseudofunctor.StrongTrans s.lift.toPseudofunctor t.lift.toPseudofunctor) (z : Γ) :
 (ordinarySectionComparison Γ C s t β).app z = (β.app z).fiber.as := rfl
theorem ordinarySectionComparison_naturality
 (s t : TwoFamily.Section (constantFamily Γ (discreteCategory C)))
 (β : Pseudofunctor.StrongTrans s.lift.toPseudofunctor t.lift.toPseudofunctor)
 {a b : Γ} (f : a ⟶ b) :
 (s.lift.map f).fiber.as ≫ (β.app b).fiber.as =
 (β.app a).fiber.as ≫ (t.lift.map f).fiber.as :=
 (ordinarySectionComparison Γ C s t β).naturality f
variable [IsLocallyGroupoid Γ]
local instance : ∀ γ, IsGroupoid ((constantFamily Γ (discreteCategory C)).obj γ) :=
 fun _ => by
  change IsGroupoid (LocallyDiscrete C)
  refine ⟨fun f => ?_⟩
  let : IsIso f.as := IsGroupoid.all_isIso (C := C) _
  exact ⟨⟨⟨inv f.as⟩, Discrete.ext (IsIso.hom_inv_id f.as),
    Discrete.ext (IsIso.inv_hom_id f.as)⟩⟩
local instance : ∀ γ, IsLocallyGroupoid ((constantFamily Γ (discreteCategory C)).obj γ) :=
 fun _ => by
  change IsLocallyGroupoid (LocallyDiscrete C)
  intro a b
  change IsGroupoid (Discrete (a.as ⟶ b.as))
  infer_instance
noncomputable def constantSectionComparison
 (s t : TwoFamily.Section (constantFamily Γ (discreteCategory C)))
 (p : TwoFamily.Section (closedId (constantFamily Γ (discreteCategory C)) s t)) :
 constantSectionFunctor Γ C s ⟶ constantSectionFunctor Γ C t :=
 locallyDiscreteTargetComparison (strongPostcomp
  (closedComparison (constantFamily Γ (discreteCategory C)) s t p) (constantDiscreteProjection Γ C))
private theorem discrete_as_heq {X Y : Type u} (e : X = Y)
 {a : Discrete X} {b : Discrete Y} (h : HEq a b) : HEq a.as b.as := by
 cases e
 cases eq_of_heq h
 rfl
def OrdinarySelectedComponents
 (s t : TwoFamily.Section (constantFamily Γ (discreteCategory C)))
 (p : TwoFamily.Section (closedId (constantFamily Γ (discreteCategory C)) s t))
 (β : Pseudofunctor.StrongTrans s.lift.toPseudofunctor t.lift.toPseudofunctor) : Prop :=
 ∀ z, HEq ((ordinarySectionComparison Γ C s t β).app z)
  (p.normalObj (closedId (constantFamily Γ (discreteCategory C)) s t) z).fiber.as.as
theorem ordinarySelectedComponents_of_native
 (s t : TwoFamily.Section (constantFamily Γ (discreteCategory C)))
 (p : TwoFamily.Section (closedId (constantFamily Γ (discreteCategory C)) s t))
 (β : Pseudofunctor.StrongTrans s.lift.toPseudofunctor t.lift.toPseudofunctor)
 (h : ClosedComparisonComponentFormula (constantFamily Γ (discreteCategory C)) s t p β) :
 OrdinarySelectedComponents Γ C s t p β := by
 intro z
 exact discrete_as_heq rfl (h z)
theorem constantSectionComparison_components
 (s t : TwoFamily.Section (constantFamily Γ (discreteCategory C)))
 (p : TwoFamily.Section (closedId (constantFamily Γ (discreteCategory C)) s t)) :
 OrdinarySelectedComponents Γ C s t p (closedComparison (constantFamily Γ (discreteCategory C)) s t p) :=
 ordinarySelectedComponents_of_native Γ C s t p _ (closedComparison_components _ _ _ _)
end SquareKit.Internal.PathTransport.HigherInterpretation
