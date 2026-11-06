import SquareKit.Internal.PathTransport.TwoFamilyOrdinaryEndpointAction
import SquareKit.Internal.PathTransport.TwoFamilyOrdinaryBranchValues
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
set_option maxHeartbeats 200000
private theorem discrete_identity_as (C D : StrictTwoCategory.{u,u,u})
 (e : C = D) [Subsingleton D] {a b : C} (d : D)
 (p : LocallyDiscrete (a ⟶ b)) (h : HEq p (LocallyDiscrete.mk (𝟙 d))) :
 HEq p.as (𝟙 a) := by
 cases e
 have ha : d = a := Subsingleton.elim _ _
 have hb : b = a := Subsingleton.elim _ _
 subst d; subst b
 exact heq_of_eq (congrArg LocallyDiscrete.as (eq_of_heq h))
namespace SourceContraction
variable {Γ Δ : Context.{u}} (F : Family Γ) (i : StrictPseudofunctor Δ Γ)
 (s t : TwoFamily.Section F.data) (d : TwoFamily.Section (reindex i (closedId F.data s t)))
def BranchArrowIdentity : Prop := ∀ δ, HEq
 (d.normalObj (reindex i (closedId F.data s t)) δ).fiber.as
 (𝟙 (s.normalObj F.data (i.obj δ)).fiber)
theorem branchArrowIdentity_of_values (B : Family Δ) [∀δ, Subsingleton (B.data.obj δ)]
 (v : TwoFamily.Section B.data) (e : F.reindex i = B)
 (h : SectionIdentityValues ((F.identity s t).reindex i) B ⟨d⟩ ⟨v⟩) :
 BranchArrowIdentity F i s t d := by
 intro δ
 exact discrete_identity_as _ _ (congrArg (fun H : Family Δ => H.data.obj δ) e)
  (v.normalObj B.data δ).fiber _ (h δ)
end SourceContraction
end SquareKit.Internal.PathTransport.HigherInterpretation

namespace SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
open CategoryTheory Bicategory TwoFamily
universe u
private theorem identity_branch_action {C D : Type u} [Category C] [Category D]
 [IsGroupoid D] [Subsingleton C] [Subsingleton D]
 (F : C ⥤ D) {a b : C} {c d : D} (l : F.obj a ⟶ c) (p : a ⟶ b) (r : F.obj b ⟶ d)
 (hl : HEq l (𝟙 c)) (hp : HEq p (𝟙 a)) :
 HEq (LocallyDiscrete.mk (inv l ≫ F.map p ≫ r)) (LocallyDiscrete.mk r) := by
 have hb : b = a := Subsingleton.elim _ _
 subst b
 have hc : c = F.obj a := Subsingleton.elim _ _
 subst c
 cases eq_of_heq hl
 cases eq_of_heq hp
 simp
variable {Γ Δ Θ : Context.{u}} {i : StrictPseudofunctor Δ Γ} (c : SourceContraction i)
 (F : Family Γ) (s t : TwoFamily.Section F.data)
 (d : TwoFamily.Section (reindex i (closedId F.data s t)))
def LeftArrowIdentity : Prop := ∀z, HEq (s.normalMap F.data (c.homotopy.app z)).fiber
 (𝟙 (s.normalObj F.data z).fiber)
theorem leftArrowIdentity_of_values [∀z, Subsingleton (F.data.obj z)]
 (v : ∀z, F.data.obj z)
 (h : ∀z, HEq (s.normalMap F.data (c.homotopy.app z)).fiber (𝟙 (v z))) :
 c.LeftArrowIdentity F s := by
 intro z
 have hv : v z = (s.normalObj F.data z).fiber := Subsingleton.elim _ _
 have hid : HEq (𝟙 (v z)) (𝟙 (s.normalObj F.data z).fiber) := by rw [hv]; rfl
 exact (h z).trans hid
def ReducedIdentityEndpointAction (σ : StrictPseudofunctor Θ Γ) (G : Family Θ) (p : TwoFamily.Section G.data) : Prop :=
 ∀z, HEq (p.normalObj G.data z).fiber
  (LocallyDiscrete.mk (t.normalMap F.data (c.homotopy.app (σ.obj z))).fiber)
theorem reduce_identity_endpoint [∀z, Subsingleton (F.data.obj z)]
 (hl : c.LeftArrowIdentity F s) (hb : BranchArrowIdentity F i s t d)
 (σ : StrictPseudofunctor Θ Γ) (G : Family Θ) (p : TwoFamily.Section G.data)
 (h : c.IdentityEndpointActionFormula F s t d σ G p) :
 c.ReducedIdentityEndpointAction F t σ G p := by
 intro z
 exact (h z).trans (identity_branch_action (F.data.map (c.homotopy.app (σ.obj z))).toFunctor
  _ _ _ (hl (σ.obj z)) (hb (c.retraction.obj (σ.obj z))))
end SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
