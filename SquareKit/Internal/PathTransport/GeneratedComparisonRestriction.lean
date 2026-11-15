import SquareKit.Internal.PathTransport.ComparisonInterpretation

/-! Extract a comparison on the same generated semantic codes at its two
endpoints. Projection equalities transport indices; the entire functor and
natural transformation, including their arrow actions, are retained. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

namespace Context

def relabel (Γ : Context.{u}) {C D : Grpd.{u,u}} (hC : Γ.left = C) (hD : Γ.right = D) :
    C ⥤ D := by
  subst C; subst D
  exact Γ.map

theorem relabel_heq (Γ : Context.{u}) {C D : Grpd.{u,u}}
    (hC : Γ.left = C) (hD : Γ.right = D) : HEq (Γ.relabel hC hD) Γ.map := by
  subst C; subst D; rfl

end Context
namespace Family

def relabelMap {Γ : Context.{u}} (A : Family Γ) {C D : Grpd.{u,u}}
    (hC : Γ.left = C) (hD : Γ.right = D)
    {B : C ⥤ Grpd.{u,u}} {E : D ⥤ Grpd.{u,u}}
    (hB : HEq A.left B) (hE : HEq A.right E) : B ⟶ Γ.relabel hC hD ⋙ E := by
  subst C; subst D
  cases eq_of_heq hB; cases eq_of_heq hE
  exact A.map

theorem relabelMap_heq {Γ : Context.{u}} (A : Family Γ) {C D : Grpd.{u,u}}
    (hC : Γ.left = C) (hD : Γ.right = D)
    {B : C ⥤ Grpd.{u,u}} {E : D ⥤ Grpd.{u,u}}
    (hB : HEq A.left B) (hE : HEq A.right E) :
    HEq (A.relabelMap hC hD hB hE) A.map := by
  subst C; subst D
  cases eq_of_heq hB; cases eq_of_heq hE
  rfl

end Family

theorem Section.relabel_commutes {Γ : Context.{u}} {A : Family Γ} (s : Section A)
    {C D : Grpd.{u,u}} (hC : Γ.left = C) (hD : Γ.right = D)
    {B : C ⥤ Grpd.{u,u}} {E : D ⥤ Grpd.{u,u}}
    (hB : HEq A.left B) (hE : HEq A.right E)
    {l : ULift.{u+1} (GroupoidModel.Section B)} {r : ULift.{u+1} (GroupoidModel.Section E)}
    (hl : HEq (ULift.up.{u+1} s.left) l) (hr : HEq (ULift.up.{u+1} s.right) r) :
    l.down.familyImage (A.relabelMap hC hD hB hE) = r.down.reindex (Γ.relabel hC hD) := by
  subst C; subst D
  cases eq_of_heq hB; cases eq_of_heq hE
  cases eq_of_heq hl; cases eq_of_heq hr
  exact s.commutes

theorem Substitution.relabel_commutes {Γ Δ : Context.{u}} (σ : Substitution Δ Γ)
    {C D E F : Grpd.{u,u}} (hC : Γ.left = C) (hD : Γ.right = D)
    (hE : Δ.left = E) (hF : Δ.right = F)
    {l : ULift.{u+1} (E ⥤ C)} {r : ULift.{u+1} (F ⥤ D)}
    (hl : HEq (ULift.up.{u+1} σ.left) l) (hr : HEq (ULift.up.{u+1} σ.right) r) :
    l.down ⋙ Γ.relabel hC hD = Δ.relabel hE hF ⋙ r.down := by
  subst C; subst D; subst E; subst F
  cases eq_of_heq hl; cases eq_of_heq hr
  exact σ.commutes

variable (S : Signature.{u})
local notation "M" => fullModel S
local notation "L" => Instance.fullModel S.base.left S.leftFiber
local notation "R" => Instance.fullModel S.base.right S.rightFiber

/-- Restriction between the two interpretations of the very same context code. -/
def generatedContextMap (h : Typed.CtxDeriv.{u+1} Γ γ) : (show Grpd.{u,u} from γ L) ⥤ (show Grpd.{u,u} from γ R) :=
  (γ M).relabel ((leftSignatureMap S).generatedCtx h) ((rightSignatureMap S).generatedCtx h)

/-- The corresponding family comparison uses the very same generated family
code; no choice of a new endpoint interpretation is involved. -/
def generatedFamilyMap (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (h : Typed.TyDeriv.{u+1} Γ γ A a) :
    (show (show Grpd.{u,u} from γ L) ⥤ Grpd.{u,u} from a L) ⟶
      generatedContextMap S hΓ ⋙ (show (show Grpd.{u,u} from γ R) ⥤ Grpd.{u,u} from a R) :=
  (a M).relabelMap ((leftSignatureMap S).generatedCtx hΓ)
    ((rightSignatureMap S).generatedCtx hΓ)
    ((leftSignatureMap S).generatedTy h).2 ((rightSignatureMap S).generatedTy h).2

/-- Every generated term respects the extracted restriction on whole sections.
This includes contextual J and conversion through generic preservation. -/
theorem generatedTerm_commutes (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ A a) (h : Typed.TmDeriv.{u+1} Γ γ A a t x) :
    (x L).down.familyImage (generatedFamilyMap S hΓ hA) =
      (x R).down.reindex (generatedContextMap S hΓ) :=
  (x M).relabel_commutes ((leftSignatureMap S).generatedCtx hΓ)
    ((rightSignatureMap S).generatedCtx hΓ)
    ((leftSignatureMap S).generatedTy hA).2 ((rightSignatureMap S).generatedTy hA).2
    ((leftSignatureMap S).generatedTm h).2 ((rightSignatureMap S).generatedTm h).2

/-- Every generated substitution gives a commuting square of whole functors. -/
theorem generatedSubstitution_commutes (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hΔ : Typed.CtxDeriv.{u+1} Δ δ) (h : Typed.SubDeriv.{u+1} Δ δ Γ γ σ s) :
    (s L).down ⋙ generatedContextMap S hΓ = generatedContextMap S hΔ ⋙ (s R).down :=
  (s M).relabel_commutes ((leftSignatureMap S).generatedCtx hΓ)
    ((rightSignatureMap S).generatedCtx hΓ) ((leftSignatureMap S).generatedCtx hΔ)
    ((rightSignatureMap S).generatedCtx hΔ)
    ((leftSignatureMap S).generatedSub h).2.2 ((rightSignatureMap S).generatedSub h).2.2

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
