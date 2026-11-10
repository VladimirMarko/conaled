import SquareKit.Internal.PathTransport.GeneratedComparisonRestriction
import SquareKit.Internal.PathTransport.ContractionModification

/-! The generated root/tail squares use exactly the native normalized
contractions and their selected counits. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory ContextualElimination Typed Typed.StructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

theorem Contraction.square_relabel {Γ Δ : Context.{u}} (e : Contraction Δ Γ)
    {CL CR DL DR : Grpd.{u,u}}
    (hCL : Γ.left = CL) (hCR : Γ.right = CR) (hDL : Δ.left = DL) (hDR : Δ.right = DR)
    (eL : NormalizedEquivalence (Cat.of DL) (Cat.of CL))
    (eR : NormalizedEquivalence (Cat.of DR) (Cat.of CR))
    (hl : HEq e.left eL) (hr : HEq e.right eR) :
    EquivalenceSquare.Square eR.equiv eL.equiv
      (Γ.relabel hCL hCR) (Δ.relabel hDL hDR) := by
  subst CL; subst CR; subst DL; subst DR
  cases eq_of_heq hl
  cases eq_of_heq hr
  exact e.square

private theorem rootTailEquivalence_heq (C : Grpd.{u,u}) (P : C ⥤ Type u)
    {Γ Δ : Grpd.{u,u}} (hΓ : Γ = Δ)
    {A : Γ ⥤ Grpd.{u,u}} {B : Δ ⥤ Grpd.{u,u}} (hA : HEq A B)
    {x : ULift.{u+1} (GroupoidModel.Section A)} {y : ULift.{u+1} (GroupoidModel.Section B)}
    (hx : HEq x y) {n}
    {T : Telescope (Instance.structuralModel C P)
      (pathContext (Instance.structuralModel C P) A x) n}
    {U : Telescope (Instance.structuralModel C P)
      (pathContext (Instance.structuralModel C P) B y) n}
    (hT : HEq T U) :
    HEq (Instance.rootTailEquivalence C P A x.down T)
      (Instance.rootTailEquivalence C P B y.down U) := by
  cases hΓ; cases eq_of_heq hA; cases eq_of_heq hx; cases eq_of_heq hT
  rfl

variable (S : Signature.{u})
local notation "M" => fullModel S
local notation "L" => Instance.fullModel S.base.left S.leftFiber
local notation "R" => Instance.fullModel S.base.right S.rightFiber

theorem generatedRootTail_left (hΓ : CtxDeriv.{u+1} Γ γ)
    (hA : TyDeriv.{u+1} Γ γ A a) (hx : TmDeriv.{u+1} Γ γ A a t x)
    (hT : TelDeriv.{u+1} (pathCtx Γ A t) (pathCode a x) n Δ T) :
    HEq (rootTail S (a M) (x M) (T M)).left
      (Instance.rootTailEquivalence S.base.left S.leftFiber (a L) (x L).down (T L)) :=
  (rootTail_left S _ _ _).trans
    (rootTailEquivalence_heq S.base.left S.leftFiber
      ((leftSignatureMap S).generatedCtx hΓ)
      ((leftSignatureMap S).generatedTy hA).2
      ((leftSignatureMap S).generatedTm hx).2
      ((cast_heq _ _).trans ((leftSignatureMap S).generatedTel hT).2))

theorem generatedRootTail_right (hΓ : CtxDeriv.{u+1} Γ γ)
    (hA : TyDeriv.{u+1} Γ γ A a) (hx : TmDeriv.{u+1} Γ γ A a t x)
    (hT : TelDeriv.{u+1} (pathCtx Γ A t) (pathCode a x) n Δ T) :
    HEq (rootTail S (a M) (x M) (T M)).right
      (Instance.rootTailEquivalence S.base.right S.rightFiber (a R) (x R).down (T R)) :=
  (rootTail_right S _ _ _).trans
    (rootTailEquivalence_heq S.base.right S.rightFiber
      ((rightSignatureMap S).generatedCtx hΓ)
      ((rightSignatureMap S).generatedTy hA).2
      ((rightSignatureMap S).generatedTm hx).2
      ((cast_heq _ _).trans ((rightSignatureMap S).generatedTel hT).2))

/-- Both native contractions, inverse functors and chosen counits are retained
through the same extracted generated comparison maps. -/
theorem generatedRootTail_square (hΓ : CtxDeriv.{u+1} Γ γ)
    (hA : TyDeriv.{u+1} Γ γ A a) (hx : TmDeriv.{u+1} Γ γ A a t x)
    (hT : TelDeriv.{u+1} (pathCtx Γ A t) (pathCode a x) n Δ T) :
    EquivalenceSquare.Square
      (Instance.rootTailEquivalence S.base.right S.rightFiber (a R) (x R).down (T R)).equiv
      (Instance.rootTailEquivalence S.base.left S.leftFiber (a L) (x L).down (T L)).equiv
      (generatedContextMap S (.telescope (.path hΓ hA hx) hT))
      (generatedContextMap S (.branch hΓ hA hx hT)) :=
  (rootTail S (a M) (x M) (T M)).square_relabel
    ((leftSignatureMap S).generatedCtx (.telescope (.path hΓ hA hx) hT))
    ((rightSignatureMap S).generatedCtx (.telescope (.path hΓ hA hx) hT))
    ((leftSignatureMap S).generatedCtx (.branch hΓ hA hx hT))
    ((rightSignatureMap S).generatedCtx (.branch hΓ hA hx hT)) _ _
    (generatedRootTail_left S hΓ hA hx hT) (generatedRootTail_right S hΓ hA hx hT)

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
