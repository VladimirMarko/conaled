import SquareKit.Internal.DependentJudgments.PresentedElimination

/-! Reusable projection and section squares for finite dependent contexts.
The square is built by recursively lifting the supplied substitution. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation.Presented
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A t σ : Expression V} {T : Reference.Tail V}

/-- This projection is over the explicit total context used by an author. -/
def projection (hT : Reference.Presented Ω Γ T) : Sub (Ω := Ω) (T.total Γ) Γ (T.projection Γ) := by
  induction hT with
  | nil hΓ => exact Ctx.identity hΓ
  | cons hA _ ih => exact (Ty.weaken hA).comp ih

def map (hT : Reference.Presented Ω Γ T) (hΔ : Ctx (Ω := Ω) Δ) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Sub (Ω := Ω) ((T.reindex Δ σ).total Δ) (T.total Γ) (T.map Δ σ) := by
  induction hT generalizing Δ σ with
  | nil => exact hs
  | cons hA _ ih => exact ih ((Ty.substitute hA hs).extend) (hs.lift hA)

def square (hT : Reference.Presented Ω Γ T) (hΔ : Ctx (Ω := Ω) Δ) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (comp (T.projection Γ) (T.map Δ σ))
      (comp σ ((T.reindex Δ σ).projection Δ)) := by
  induction hT generalizing Δ σ with
  | nil => exact hs.idLeft.transitive hs.idRight.symmetric
  | @cons Γ A T hA hT ih =>
    have hB := Ty.substitute hA hs
    have hm := map hT hB.extend (hs.lift hA)
    have hp := projection (hT.reindex hB.extend (hs.lift hA))
    exact (((Ty.weaken hA).assoc (projection hT) hm).transitive
      (Equal.comp (.reflexive _) (ih hB.extend (hs.lift hA)))).transitive
      (((Ty.weaken hA).assoc (hs.lift hA) hp).symmetric.transitive
        ((Equal.comp (hs.liftWeaken hA) (.reflexive _)).transitive
          (hs.assoc hB.weaken hp)))

def termSquare (hT : Reference.Presented Ω Γ T) (ht : Tm (Ω := Ω) Γ A t)
    (hΔ : Ctx (Ω := Ω) Δ) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (subTm t (T.projection Γ)) (T.map Δ σ))
      (subTm (subTm t σ) ((T.reindex Δ σ).projection Δ)) :=
  (ht.subComp (projection hT) (map hT hΔ hs)).transitive
    ((Equal.subTm (.reflexive _) (square hT hΔ hs)).transitive
      (ht.subComp hs (projection (hT.reindex hΔ hs))).symmetric)

def typeSquare (hT : Reference.Presented Ω Γ T) (hA : Ty (Ω := Ω) Γ A)
    (hΔ : Ctx (Ω := Ω) Δ) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTy (subTy A (T.projection Γ)) (T.map Δ σ))
      (subTy (subTy A σ) ((T.reindex Δ σ).projection Δ)) :=
  (hA.subComp (projection hT) (map hT hΔ hs)).transitive
    ((Equal.subTy (.reflexive _) (square hT hΔ hs)).transitive
      (hA.subComp hs (projection (hT.reindex hΔ hs))).symmetric)
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation.Presented
