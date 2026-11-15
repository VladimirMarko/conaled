import SquareKit.Internal.DependentJudgments.LiftFunctoriality
/-! The original path transport restricted to fixed endpoints in source syntax. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ F s σ A x y : Expression V}
abbrev pathTransportTerm (Γ A x : Expression V) :=
 transportGeneric Γ A (pathFamily Γ A x) x (reflexivity A x)
abbrev fixedPathTransportTerm (Γ A x y : Expression V) :=
 subTm (pathTransportTerm Γ A x) (lift Γ (pathFamily Γ A x) (sectionSub Γ A y))
def Tm.reindexEndomap (hF : Ty (Ω := Ω) Γ F)
 (hs : Tm (Ω := Ω) (Contextual.extend Γ F) (Contextual.subTy F (Contextual.weaken Γ F)) s)
 (hσ : Sub (Ω := Ω) Δ Γ σ) :
 Tm (Ω := Ω) (Contextual.extend Δ (Contextual.subTy F σ))
 (Contextual.subTy (Contextual.subTy F σ) (Contextual.weaken Δ (Contextual.subTy F σ)))
 (Contextual.subTm s (Contextual.lift Δ F σ)) :=
 (hs.substitute (hσ.lift hF)).convert
 (((hF.subComp hF.weaken (hσ.lift hF)).transitive
  (Equal.subTy (.reflexive _) (hσ.liftWeaken hF))).transitive
  (hF.subComp hσ (hF.substitute hσ).weaken).symmetric)
def Tm.pathTransportTerm (hx : Tm (Ω := Ω) Γ A x) :
 Tm (Ω := Ω) (Contextual.path A x)
 (Contextual.transportMotive Γ A (Contextual.pathFamily Γ A x) x)
 (Contextual.pathTransportTerm Γ A x) :=
 Tm.transportGeneric hx.pathFamily hx (hx.reflexivity.convert (hx.pathFamilySection hx).symmetric)
def Tm.fixedPathTransportTerm (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y) :
 Tm (Ω := Ω) (Contextual.extend Γ (Contextual.identity A x y))
 (Contextual.subTy (Contextual.identity A x y) (Contextual.weaken Γ (Contextual.identity A x y)))
 (Contextual.fixedPathTransportTerm Γ A x y) :=
 ((Tm.reindexEndomap hx.pathFamily ((Tm.pathTransportTerm hx).recontext hx.pathDef) hy.section).recontext
  (Equal.extend (.reflexive _) (hx.pathFamilySection hy))).convert
  (Equal.subTy (hx.pathFamilySection hy) (Equal.weaken (.reflexive _) (hx.pathFamilySection hy)))
end SquareKit.Internal.DependentJudgments.Contextual
