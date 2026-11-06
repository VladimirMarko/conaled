import SquareKit.Internal.DependentJudgments.ReferenceCalculus
import SquareKit.Internal.DependentJudgments.FiniteJNaturality

/-! Forward derivability into the explicitly extended telescope presentation.
No reflection from arbitrary guarded proofs is asserted. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory TelescopePresentation
set_option backward.isDefEq.respectTransparency false
variable {V : Type}

def Boundary.encode : Boundary V → Expression V → Judgment V
  | .ctx, Γ => context Γ
  | .ty Γ, A => family Γ A
  | .tm Γ A, t => term Γ A t
  | .sub Δ Γ, σ => substitution Δ Γ σ
  | .tel n Γ, T => telescope n Γ T

def Declaration.encode : Declaration V → Judgment V
  | .family Γ A => Contextual.family Γ A
  | .term Γ A t => Contextual.term Γ A t
  | .familyEq _ A B => .eq A B
  | .termEq _ _ s t => .eq s t

def Realizes (Ξ : List (Declaration V)) : Claim V → Type
  | .has b t => Target (Ω := Ξ.map Declaration.encode) (b.encode t)
  | .eq _ s t => Target (Ω := Ξ.map Declaration.encode) (.eq s t)
  | .tail Γ T => Presented (Ξ.map Declaration.encode) Γ T

variable {Ξ : List (Declaration V)} {Ω : List (Judgment V)}

private def originalRule (a : Contextual.Axiom)
    (θ : Fin (Contextual.rule a).parameterCount → Expression V)
    (h : ∀ i, Derivation Contextual.theory Ω (((Contextual.rule a).premise i).subst θ)) :
    Derivation Contextual.theory Ω ((Contextual.rule a).conclusion.subst θ) :=
  Derivation.rule (T := Contextual.theory) (Sum.inr a) θ h

private def reflSubProof {Γ Δ A x σ : Expression V}
    (hx : Tm (Ω := Ω) Γ A x) (hs : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (reflexivity A x) σ)
      (reflexivity (subTy A σ) (subTm x σ)) := by
  have r := originalRule (Ω := Ω) .reflSub ![Γ, Δ, A, x, σ]
    (Fin.cases (by simpa [Contextual.rule] using hx)
      (Fin.cases (by simpa [Contextual.rule] using hs) (fun i => nomatch i)))
  simpa [Contextual.rule] using r

/-- Every reference derivation has a guarded derivation in the named finite-tail
extension. The reference inference relation is not defined through this map. -/
noncomputable def translate {c : Claim V} (h : Derives Ξ c) : Realizes Ξ c := by
  induction h <;> dsimp only [Realizes, Boundary.encode] at *
  case empty => exact embed Ctx.empty
  case extend _ ih => refine unary ?_ ih; exact Ty.extend (.hypothesis List.mem_cons_self)
  case familyDecl hm _ _ => exact .hypothesis (List.mem_map.mpr ⟨_, hm, rfl⟩)
  case termDecl hm _ _ => exact .hypothesis (List.mem_map.mpr ⟨_, hm, rfl⟩)
  case typeContext _ ih => refine unary ?_ ih; exact Ty.context (.hypothesis List.mem_cons_self)
  case termFamily _ ih => refine unary ?_ ih; exact Tm.family (.hypothesis List.mem_cons_self)
  case subTy _ _ ihA ihσ => refine binary ?_ ihA ihσ; exact Ty.substitute (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  case subTm _ _ iht ihσ => refine binary ?_ iht ihσ; exact Tm.substitute (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  case identitySub _ ih => refine unary ?_ ih; exact Ctx.identity (.hypothesis List.mem_cons_self)
  case comp _ _ ihσ ihτ => refine binary ?_ ihσ ihτ; exact Sub.comp (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  case weaken _ ih => refine unary ?_ ih; exact Ty.weaken (.hypothesis List.mem_cons_self)
  case generic _ ih => refine unary ?_ ih; exact Ty.generic (.hypothesis List.mem_cons_self)
  case pair _ _ _ ihA ihσ iht => refine ternary ?_ ihA ihσ iht; exact Sub.pair (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  case identity _ _ ihx ihy => refine binary ?_ ihx ihy; exact Tm.identity (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  case reflexivity _ ih => refine unary ?_ ih; exact Tm.reflexivity (.hypothesis List.mem_cons_self)
  case path _ ih => refine unary ?_ ih; exact Tm.path (.hypothesis List.mem_cons_self)
  case root _ ih => refine unary ?_ ih; exact Tm.root (.hypothesis List.mem_cons_self)
  case pathSub _ _ ihx ihσ =>
    refine binary ?_ ihx ihσ
    exact Tm.pathSub (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  case nil _ ih => exact Presented.nil ih
  case cons _ _ ihA ihT => exact Presented.cons ihA ihT
  case tailCode _ ih => exact ih.typing
  case contextConvertTel _ _ ih ie =>
    exact Derivation.conversion (T := TelescopePresentation.theory) (.inr (.telescope _))
      (Fin.cases ie (Fin.cases (.reflexive _) (fun i => nomatch i))) ih
  case tailTotal _ ih =>
    have ht := unary (Tel.total (.hypothesis List.mem_cons_self)) ih.typing
    exact Derivation.conversion (T := TelescopePresentation.theory) (.inl .context)
      (Fin.cases ih.total_eq (fun i => nomatch i)) ht
  case branchMap _ _ _ _ _ ihx ihT ihσ _ _ => exact translateBranchMap ihx ihT ihσ
  case branchSquare _ _ _ _ _ ihx ihT ihσ _ _ => exact translateBranchSquare ihx ihT ihσ
  case jSub _ _ _ _ _ _ _ ihx ihT ihD ihd ihσ _ _ => exact translateJSub ihx ihT ihD ihd ihσ
  case j _ _ _ _ ihx ihT ihD ihd => exact translateJ ihx ihT ihD ihd
  case jBeta _ _ _ _ _ ihx ihT ihD ihd _ => exact translateJBeta ihx ihT ihD ihd
  case convert _ _ iht ihe => refine binary ?_ iht ihe; exact Tm.convert (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  case contextConvertType _ _ ih ie =>
    exact Derivation.conversion (T := TelescopePresentation.theory) (.inl .family)
      (Fin.cases ie (Fin.cases (.reflexive _) (fun i => nomatch i))) ih
  case contextConvertTerm _ _ ih ie =>
    exact Derivation.conversion (T := TelescopePresentation.theory) (.inl .term)
      (Fin.cases ie (Fin.cases (.reflexive _) (Fin.cases (.reflexive _) (fun i => nomatch i)))) ih
  case contextConvertSub _ _ _ ih ieΔ ieΓ =>
    exact Derivation.conversion (T := TelescopePresentation.theory) (.inl .substitution)
      (Fin.cases ieΔ (Fin.cases ieΓ (Fin.cases (.reflexive _) (fun i => nomatch i)))) ih
  case pathDef _ ih => refine unary ?_ ih; exact Tm.pathDef (.hypothesis List.mem_cons_self)
  case rootDef _ _ ih _ => refine unary ?_ ih; exact Tm.rootDef (.hypothesis List.mem_cons_self)
  case pairEta _ _ _ ihA ihσ _ =>
    refine binary ?_ ihA ihσ
    exact Ty.pairEta (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  case familyEqDecl hm _ _ _ _ => exact .hypothesis (List.mem_map.mpr ⟨_, hm, rfl⟩)
  case termEqDecl hm _ _ _ _ => exact .hypothesis (List.mem_map.mpr ⟨_, hm, rfl⟩)
  case pairComp _ _ _ _ ihA ihσ iht ihτ =>
    refine quaternary ?_ ihA ihσ iht ihτ
    exact Ty.pairComp (.hypothesis List.mem_cons_self)
      (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
      (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  case subTyId _ ih0 => refine unary ?_ ih0; exact Ty.subId (.hypothesis List.mem_cons_self)
  case subTyComp _ _ _ ih0 ih1 ih2 => refine ternary ?_ ih0 ih1 ih2; exact Ty.subComp (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  case subTmId _ ih0 => refine unary ?_ ih0; exact Tm.subId (.hypothesis List.mem_cons_self)
  case subTmComp _ _ _ ih0 ih1 ih2 => refine ternary ?_ ih0 ih1 ih2; exact Tm.subComp (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  case subIdLeft _ ih0 => refine unary ?_ ih0; exact Sub.idLeft (.hypothesis List.mem_cons_self)
  case subIdRight _ ih0 => refine unary ?_ ih0; exact Sub.idRight (.hypothesis List.mem_cons_self)
  case subAssoc _ _ _ ih0 ih1 ih2 => refine ternary ?_ ih0 ih1 ih2; exact Sub.assoc (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  case weakenPair _ _ _ ih0 ih1 ih2 => refine ternary ?_ ih0 ih1 ih2; exact Ty.weakenPair (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  case genericPair _ _ _ _ ih0 ih1 ih2 ih3 => refine ternary ?_ ih0 ih1 ih2; exact Ty.variablePair (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  case identitySubLaw _ _ _ ih0 ih1 ih2 => refine ternary ?_ ih0 ih1 ih2; exact Tm.identitySub (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  case reflexivitySubLaw _ _ ih0 ih1 => refine binary ?_ ih0 ih1; exact reflSubProof (.hypothesis List.mem_cons_self) (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  case eqRefl => exact .reflexive _
  case eqSymm _ ih => exact .symmetric ih
  case eqTrans _ _ ih ih' => exact .transitive ih ih'
  case congruence => apply Derivation.congruence; assumption

end SquareKit.Internal.DependentJudgments.Contextual.Reference
