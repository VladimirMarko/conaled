import SquareKit.Internal.PathTransport.GeneratedHorizontalEndpoints
import SquareKit.Internal.PathTransport.ComparisonTelescopeComposition

/-! Horizontal composition for all supported generated judgments, including
contextual J, dependent reindexing and conversion. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.GeneratedComposition
open CategoryTheory Typed Typed.StructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (S T : Signature.{u}) (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber)
local notation "L" => fullModel S
local notation "R" => fullModel T
local notation "N" => fullModel (S.horizontal T h hB)

def CtxPres (γ : CtxCode.{u+1}) : Prop := (γ L).Composes (γ R) (γ N)
def TyPres {γ : CtxCode.{u+1}} (a : TyCode γ) : Prop := (a L).Composes (a R) (a N)
def SubPres {δ γ : CtxCode.{u+1}} (_s : SubCode δ γ) : Prop :=
  CtxPres S T h hB δ ∧ CtxPres S T h hB γ
def TelPres {γ : CtxCode.{u+1}} {n} (Ts : TelCode γ n) : Prop :=
  TelescopeComposes S T (S.horizontal T h hB) (Ts L) (Ts R) (Ts N)

private def sourceContext (hs : SubDeriv.{u+1} Δ δ Γ γ σ s) : CtxDeriv Δ δ :=
  match hs with
  | .id hΓ => hΓ
  | .comp _ ht => sourceContext ht
  | .weaken hΓ hA => .ext hΓ hA
  | .projection hΓ hT => .telescope hΓ hT
  | .root hΓ _ _ => hΓ
  | .rootTail hΓ hA hx hT => .branch hΓ hA hx hT
  | .pathTailMap hΓ hA hx hT hs =>
      .telescope (.path (sourceContext hs) (.sub hA hs) (.sub hx hs))
        (.pathReindex hΓ hA hx hT hs)
  | .pair _ hs _ => sourceContext hs
termination_by sizeOf hs

private theorem section_pres (hx : TmDeriv Γ γ A a t x) (ha : TyPres S T h hB a) :
    (x L).Composes (x R) (x N) := generated_section_composes S T h hB hx ha

private theorem substitution_pres (hs : SubDeriv Δ δ Γ γ σ s) (hh : SubPres S T h hB s) :
    (s L).Composes (s R) (s N) := generated_substitution_composes S T h hB hs hh.2 hh.1

private theorem path_pres {γ : CtxCode.{u+1}} {a : TyCode γ} {x : TmCode γ a}
    (hx : (x L).Composes (x R) (x N)) : CtxPres S T h hB (pathCode a x) :=
  ((hx.reindex hx.family.weaken).identity hx.family.variable).extend

private theorem root_pres (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a)
    (hx : TmDeriv Γ γ A a t x) (ha : TyPres S T h hB a) :
    (rootCode a x L).Composes (rootCode a x R) (rootCode a x N) :=
  generated_substitution_composes S T h hB (.root hΓ hA hx)
    (path_pres S T h hB (section_pres S T h hB hx ha)) ha.context

private theorem branch_pres (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a)
    (hx : TmDeriv Γ γ A a t x)
    {n Δ Ts} (_hT : TelDeriv (pathCtx Γ A t) (pathCode a x) n Δ Ts)
    (ha : TyPres S T h hB a) (ht : TelPres S T h hB Ts) :
    CtxPres S T h hB (branchCode a x Ts) :=
  (ht.pullback (root_pres S T h hB hΓ hA hx ha)).total

private theorem pathTail_pres (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a)
    (hx : TmDeriv Γ γ A a t x)
    {n Δ Ts} (_hT : TelDeriv (pathCtx Γ A t) (pathCode a x) n Δ Ts)
    (hs : SubDeriv Ω ω Γ γ σ s)
    (ha : TyPres S T h hB a) (ht : TelPres S T h hB Ts) (hh : SubPres S T h hB s) :
    TelPres S T h hB (pathTailCode a x Ts s) := by
  have hsub := substitution_pres S T h hB hs hh
  have hsection := section_pres S T h hB hx ha
  have hpath := generated_substitution_composes S T h hB
    (SubDeriv.pathTailMap hΓ hA hx (.nil (.path hΓ hA hx)) hs)
    (path_pres S T h hB hsection) (path_pres S T h hB (hsection.reindex hsub))
  exact ht.pullback hpath

private theorem reindexBranch_pres (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a)
    (hx : TmDeriv Γ γ A a t x)
    {n Δ Ts} (hT : TelDeriv (pathCtx Γ A t) (pathCode a x) n Δ Ts)
    {C c} (_hc : TyDeriv (Δ ++ pathCtx Γ A t) (telTotal Ts) C c)
    (hs : SubDeriv Ω ω Γ γ σ s)
    (ha : TyPres S T h hB a) (ht : TelPres S T h hB Ts)
    (hc : TyPres S T h hB c) (hh : SubPres S T h hB s) :
    TyPres S T h hB (subTyCode (subTyCode c (pathTailMapCode a x Ts s))
      (rootTailCode (subTyCode a s) (subTmCode x s) (pathTailCode a x Ts s))) := by
  have ht' := pathTail_pres S T h hB hΓ hA hx hT hs ha ht hh
  have ha' := ha.reindex (substitution_pres S T h hB hs hh)
  have hmap := generated_substitution_composes S T h hB (.pathTailMap hΓ hA hx hT hs)
    ht.total ht'.total
  have hroot := generated_substitution_composes S T h hB
    (.rootTail (sourceContext hs) (.sub hA hs) (.sub hx hs) (.pathReindex hΓ hA hx hT hs))
    ht'.total
    (branch_pres S T h hB (sourceContext hs) (.sub hA hs) (.sub hx hs)
      (.pathReindex hΓ hA hx hT hs) ha' ht')
  exact (hc.reindex hmap).reindex hroot

private theorem cast_pres {γ : CtxCode.{u+1}} {a b : TyCode γ} (e : a = b)
    (ha : TyPres S T h hB a) : TyPres S T h hB b := by
  cases e; exact ha

mutual

theorem generatedCtx (deriv : CtxDeriv.{u+1} Γ γ) : CtxPres S T h hB γ :=
  match deriv with
  | .empty => ⟨rfl, rfl⟩
  | .ext _ ha => (generatedTy ha).extend
  | .path _ _ hx => path_pres S T h hB (section_pres S T h hB hx (generatedTmType hx))
  | .telescope _ ht => (generatedTel ht).total
  | .branch hΓ ha hx ht => branch_pres S T h hB hΓ ha hx ht (generatedTmType hx) (generatedTel ht)
termination_by sizeOf deriv

theorem generatedTel (deriv : TelDeriv.{u+1} Γ γ n Δ Ts) : TelPres S T h hB Ts :=
  match deriv with
  | .nil hΓ => .nil (generatedCtx hΓ)
  | .cons ha ht => .cons (generatedTy ha) (generatedTel ht)
  | .pullback ht hs => (generatedTel ht).pullback (substitution_pres S T h hB hs (generatedSubContexts hs))
  | .pathReindex hΓ ha hx ht hs =>
      pathTail_pres S T h hB hΓ ha hx ht hs (generatedTmType hx) (generatedTel ht) (generatedSubContexts hs)
termination_by sizeOf deriv

theorem generatedTy (deriv : TyDeriv.{u+1} Γ γ A a) : TyPres S T h hB a :=
  match deriv with
  | .base hΓ => S.baseFamily_composes T h hB (generatedCtx hΓ)
  | .fiber hx => S.fiber_composes T h hB (section_pres S T h hB hx (generatedTmType hx))
  | .identity _ hx hy =>
      (section_pres S T h hB hx (generatedTmType hx)).identity (section_pres S T h hB hy (generatedTmType hy))
  | .sub ha hs => (generatedTy ha).reindex (substitution_pres S T h hB hs (generatedSubContexts hs))
termination_by sizeOf deriv

/-- The family invariant for every generated term; the full section relation
then follows from the already-proved generated endpoint preservation. -/
theorem generatedTmType (deriv : TmDeriv.{u+1} Γ γ A a t x) : TyPres S T h hB a :=
  match deriv with
  | .var _ ha => (generatedTy ha).reindex (generatedTy ha).weaken
  | .refl _ hx =>
      (section_pres S T h hB hx (generatedTmType hx)).identity (section_pres S T h hB hx (generatedTmType hx))
  | .sub hx hs => (generatedTmType hx).reindex (substitution_pres S T h hB hs (generatedSubContexts hs))
  | .pathInduction _ _ _ _ hc _ _ _ hs =>
      (generatedTy hc).reindex (substitution_pres S T h hB hs (generatedSubContexts hs))
  | .pathInductionReindex _ _ _ _ hc _ _ _ _ hs =>
      (generatedTy hc).reindex (substitution_pres S T h hB hs (generatedSubContexts hs))
  | .genericJ _ _ _ _ hc _ => generatedTy hc
  | .reindexJBranch hΓ ha hx ht hc _ hs =>
      reindexBranch_pres S T h hB hΓ ha hx ht hc hs
        (generatedTmType hx) (generatedTel ht) (generatedTy hc) (generatedSubContexts hs)
  | .conv hx _ e => cast_pres S T h hB e (generatedTmType hx)
termination_by sizeOf deriv

theorem generatedSubContexts (deriv : SubDeriv.{u+1} Δ δ Γ γ σ s) : SubPres S T h hB s :=
  match deriv with
  | .id hΓ => ⟨generatedCtx hΓ, generatedCtx hΓ⟩
  | .comp hs ht => ⟨(generatedSubContexts ht).1, (generatedSubContexts hs).2⟩
  | .weaken _ ha => ⟨(generatedTy ha).extend, (generatedTy ha).context⟩
  | .projection _ ht => ⟨(generatedTel ht).total, (generatedTel ht).context⟩
  | .root _ _ hx =>
      ⟨(generatedTmType hx).context, path_pres S T h hB (section_pres S T h hB hx (generatedTmType hx))⟩
  | .rootTail hΓ ha hx ht =>
      ⟨branch_pres S T h hB hΓ ha hx ht (generatedTmType hx) (generatedTel ht), (generatedTel ht).total⟩
  | .pathTailMap hΓ ha hx ht hs =>
      ⟨(pathTail_pres S T h hB hΓ ha hx ht hs (generatedTmType hx)
        (generatedTel ht) (generatedSubContexts hs)).total, (generatedTel ht).total⟩
  | .pair ha hs _ => ⟨(generatedSubContexts hs).1, (generatedTy ha).extend⟩
termination_by sizeOf deriv
end

theorem generatedTm (deriv : TmDeriv.{u+1} Γ γ A a t x) :
    (x L).Composes (x R) (x N) :=
  section_pres S T h hB deriv (generatedTmType S T h hB deriv)

theorem generatedSub (deriv : SubDeriv.{u+1} Δ δ Γ γ σ s) :
    (s L).Composes (s R) (s N) :=
  substitution_pres S T h hB deriv (generatedSubContexts S T h hB deriv)

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.GeneratedComposition
