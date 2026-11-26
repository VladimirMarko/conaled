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

theorem generated_ctx (deriv : CtxDeriv.{u+1} Γ γ) : CtxPres S T h hB γ :=
  match deriv with
  | .empty => ⟨rfl, rfl⟩
  | .ext _ ha => (generated_ty ha).extend
  | .path _ _ hx => path_pres S T h hB (section_pres S T h hB hx (generated_tm_type hx))
  | .telescope _ ht => (generated_tel ht).total
  | .branch hΓ ha hx ht => branch_pres S T h hB hΓ ha hx ht (generated_tm_type hx) (generated_tel ht)
termination_by sizeOf deriv

theorem generated_tel (deriv : TelDeriv.{u+1} Γ γ n Δ Ts) : TelPres S T h hB Ts :=
  match deriv with
  | .nil hΓ => .nil (generated_ctx hΓ)
  | .cons ha ht => .cons (generated_ty ha) (generated_tel ht)
  | .pullback ht hs => (generated_tel ht).pullback (substitution_pres S T h hB hs (generated_sub_contexts hs))
  | .pathReindex hΓ ha hx ht hs =>
      pathTail_pres S T h hB hΓ ha hx ht hs (generated_tm_type hx) (generated_tel ht) (generated_sub_contexts hs)
termination_by sizeOf deriv

theorem generated_ty (deriv : TyDeriv.{u+1} Γ γ A a) : TyPres S T h hB a :=
  match deriv with
  | .base hΓ => S.baseFamily_composes T h hB (generated_ctx hΓ)
  | .fiber hx => S.fiber_composes T h hB (section_pres S T h hB hx (generated_tm_type hx))
  | .identity _ hx hy =>
      (section_pres S T h hB hx (generated_tm_type hx)).identity (section_pres S T h hB hy (generated_tm_type hy))
  | .sub ha hs => (generated_ty ha).reindex (substitution_pres S T h hB hs (generated_sub_contexts hs))
termination_by sizeOf deriv

/-- The family invariant for every generated term; the full section relation
then follows from the already-proved generated endpoint preservation. -/
theorem generated_tm_type (deriv : TmDeriv.{u+1} Γ γ A a t x) : TyPres S T h hB a :=
  match deriv with
  | .var _ ha => (generated_ty ha).reindex (generated_ty ha).weaken
  | .refl _ hx =>
      (section_pres S T h hB hx (generated_tm_type hx)).identity (section_pres S T h hB hx (generated_tm_type hx))
  | .sub hx hs => (generated_tm_type hx).reindex (substitution_pres S T h hB hs (generated_sub_contexts hs))
  | .pathInduction _ _ _ _ hc _ _ _ hs =>
      (generated_ty hc).reindex (substitution_pres S T h hB hs (generated_sub_contexts hs))
  | .pathInductionReindex _ _ _ _ hc _ _ _ _ hs =>
      (generated_ty hc).reindex (substitution_pres S T h hB hs (generated_sub_contexts hs))
  | .genericJ _ _ _ _ hc _ => generated_ty hc
  | .reindexJBranch hΓ ha hx ht hc _ hs =>
      reindexBranch_pres S T h hB hΓ ha hx ht hc hs
        (generated_tm_type hx) (generated_tel ht) (generated_ty hc) (generated_sub_contexts hs)
  | .conv hx _ e => cast_pres S T h hB e (generated_tm_type hx)
termination_by sizeOf deriv

theorem generated_sub_contexts (deriv : SubDeriv.{u+1} Δ δ Γ γ σ s) : SubPres S T h hB s :=
  match deriv with
  | .id hΓ => ⟨generated_ctx hΓ, generated_ctx hΓ⟩
  | .comp hs ht => ⟨(generated_sub_contexts ht).1, (generated_sub_contexts hs).2⟩
  | .weaken _ ha => ⟨(generated_ty ha).extend, (generated_ty ha).context⟩
  | .projection _ ht => ⟨(generated_tel ht).total, (generated_tel ht).context⟩
  | .root _ _ hx =>
      ⟨(generated_tm_type hx).context, path_pres S T h hB (section_pres S T h hB hx (generated_tm_type hx))⟩
  | .rootTail hΓ ha hx ht =>
      ⟨branch_pres S T h hB hΓ ha hx ht (generated_tm_type hx) (generated_tel ht), (generated_tel ht).total⟩
  | .pathTailMap hΓ ha hx ht hs =>
      ⟨(pathTail_pres S T h hB hΓ ha hx ht hs (generated_tm_type hx)
        (generated_tel ht) (generated_sub_contexts hs)).total, (generated_tel ht).total⟩
  | .pair ha hs _ => ⟨(generated_sub_contexts hs).1, (generated_ty ha).extend⟩
termination_by sizeOf deriv
end

theorem generated_tm (deriv : TmDeriv.{u+1} Γ γ A a t x) :
    (x L).Composes (x R) (x N) :=
  section_pres S T h hB deriv (generated_tm_type S T h hB deriv)

theorem generated_sub (deriv : SubDeriv.{u+1} Δ δ Γ γ σ s) :
    (s L).Composes (s R) (s N) :=
  substitution_pres S T h hB deriv (generated_sub_contexts S T h hB deriv)

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.GeneratedComposition
