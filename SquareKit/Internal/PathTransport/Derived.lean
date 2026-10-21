import SquareKit.Internal.PathTransport.Endpoints

/-! Operations derived by source path induction. The transport definition follows
agda-unimath's `tr` at revision 75518656f287c203b41cb7f71df46e02b987a084.
See docs/research/agda-transfer-source-notice.md for correspondence and MIT notice. -/
namespace SquareKit.Internal.PathTransport.Typed.Authoring
open SquareKit.Internal.PathTransport
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def moving (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) :
    BasePoint (pathCtx Γ .base x.raw) (pathCode (baseCode γ) x.code) :=
  (BasePoint.variable hΓ).reindex
    (.weaken (.ext hΓ (.base hΓ)) (.pathFamily hΓ (.base hΓ) x.deriv))

def pathProjection (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) :=
  SubDeriv.comp (.weaken hΓ (.base hΓ))
    (.weaken (.ext hΓ (.base hΓ)) (.pathFamily hΓ (.base hΓ) x.deriv))

theorem subTm_cast_eval {γ δ : CtxCode} {a b : TyCode γ} (h : a = b)
    (ξ : TmCode γ a) (s : SubCode δ γ) (M : Model) :
    HEq (M.subTm (castCode h ξ M) (s M)) (M.subTm (ξ M) (s M)) := by cases h; rfl

theorem subTm_substitution_heq (M : Model) {Γ Δ : M.Context} {A : M.Family Γ}
    (t : M.Section Γ A) {s r : M.Substitution Δ Γ} (h : s = r) :
    HEq (M.subTm t s) (M.subTm t r) := by cases h; rfl

theorem moving_at (hΓ : CtxDeriv Γ γ) (x y : BasePoint Γ γ) (p : Path x y) :
    ((moving hΓ x).reindex (.endpoint hΓ (.base hΓ) x.deriv y.deriv p.deriv)).code = y.code := by
  funext M
  apply eq_of_heq
  apply (castCode_eval _ _ M).trans
  apply (subTm_cast_eval _ _ _ M).trans
  apply (M.subTm_comp _ _ _).trans
  apply (subTm_substitution_heq M _ (M.weaken_pair _ _ _)).trans
  exact (subTm_cast_eval _ _ _ M).trans
    ((M.variable_pair _ _ _).trans (castCode_eval _ _ M))

def transportMotive (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) :=
  TyDeriv.fiber (moving hΓ x).deriv

theorem transportMotive_at (hΓ : CtxDeriv Γ γ) (x y : BasePoint Γ γ) (p : Path x y) :
    subTyCode (fiberCode (moving hΓ x).code) (endpointCode (baseCode γ) x.code y.code p.code) =
      fiberCode y.code :=
  (fiberSub_code _ _).trans (congrArg fiberCode (moving_at hΓ x y p))

theorem transportMotive_root (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) :
    subTyCode (fiberCode (moving hΓ x).code) (rootCode (baseCode γ) x.code) = fiberCode x.code := by
  simpa only [Path.reflexivity, endpointCode_root] using
    transportMotive_at hΓ x x (Path.reflexivity hΓ x)

/-- The branch is the supplied fiber element, with its exact raw type retained. -/
def transportBranch (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) (b : FiberElement x) :
    TmDeriv Γ γ (.fiber x.raw)
      (subTyCode (fiberCode (moving hΓ x).code) (rootCode (baseCode γ) x.code))
      b.raw (castCode (transportMotive_root hΓ x).symm b.code) :=
  b.deriv.annotateType (transportMotive_root hΓ x).symm

def transportCommand (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) (b : FiberElement x) :
    @PathCommand Γ γ .base x.raw (baseCode γ) x.code 0 [] (telNil (pathCode (baseCode γ) x.code)) :=
  { context := hΓ
    type := .base hΓ
    point := x.deriv
    telescope := .nil (.path hΓ (.base hΓ) x.deriv)
    motive :=
      { raw := .fiber (.var 1)
        code := fiberCode (moving hΓ x).code
        typing := transportMotive hΓ x
        branch := b.raw
        branchCode := _
        branchTyping := transportBranch hΓ x b } }

/-- Transport is a generated J term. The source branch is the original element. -/
def transport (hΓ : CtxDeriv Γ γ) {x y : BasePoint Γ γ}
    (p : Path x y) (b : FiberElement x) : FiberElement y := by
  let cmd := transportCommand hΓ x b
  let endpoint := SubDeriv.endpoint hΓ (.base hΓ) x.deriv y.deriv p.deriv
  let hs := SubDeriv.rawTransport (argsSub_zero (genericArguments 0) _).symm endpoint
  let t := cmd.motive.pathInduction hΓ (.base hΓ) x.deriv cmd.telescope y.deriv p.deriv hs
  have hraw : (Expr.fiber (.var 1)).sub (eliminationSub y.raw p.raw (genericArguments 0)) =
      .fiber y.raw := by simp only [eliminationSub, argsSub_zero, Expr.sub, consSub]
  exact ⟨_, _, (t.rawType hraw).annotateType (transportMotive_at hΓ x y p)⟩

/-- Judgmental computation is inherited from the generated contextual beta rule. -/
def transport_beta (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) (b : FiberElement x) :
    TmEqDeriv Γ γ (.fiber x.raw) (fiberCode x.code)
      (transport hΓ (Path.reflexivity hΓ x) b).raw
      (transport hΓ (Path.reflexivity hΓ x) b).code b.raw b.code := by
  let cmd := transportCommand hΓ x b
  let hs := SubDeriv.rawTransport (argsSub_zero (genericArguments 0) Expr.var).symm (SubDeriv.id hΓ)
  have e := TmEqDeriv.contextualBeta hΓ (.base hΓ) x.deriv cmd.telescope
    cmd.motive.typing cmd.motive.branchTyping hs
  simp only [argsSub_zero, Expr.sub_id] at e
  have hcomp : compCode (rootCode (baseCode γ) x.code) (idCode γ) =
      endpointCode (baseCode γ) x.code x.code (reflCode (baseCode γ) x.code) :=
    (funext fun M => M.comp_id_right _).trans (endpointCode_root _ _).symm
  have hty := (congrArg (subTyCode (fiberCode (moving hΓ x).code)) hcomp).trans
    (transportMotive_at hΓ x x (Path.reflexivity hΓ x))
  apply (e.annotateType hty).annotate
  · apply eq_of_heq
    exact (castCode_heq _ _).trans ((subTmCode_substitution_heq _ hcomp).trans (castCode_heq _ _).symm)
  · apply eq_of_heq
    exact (castCode_heq _ _).trans ((castCode_heq _ _).trans
      ((subTmId_heq _).trans (castCode_heq _ _)))

end SquareKit.Internal.PathTransport.Typed.Authoring
