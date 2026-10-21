import SquareKit.Internal.PathTransport.Typed

/-! Named author operations and a checked dependent-tail path-induction case.
The retained caller uses source derivations for reflexive computation and
rebuilding J after context substitution. -/

namespace SquareKit.Internal.PathTransport.Typed.Authoring
open SquareKit.Internal.PathTransport
universe u

/-- A named base point includes its source derivation. -/
structure BasePoint (Γ : RawCtx) (γ : CtxCode.{u}) where
  raw : Expr
  code : TmCode γ (baseCode γ)
  deriv : TmDeriv Γ γ .base (baseCode γ) raw code

def BasePoint.variable (hΓ : CtxDeriv Γ γ) :
    BasePoint (.base :: Γ) (extendCode γ (baseCode γ)) where
  raw := .var 0
  code := castCode (baseSub_code (weakenCode γ (baseCode γ))) (varCode γ (baseCode γ))
  deriv := (TmDeriv.var hΓ (.base hΓ)).convert (.baseSub (.weaken hΓ (.base hΓ)))

def BasePoint.weaken (x : BasePoint Γ γ) (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) :
    BasePoint (A :: Γ) (extendCode γ a) where
  raw := x.raw.sub (Expr.var ∘ Nat.succ)
  code := castCode (baseSub_code (weakenCode γ a)) (subTmCode x.code (weakenCode γ a))
  deriv := (TmDeriv.sub x.deriv (.weaken hΓ hA)).convert (.baseSub (.weaken hΓ hA))

/-- Source motive and reflexive branch for a generalized path-induction command. -/
structure Motive {Γ : RawCtx} {γ : CtxCode.{u}} {A x : Expr} {a : TyCode γ}
    {ξ : TmCode γ a} {n : Nat} {Δ : RawCtx} (T : TelCode (pathCode a ξ) n) where
  raw : Expr
  code : TyCode (telTotal T)
  typing : TyDeriv (Δ ++ pathCtx Γ A x) (telTotal T) raw code
  branch : Expr
  branchCode : TmCode (SquareKit.Internal.PathTransport.Typed.branchCode a ξ T) (subTyCode code (rootTailCode a ξ T))
  branchTyping : TmDeriv (subTail (reflexiveSub x) Δ ++ Γ) (SquareKit.Internal.PathTransport.Typed.branchCode a ξ T)
    (raw.sub (Expr.liftSubN n (reflexiveSub x))) (subTyCode code (rootTailCode a ξ T)) branch branchCode

def Motive.reflexivity
    (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) (hx : TmDeriv Γ γ A a x ξ)
    (hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T)
    (hQ : TyDeriv (Δ ++ pathCtx Γ A x) (telTotal T) Q q)
    (hp : TmDeriv (Δ ++ pathCtx Γ A x) (telTotal T) Q q p π) :
    @Motive Γ γ A x a ξ n Δ T := by
  let root := SubDeriv.rootTail hΓ hA hx hT
  let branch := (TmDeriv.refl (.sub hQ root) (.sub hp root)).convert
    (.symm (.identitySub hQ hp hp root))
  exact ⟨.identity Q p p, identityCode q π π, .identity hQ hp hp,
    .refl (p.sub (Expr.liftSubN n (reflexiveSub x))), _, branch⟩

def Motive.pathInduction (m : @Motive Γ γ A x a ξ n Δ T)
    (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) (hx : TmDeriv Γ γ A a x ξ)
    (hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T)
    {args : Fin n → Expr}
    (hy : TmDeriv Γ γ A a y υ) (hp : TmDeriv Γ γ (.identity A x y) (identityCode a ξ υ) p π)
    (hs : SubDeriv Γ γ (Δ ++ pathCtx Γ A x) (telTotal T) (eliminationSub y p args) s) :=
  TmDeriv.pathInduction hΓ hA hx hT m.typing m.branchTyping hy hp hs

/-- A checked open path-induction command. Applying it only needs source terms
and a typed simultaneous substitution, never a semantic proof. -/
structure PathCommand {Γ : RawCtx} {γ : CtxCode.{u}} {A x : Expr} {a : TyCode γ}
    {ξ : TmCode γ a} {n : Nat} {Δ : RawCtx} (T : TelCode (pathCode a ξ) n) where
  context : CtxDeriv Γ γ
  type : TyDeriv Γ γ A a
  point : TmDeriv Γ γ A a x ξ
  telescope : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T
  motive : @Motive Γ γ A x a ξ n Δ T

def PathCommand.make
    (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) (hx : TmDeriv Γ γ A a x ξ)
    (hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T)
    (m : @Motive Γ γ A x a ξ n Δ T) : @PathCommand Γ γ A x a ξ n Δ T :=
  ⟨hΓ, hA, hx, hT, m⟩

/-- Interpretation checks every source component recursively before invoking J. -/
def PathCommand.interpretChecked (cmd : @PathCommand Γ γ A x a ξ n Δ T) (M : Model) :
    { t : M.Section (telTotal T M) (cmd.motive.code M) //
      t = jCode a ξ T cmd.motive.code cmd.motive.branchCode M } := by
  obtain ⟨g, hg⟩ := interpretCtxChecked M cmd.context
  obtain ⟨a, ha⟩ := interpretTyChecked M cmd.type
  obtain ⟨x, hx⟩ := interpretTmChecked M cmd.point
  obtain ⟨T, hT⟩ := interpretTelChecked M cmd.telescope
  obtain ⟨c, hc⟩ := interpretTyChecked M cmd.motive.typing
  obtain ⟨d, hd⟩ := interpretTmChecked M cmd.motive.branchTyping
  subst g; subst a; subst x; subst T; subst c; subst d
  exact ⟨M.j _ _ _ _ _, rfl⟩

def PathCommand.interpret (cmd : @PathCommand Γ γ A x a ξ n Δ T) (M : Model) :
    M.Section (telTotal T M) (cmd.motive.code M) := (cmd.interpretChecked M).val

theorem PathCommand.beta (cmd : @PathCommand Γ γ A x a ξ n Δ T) (M : Model) :
    HEq (M.subTm (cmd.interpret M) (rootTailCode a ξ T M)) (cmd.motive.branchCode M) := by
  have h := (cmd.interpretChecked M).property
  change cmd.interpret M = _ at h
  rw [h]
  exact M.j_beta _ _ _ _ _


def genericArguments (n : Nat) : Fin n → Expr := fun i => .var i.val

theorem genericArguments_id (n : Nat) :
    argsSub (genericArguments n) (fun i => .var (i+n)) = Expr.var := by
  funext i
  unfold argsSub
  split
  · rfl
  · simp only [Nat.sub_add_cancel (by omega : n ≤ i)]

theorem reflexiveCompose (n : Nat) (x : Expr) (ρ : RawSub) (args : Fin n → Expr) :
    (fun i => (Expr.liftSubN n (reflexiveSub x) i).sub (argsSub args ρ)) =
      argsSub args (consSub (.refl (x.sub ρ)) (consSub (x.sub ρ) ρ)) := by
  rw [liftSubN_argsSub]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

def SubDeriv.rawTransport {σ τ : RawSub} (h : σ = τ) (hs : SubDeriv Ω ω Γ γ σ s) :
    SubDeriv Ω ω Γ γ τ s := h ▸ hs

def PathCommand.branchContext (cmd : @PathCommand Γ γ A x a ξ n Δ T) :=
  CtxDeriv.branch cmd.context cmd.type cmd.point cmd.telescope

def PathCommand.branchTelescope (cmd : @PathCommand Γ γ A x a ξ n Δ T) :=
  TelDeriv.pullback cmd.telescope (SubDeriv.root cmd.context cmd.type cmd.point)

def PathCommand.branchProjection (cmd : @PathCommand Γ γ A x a ξ n Δ T) :=
  SubDeriv.projection cmd.context cmd.branchTelescope

def PathCommand.branchArguments (cmd : @PathCommand Γ γ A x a ξ n Δ T) :=
  SubDeriv.rawTransport (genericArguments_id n).symm (SubDeriv.id cmd.branchContext)

def PathCommand.reflexiveEndpoint (cmd : @PathCommand Γ γ A x a ξ n Δ T) :=
  SubDeriv.rawTransport (reflexiveCompose n x (fun i => .var (i+n)) (genericArguments n))
    (SubDeriv.comp (SubDeriv.rootTail cmd.context cmd.type cmd.point cmd.telescope)
      cmd.branchArguments)

/-- Apply the source J rule in its own reflexive branch context. The projection
and argument list are generated; the author supplies neither indices nor codes. -/
def PathCommand.reflexiveTerm (cmd : @PathCommand Γ γ A x a ξ n Δ T) :=
  TmDeriv.pathInductionReindex cmd.context cmd.type cmd.point cmd.telescope
    cmd.motive.typing cmd.motive.branchTyping cmd.branchProjection
    (TmDeriv.sub cmd.point cmd.branchProjection)
    (TmDeriv.refl (.sub cmd.type cmd.branchProjection) (.sub cmd.point cmd.branchProjection))
    cmd.reflexiveEndpoint

/-- Source computation, proved through the generic contextual beta rule. -/
def PathCommand.reflexiveBeta (cmd : @PathCommand Γ γ A x a ξ n Δ T) :=
  TmEqDeriv.jBetaReindex cmd.reflexiveTerm cmd.motive.branchTyping cmd.branchArguments


theorem PathCommand.interpreted_reflexiveBeta
    (cmd : @PathCommand Γ γ A x a ξ n Δ T) (M : Model) :
    subTmCode (jCode a ξ T cmd.motive.code cmd.motive.branchCode)
        (compCode (rootTailCode a ξ T) (idCode (SquareKit.Internal.PathTransport.Typed.branchCode a ξ T))) M =
      castCode (subTyComp_code cmd.motive.code (rootTailCode a ξ T)
        (idCode (SquareKit.Internal.PathTransport.Typed.branchCode a ξ T)))
        (subTmCode cmd.motive.branchCode (idCode (SquareKit.Internal.PathTransport.Typed.branchCode a ξ T))) M :=
  congrFun (termSound cmd.reflexiveBeta) M

/-- The generic source Expr J term over its complete path-and-tail context. -/
def PathCommand.genericTerm (cmd : @PathCommand Γ γ A x a ξ n Δ T) :=
  TmDeriv.genericJ cmd.context cmd.type cmd.point cmd.telescope
    cmd.motive.typing cmd.motive.branchTyping

/-- Rebuild all source premises under a typed substitution, including the
reflexive branch's dependent context. No semantic certificate is an argument. -/
def PathCommand.rebuild (cmd : @PathCommand Γ γ A x a ξ n Δ T)
    (hΩ : CtxDeriv Ω ω) (hσ : SubDeriv Ω ω Γ γ σ s) :
    @PathCommand Ω ω (A.sub σ) (x.sub σ) (subTyCode a s) (subTmCode ξ s)
      n (subTail (Expr.liftSubN 2 σ) Δ) (pathTailCode a ξ T s) :=
  { context := hΩ
    type := .sub cmd.type hσ
    point := .sub cmd.point hσ
    telescope := .pathReindex cmd.context cmd.type cmd.point cmd.telescope hσ
    motive :=
      { raw := cmd.motive.raw.sub (Expr.liftSubN (n+2) σ)
        code := subTyCode cmd.motive.code (pathTailMapCode a ξ T s)
        typing := .sub cmd.motive.typing
          (.pathTailMap cmd.context cmd.type cmd.point cmd.telescope hσ)
        branch := cmd.motive.branch.sub (Expr.liftSubN n σ)
        branchCode := reindexBranchCode a ξ T cmd.motive.code cmd.motive.branchCode s
        branchTyping := .reindexJBranch cmd.context cmd.type cmd.point cmd.telescope
          cmd.motive.typing cmd.motive.branchTyping hσ } }

/-- Source equality between substituting the old J and rebuilding it. -/
def PathCommand.rebuildConversion (cmd : @PathCommand Γ γ A x a ξ n Δ T)
    (hσ : SubDeriv Ω ω Γ γ σ s) :=
  TmEqDeriv.jSub cmd.context cmd.type cmd.point cmd.telescope
    cmd.motive.typing cmd.motive.branchTyping hσ

def PathCommand.substitutedTerm (cmd : @PathCommand Γ γ A x a ξ n Δ T)
    (hσ : SubDeriv Ω ω Γ γ σ s) :=
  TmDeriv.sub cmd.genericTerm
    (SubDeriv.pathTailMap cmd.context cmd.type cmd.point cmd.telescope hσ)

/-- All-rule conversion soundness connects the two actual source derivations. -/
theorem PathCommand.interpreted_rebuild (cmd : @PathCommand Γ γ A x a ξ n Δ T)
    (hΩ : CtxDeriv Ω ω) (hσ : SubDeriv Ω ω Γ γ σ s) (M : Model) :
    interpretTm M (cmd.substitutedTerm hσ) =
      interpretTm M (cmd.rebuild hΩ hσ).genericTerm := by
  rw [interpretTm_agrees, interpretTm_agrees]
  exact congrFun (termSound (cmd.rebuildConversion hσ)) M


namespace NamedCaller

def earlier := Checked.pointContext
def x : BasePoint [.base] (extendCode emptyCode (baseCode emptyCode)) :=
  ⟨.var 0, _, Checked.point⟩
def base := TyDeriv.base earlier
def endpointContext := CtxDeriv.ext earlier base
def endpointNative := TmDeriv.var earlier base
def fixedNative := TmDeriv.sub x.deriv (SubDeriv.weaken earlier base)
def pathType := TyDeriv.identity (.sub base (.weaken earlier base)) fixedNative endpointNative
def paths := CtxDeriv.ext endpointContext pathType

def moving := (BasePoint.variable earlier).weaken endpointContext pathType
def fixed := (x.weaken earlier base).weaken endpointContext pathType

def zType := TyDeriv.base paths
def withZ := CtxDeriv.ext paths zType
def z := BasePoint.variable paths
def yAtZ := moving.weaken paths zType
def qType := TyDeriv.identity (.base withZ) yAtZ.deriv z.deriv
def withQ := CtxDeriv.ext withZ qType
def xAtQ := (fixed.weaken paths zType).weaken withZ qType
def bType := TyDeriv.fiber xAtQ.deriv
def withB := CtxDeriv.ext withQ bType

def generalized := TelDeriv.cons zType (.cons qType (.cons bType (.nil withB)))
def qAtB := TmDeriv.sub (TmDeriv.var withZ qType) (SubDeriv.weaken withQ bType)
def qAtBType := TyDeriv.sub (.sub qType (.weaken withZ qType)) (.weaken withQ bType)

/-- The author chooses q = q, proves the branch by reflexivity, and retains
z, q : y = z and b : fiber x. No semantic argument occurs in the caller. -/
def pathInductionGeneralizingZQB :=
  PathCommand.make earlier base x.deriv generalized
    (Motive.reflexivity earlier base x.deriv generalized qAtBType qAtB)


/-- This is an actual source Expr J derivation, not only an open semantic command. -/
def reflexiveApplication := pathInductionGeneralizingZQB.reflexiveTerm

def reflexiveApplication_beta := pathInductionGeneralizingZQB.reflexiveBeta

/-- The actual source J term computes to its branch through all-rule soundness. -/
theorem interpreted_beta (M : Model) :
    HEq (interpretTm M reflexiveApplication) (pathInductionGeneralizingZQB.motive.branchCode M) := by
  rw [interpretTm_agrees]
  have h := pathInductionGeneralizingZQB.interpreted_reflexiveBeta M
  apply (heq_of_eq h).trans
  exact (castCode_eval _ _ M).trans (M.subTm_id _)

/-- Add an earlier source parameter and rebuild the same generalized-tail proof. -/
def weakenedCommand := pathInductionGeneralizingZQB.rebuild
  (CtxDeriv.ext earlier base) (SubDeriv.weaken earlier base)

def substitutedOriginal := pathInductionGeneralizingZQB.substitutedTerm
  (SubDeriv.weaken earlier base)

def source_rebuild_conversion := pathInductionGeneralizingZQB.rebuildConversion
  (SubDeriv.weaken earlier base)

/-- The checked source conversion, rather than beta or post-substitution alone,
proves agreement with J reconstructed from the substituted premises. -/
theorem rebuilt_interpretation (M : Model) :
    interpretTm M substitutedOriginal = interpretTm M weakenedCommand.genericTerm :=
  pathInductionGeneralizingZQB.interpreted_rebuild
    (CtxDeriv.ext earlier base) (SubDeriv.weaken earlier base) M

end NamedCaller

/- A beta redex used inside another J and inside simultaneous substitution. -/
namespace CongruenceCaller
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def context := Checked.pointContext
def point := Checked.point
def base := TyDeriv.base context
def paths := CtxDeriv.path context base point
def tail := TelDeriv.nil paths
def motive := TyDeriv.base paths
def root := SubDeriv.rootTail context base point tail
def branch := point.convert (TyEqDeriv.symm (.baseSub root))
def command := PathCommand.make context base point tail
  { raw := .base, code := baseCode _, typing := motive,
    branch := .var 0, branchCode := _, branchTyping := branch }

/-- The inner beta equality is converted to the ordinary base type. -/
def innerBeta := command.reflexiveBeta.convert (.baseSub command.reflexiveEndpoint)
def innerTerm := command.reflexiveTerm.convert (.baseSub command.reflexiveEndpoint)

private def annotateRight {Γ γ A a t ξ v ν ζ}
    (_e : TmEqDeriv Γ γ A a t ξ v ν) (h : TmDeriv Γ γ A a v ζ) (hc : ν = ζ) :
    TmDeriv Γ γ A a v ν := hc.symm ▸ h

private theorem cast_trans {γ : CtxCode} {a b c : TyCode γ}
    (h : a = b) (k : b = c) (ξ : TmCode γ a) :
    castCode k (castCode h ξ) = castCode (h.trans k) ξ := by cases h; cases k; rfl

private theorem cast_sub_id {γ : CtxCode} {a b : TyCode γ}
    (h : a = b) (k : subTyCode b (idCode γ) = a) (ξ : TmCode γ a) :
    castCode k (subTmCode (castCode h ξ) (idCode γ)) = ξ := by
  funext M
  exact eq_of_heq ((castCode_eval _ _ M).trans
    ((M.subTm_id _).trans (castCode_eval _ _ M)))

def innerRight := annotateRight innerBeta point (by
  change castCode _ (castCode _ (subTmCode (castCode _ _) (idCode _))) = _
  exact (cast_trans _ _ _).trans (cast_sub_id _ _ _))

def branchLeft := innerTerm.convert (.symm (.baseSub root))
def branchRight := innerRight.convert (.symm (.baseSub root))
def nestedLeft := TmDeriv.genericJ context base point tail motive branchLeft
def nestedRight := TmDeriv.genericJ context base point tail motive branchRight

/-- The converted inner beta equality is itself a branch conversion for J. -/
def branchBeta := innerBeta.convert (.symm (.baseSub root))
def nestedBeta := TmEqDeriv.pathInductionCongr context base point tail
  (.refl motive) branchBeta

def outerLeft := PathCommand.make context base point tail
  { raw := .base, code := baseCode _, typing := motive,
    branch := _, branchCode := _, branchTyping := branchLeft }
def outerRight := PathCommand.make context base point tail
  { raw := .base, code := baseCode _, typing := motive,
    branch := _, branchCode := _, branchTyping := branchRight }
def nestedAtBeta := TmEqDeriv.pathInductionAtCongr (.refl motive) branchBeta
  (.refl command.reflexiveEndpoint) outerLeft.reflexiveTerm outerRight.reflexiveTerm

def pathProjection := SubDeriv.comp (.weaken context base)
  (.weaken NamedCaller.endpointContext NamedCaller.pathType)
def motivePointType := TyDeriv.sub base pathProjection
def motivePoint := TmDeriv.sub innerTerm pathProjection
def motivePointRight := TmDeriv.sub innerRight pathProjection
def motivePointBeta := TmEqDeriv.sub innerBeta pathProjection
def motiveLeft := Motive.reflexivity context base point tail motivePointType motivePoint
def motiveRight := TyDeriv.identity motivePointType motivePointRight motivePointRight
def motiveConversion := TyEqDeriv.identity motivePointType motivePointBeta motivePointBeta
def motiveBeta := TmEqDeriv.pathInductionMotiveCongr context base point tail
  motiveConversion motiveLeft.branchTyping
def changedMotiveLeft := TmDeriv.genericJ context base point tail
  motiveLeft.typing motiveLeft.branchTyping
def changedMotiveRight := TmDeriv.genericJ context base point tail motiveRight
  (motiveLeft.branchTyping.convert (.sub motiveConversion root))

private def rawTerm {Γ γ A a t ξ} (_h : TmDeriv Γ γ A a t ξ) : Expr := t

/-- The checked conversion replaces an actual J node with a variable. -/
theorem beta_sides_distinct : rawTerm innerTerm ≠ rawTerm innerRight := by
  intro h
  cases h

theorem nested_sides_distinct : rawTerm nestedLeft ≠ rawTerm nestedRight := by
  intro h
  have hd := Expr.pathInduction.inj h
  obtain ⟨_, _, _, _, hd, _, _, _⟩ := hd
  cases hd

/-- The same beta conversion changes a substitution component, then an
identity proof using that component. -/
def pairedBeta := SubEqDeriv.pairingTerm base (SubDeriv.id context)
  (innerBeta.convert (.symm (.baseSub (.id context))))
def pairedLeft := SubDeriv.pair base (.id context)
  (innerTerm.convert (.symm (.baseSub (.id context))))
def pairedRight := SubDeriv.pair base (.id context)
  (innerRight.convert (.symm (.baseSub (.id context))))
def boundPoint := TmDeriv.var context base
def boundIdentity := TmDeriv.refl (.sub base (.weaken context base)) boundPoint
def substitutedBeta := TmEqDeriv.substitutionCongr boundIdentity pairedBeta

def substitutedLeft := TmDeriv.sub boundIdentity pairedLeft
def substitutedRight := TmDeriv.sub boundIdentity pairedRight

/-- A second component depends on the converted first component. This uses
both substitution and term premises of dependent pairing congruence. -/
def dependentType := TyDeriv.identity (.sub base (.weaken context base)) boundPoint boundPoint
def dependentPairedBeta := SubEqDeriv.pairingCongr dependentType pairedBeta substitutedBeta
def dependentPairedLeft := SubDeriv.pair dependentType pairedLeft substitutedLeft
def dependentPairedRight := SubDeriv.pair dependentType pairedRight substitutedRight

theorem dependentPairedBeta_sound (M : Model) :
    interpretSub M dependentPairedLeft = interpretSub M dependentPairedRight := by
  rw [interpretSub_agrees, interpretSub_agrees]
  exact congrFun (subSound dependentPairedBeta) M

theorem motiveBeta_sound (M : Model) :
    HEq (interpretTm M changedMotiveLeft) (interpretTm M changedMotiveRight) := by
  rw [interpretTm_agrees, interpretTm_agrees]
  exact (heq_of_eq (congrFun (termSound motiveBeta) M)).trans (castCode_eval _ _ M)

theorem nestedAtBeta_sound (M : Model) :
    interpretTm M outerLeft.reflexiveTerm = interpretTm M outerRight.reflexiveTerm := by
  rw [interpretTm_agrees, interpretTm_agrees]
  exact congrFun (termSound nestedAtBeta) M

theorem substitutedBeta_sound (M : Model) :
    HEq (interpretTm M substitutedLeft) (interpretTm M substitutedRight) := by
  rw [interpretTm_agrees, interpretTm_agrees]
  exact (heq_of_eq (congrFun (termSound substitutedBeta) M)).trans (castCode_eval _ _ M)

theorem nestedBeta_sound (M : Model) :
    interpretTm M nestedLeft = interpretTm M nestedRight := by
  rw [interpretTm_agrees, interpretTm_agrees]
  exact congrFun (termSound nestedBeta) M

end CongruenceCaller
end SquareKit.Internal.PathTransport.Typed.Authoring
