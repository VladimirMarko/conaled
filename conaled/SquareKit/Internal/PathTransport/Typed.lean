import SquareKit.Internal.PathTransport.ContextualModel

/-! Generated typed syntax with model-parametric interpretation annotations.
Raw contexts, types and terms remain indices, including through conversion.
The interpretation recurses on source derivations and proves agreement with
the annotations; arbitrary denotations are not source constructors. -/

namespace SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.PathTransport
universe u

abbrev CtxCode := (M : Model.{u}) → M.Context
abbrev TyCode (Γ : CtxCode.{u}) := (M : Model.{u}) → M.Family (Γ M)
abbrev TmCode (Γ : CtxCode.{u}) (A : TyCode Γ) := (M : Model.{u}) → M.Section (Γ M) (A M)
abbrev SubCode (Δ Γ : CtxCode.{u}) := (M : Model.{u}) → M.Substitution (Δ M) (Γ M)

def emptyCode : CtxCode := fun M => M.empty
def extendCode (Γ : CtxCode) (A : TyCode Γ) : CtxCode := fun M => M.extend (Γ M) (A M)
def baseCode (Γ : CtxCode) : TyCode Γ := fun M => M.base (Γ M)
def fiberCode (x : TmCode Γ (baseCode Γ)) : TyCode Γ := fun M => M.fiber (x M)
def identityCode (A : TyCode Γ) (x y : TmCode Γ A) : TyCode Γ :=
  fun M => M.identity (A M) (x M) (y M)
def reflCode (A : TyCode Γ) (x : TmCode Γ A) : TmCode Γ (identityCode A x x) :=
  fun M => M.reflexivity (A M) (x M)
def idCode (Γ : CtxCode) : SubCode Γ Γ := fun M => M.idSub (Γ M)
def compCode (σ : SubCode Δ Γ) (τ : SubCode Θ Δ) : SubCode Θ Γ :=
  fun M => M.compSub (σ M) (τ M)
def subTyCode (A : TyCode Γ) (σ : SubCode Δ Γ) : TyCode Δ := fun M => M.subTy (A M) (σ M)
def subTmCode (t : TmCode Γ A) (σ : SubCode Δ Γ) : TmCode Δ (subTyCode A σ) :=
  fun M => M.subTm (t M) (σ M)
def weakenCode (Γ : CtxCode) (A : TyCode Γ) : SubCode (extendCode Γ A) Γ :=
  fun M => M.weaken (Γ M) (A M)
def varCode (Γ : CtxCode) (A : TyCode Γ) :
    TmCode (extendCode Γ A) (subTyCode A (weakenCode Γ A)) :=
  fun M => M.genericVariable (Γ M) (A M)
def pairCode (A : TyCode Γ) (σ : SubCode Δ Γ) (t : TmCode Δ (subTyCode A σ)) :
    SubCode Δ (extendCode Γ A) := fun M => M.pairSub (A M) (σ M) (t M)
def castCode {a b : TyCode Γ} (h : a = b) (ξ : TmCode Γ a) : TmCode Γ b := h ▸ ξ

theorem subTyId_code (A : TyCode Γ) : subTyCode A (idCode Γ) = A := by
  funext M; exact M.subTy_id _
theorem subTyComp_code (A : TyCode Γ) (σ : SubCode Δ Γ) (τ : SubCode Θ Δ) :
    subTyCode (subTyCode A σ) τ = subTyCode A (compCode σ τ) := by
  funext M; exact M.subTy_comp _ _ _
theorem baseSub_code (σ : SubCode Δ Γ) : subTyCode (baseCode Γ) σ = baseCode Δ := by
  funext M; exact M.base_sub _
theorem identitySub_code (A : TyCode Γ) (x y : TmCode Γ A) (σ : SubCode Δ Γ) :
    subTyCode (identityCode A x y) σ =
      identityCode (subTyCode A σ) (subTmCode x σ) (subTmCode y σ) := by
  funext M; exact M.identity_sub _ _ _ _

theorem castCode_eval {a b : TyCode Γ} (h : a = b) (ξ : TmCode Γ a) (M : Model) :
    HEq (castCode h ξ M) (ξ M) := by cases h; rfl

theorem fiberSub_code (ξ : TmCode Γ (baseCode Γ)) (s : SubCode Δ Γ) :
    subTyCode (fiberCode ξ) s = fiberCode (castCode (baseSub_code s) (subTmCode ξ s)) := by
  funext M
  dsimp [subTyCode, fiberCode, baseCode]
  apply (M.fiber_sub (ξ M) (s M)).trans
  apply congrArg M.fiber
  apply eq_of_heq
  exact (cast_heq _ _).trans (castCode_eval (baseSub_code s) (subTmCode ξ s) M).symm

theorem subTmId_code (ξ : TmCode Γ a) :
    castCode (subTyId_code a) (subTmCode ξ (idCode Γ)) = ξ := by
  funext M
  exact eq_of_heq ((castCode_eval _ _ M).trans (M.subTm_id (ξ M)))

theorem subTmComp_code (ξ : TmCode Γ a) (s : SubCode Δ Γ) (t : SubCode Θ Δ) :
    castCode (subTyComp_code a s t) (subTmCode (subTmCode ξ s) t) =
      subTmCode ξ (compCode s t) := by
  funext M
  exact eq_of_heq ((castCode_eval _ _ M).trans (M.subTm_comp (ξ M) (s M) (t M)))

theorem reflSub_code (a : TyCode Γ) (ξ : TmCode Γ a) (s : SubCode Δ Γ) :
    castCode (identitySub_code a ξ ξ s) (subTmCode (reflCode a ξ) s) =
      reflCode (subTyCode a s) (subTmCode ξ s) := by
  funext M
  exact eq_of_heq ((castCode_eval _ _ M).trans (M.refl_sub (a M) (ξ M) (s M)))


theorem weakenPair_code (a : TyCode Γ) (s : SubCode Δ Γ) (ξ : TmCode Δ (subTyCode a s)) :
    compCode (weakenCode Γ a) (pairCode a s ξ) = s := by
  funext M; exact M.weaken_pair _ _ _

theorem variablePair_type (a : TyCode Γ) (s : SubCode Δ Γ) (ξ : TmCode Δ (subTyCode a s)) :
    subTyCode (subTyCode a (weakenCode Γ a)) (pairCode a s ξ) = subTyCode a s := by
  rw [subTyComp_code, weakenPair_code]

theorem variablePair_code (a : TyCode Γ) (s : SubCode Δ Γ) (ξ : TmCode Δ (subTyCode a s)) :
    castCode (variablePair_type a s ξ) (subTmCode (varCode Γ a) (pairCode a s ξ)) = ξ := by
  funext M
  exact eq_of_heq ((castCode_eval _ _ M).trans (M.variable_pair (a M) (s M) (ξ M)))

def etaPairCode (a : TyCode Γ) (s : SubCode Δ (extendCode Γ a)) : SubCode Δ (extendCode Γ a) :=
  pairCode a (compCode (weakenCode Γ a) s)
    (castCode (subTyComp_code a (weakenCode Γ a) s) (subTmCode (varCode Γ a) s))

theorem etaPair_code (a : TyCode Γ) (s : SubCode Δ (extendCode Γ a)) : etaPairCode a s = s := by
  funext M
  apply Eq.trans _ (M.pair_eta (a M) (s M))
  apply congrArg (M.pairSub (a M) (M.compSub (M.weaken (Γ M) (a M)) (s M)))
  exact eq_of_heq ((castCode_eval (subTyComp_code a (weakenCode Γ a) s)
    (subTmCode (varCode Γ a) s) M).trans (cast_heq _ _).symm)


abbrev TelCode (γ : CtxCode.{u}) (n : Nat) :=
  (M : Model.{u}) → StructuralModel.Telescope M.toStructuralModel (γ M) n

def pathCode (a : TyCode γ) (ξ : TmCode γ a) : CtxCode :=
  fun M => M.toStructuralModel.pathContext (a M) (ξ M)
def telNil (γ : CtxCode) : TelCode γ 0 := fun _ => .nil
def telCons (a : TyCode γ) (T : TelCode (extendCode γ a) n) : TelCode γ (n+1) :=
  fun M => .cons (a M) (T M)
def telTotal (T : TelCode γ n) : CtxCode :=
  fun M => StructuralModel.Telescope.total M.toStructuralModel (T M)
def projectionCode (T : TelCode γ n) : SubCode (telTotal T) γ :=
  fun M => StructuralModel.Telescope.projection M.toStructuralModel (T M)
def telPullback (T : TelCode γ n) (s : SubCode δ γ) : TelCode δ n :=
  fun M => StructuralModel.Telescope.pullback M.toStructuralModel (T M) (s M)
def rootCode (a : TyCode γ) (ξ : TmCode γ a) : SubCode γ (pathCode a ξ) :=
  fun M => M.toStructuralModel.rootSub (a M) (ξ M)
def branchCode (a : TyCode γ) (ξ : TmCode γ a) (T : TelCode (pathCode a ξ) n) : CtxCode :=
  fun M => StructuralModel.Telescope.total M.toStructuralModel
    (StructuralModel.Telescope.pullback M.toStructuralModel (T M)
      (M.toStructuralModel.rootSub (a M) (ξ M)))
def rootTailCode (a : TyCode γ) (ξ : TmCode γ a) (T : TelCode (pathCode a ξ) n) :
    SubCode (branchCode a ξ T) (telTotal T) :=
  fun M => M.toStructuralModel.rootTail (a M) (ξ M) (T M)
def jCode (a : TyCode γ) (ξ : TmCode γ a) (T : TelCode (pathCode a ξ) n)
    (c : TyCode (telTotal T)) (d : TmCode (branchCode a ξ T) (subTyCode c (rootTailCode a ξ T))) :
    TmCode (telTotal T) c := fun M => M.j (a M) (ξ M) (T M) (c M) (d M)


theorem jBetaSub_code (a : TyCode γ) (ξ : TmCode γ a) (T : TelCode (pathCode a ξ) n)
    (c : TyCode (telTotal T)) (d : TmCode (branchCode a ξ T) (subTyCode c (rootTailCode a ξ T)))
    (s : SubCode δ (branchCode a ξ T)) :
    subTmCode (jCode a ξ T c d) (compCode (rootTailCode a ξ T) s) =
      castCode (subTyComp_code c (rootTailCode a ξ T) s) (subTmCode d s) := by
  funext M
  apply eq_of_heq
  apply (M.subTm_comp (M.j (a M) (ξ M) (T M) (c M) (d M))
    (rootTailCode a ξ T M) (s M)).symm.trans
  have hb := eq_of_heq (M.j_beta (a M) (ξ M) (T M) (c M) (d M))
  have he := congrArg (fun z => M.subTm z (s M)) hb
  exact (heq_of_eq he).trans
    (castCode_eval (subTyComp_code c (rootTailCode a ξ T) s) (subTmCode d s) M).symm

/-- Contextual J at the generic endpoint, path and tail variables. Ambient
parameters are weakened across the full telescope; each binder is preserved. -/
def genericJRaw (n : Nat) (A x C d : Expr) : Expr :=
  let shift := fun i => i + (n + 2)
  .pathInduction n (A.rename shift) (x.rename shift)
    (C.rename (Expr.liftRenN (n+2) shift)) (d.rename (Expr.liftRenN n shift))
    (.var (n+1)) (.var n) (fun i => .var i.val)

def pathSubCode (a : TyCode γ) (ξ : TmCode γ a) (s : SubCode δ γ) :
    SubCode (pathCode (subTyCode a s) (subTmCode ξ s)) (pathCode a ξ) :=
  fun M => M.toStructuralModel.pathSub (a M) (ξ M) (s M)

def pathTailCode (a : TyCode γ) (ξ : TmCode γ a) (T : TelCode (pathCode a ξ) n)
    (s : SubCode δ γ) : TelCode (pathCode (subTyCode a s) (subTmCode ξ s)) n :=
  fun M => M.toStructuralModel.pathTail (a M) (ξ M) (T M) (s M)

def pathTailMapCode (a : TyCode γ) (ξ : TmCode γ a) (T : TelCode (pathCode a ξ) n)
    (s : SubCode δ γ) : SubCode (telTotal (pathTailCode a ξ T s)) (telTotal T) :=
  fun M => M.toStructuralModel.pathTailMap (a M) (ξ M) (T M) (s M)

def reindexBranchCode (a : TyCode γ) (ξ : TmCode γ a) (T : TelCode (pathCode a ξ) n)
    (c : TyCode (telTotal T)) (η : TmCode (branchCode a ξ T) (subTyCode c (rootTailCode a ξ T)))
    (s : SubCode δ γ) :
    TmCode (branchCode (subTyCode a s) (subTmCode ξ s) (pathTailCode a ξ T s))
      (subTyCode (subTyCode c (pathTailMapCode a ξ T s))
        (rootTailCode (subTyCode a s) (subTmCode ξ s) (pathTailCode a ξ T s))) :=
  fun M => M.toStructuralModel.reindexBranch (a M) (ξ M) (T M) (s M) (c M) (η M)

/-- Rebuilt J uses the pulled-back telescope and the constructed branch
comparison, rather than merely reindexing an already constructed section. -/
theorem jSub_code (a : TyCode γ) (ξ : TmCode γ a) (T : TelCode (pathCode a ξ) n)
    (c : TyCode (telTotal T)) (η : TmCode (branchCode a ξ T) (subTyCode c (rootTailCode a ξ T)))
    (s : SubCode δ γ) :
    subTmCode (jCode a ξ T c η) (pathTailMapCode a ξ T s) =
      jCode (subTyCode a s) (subTmCode ξ s) (pathTailCode a ξ T s)
        (subTyCode c (pathTailMapCode a ξ T s)) (reindexBranchCode a ξ T c η s) := by
  funext M
  exact eq_of_heq (M.j_sub (a M) (ξ M) (T M) (c M) (η M) (s M))


mutual
inductive CtxDeriv : RawCtx → CtxCode.{u} → Type (u+1) where
  | empty : CtxDeriv [] emptyCode
  | ext : CtxDeriv Γ γ → TyDeriv Γ γ A a → CtxDeriv (A :: Γ) (extendCode γ a)
  | path : CtxDeriv Γ γ → TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ →
      CtxDeriv (pathCtx Γ A x) (pathCode a ξ)
  | telescope : CtxDeriv Γ γ → TelDeriv Γ γ n Δ T → CtxDeriv (Δ ++ Γ) (telTotal T)
  | branch : CtxDeriv Γ γ → TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ →
      TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T →
      CtxDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)

inductive TelDeriv : (Γ : RawCtx) → (γ : CtxCode.{u}) →
    (n : Nat) → RawCtx → TelCode γ n → Type (u+1) where
  | nil : CtxDeriv Γ γ → TelDeriv Γ γ 0 [] (telNil γ)
  | cons : TyDeriv Γ γ A a → TelDeriv (A :: Γ) (extendCode γ a) n Δ T →
      TelDeriv Γ γ (n+1) (Δ ++ [A]) (telCons a T)
  | pullback : TelDeriv Γ γ n Δ T → SubDeriv Ω ω Γ γ σ s →
      TelDeriv Ω ω n (subTail σ Δ) (telPullback T s)

  | pathReindex : CtxDeriv Γ γ → TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ →
      TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T → SubDeriv Ω ω Γ γ σ s →
      TelDeriv (pathCtx Ω (A.sub σ) (x.sub σ)) (pathCode (subTyCode a s) (subTmCode ξ s))
        n (subTail (Expr.liftSubN 2 σ) Δ) (pathTailCode a ξ T s)

inductive TyDeriv : (Γ : RawCtx) → (γ : CtxCode.{u}) → Expr → TyCode γ → Type (u+1) where
  | base : CtxDeriv Γ γ → TyDeriv Γ γ .base (baseCode γ)
  | fiber : TmDeriv Γ γ .base (baseCode γ) x ξ → TyDeriv Γ γ (.fiber x) (fiberCode ξ)
  | identity : TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ → TmDeriv Γ γ A a y η →
      TyDeriv Γ γ (.identity A x y) (identityCode a ξ η)
  | sub : TyDeriv Γ γ A a → SubDeriv Δ δ Γ γ σ s → TyDeriv Δ δ (A.sub σ) (subTyCode a s)

inductive TmDeriv : (Γ : RawCtx) → (γ : CtxCode.{u}) →
    (A : Expr) → (a : TyCode γ) → Expr → TmCode γ a → Type (u+1) where
  | var : CtxDeriv Γ γ → TyDeriv Γ γ A a →
      TmDeriv (A :: Γ) (extendCode γ a) (A.rename Nat.succ)
        (subTyCode a (weakenCode γ a)) (.var 0) (varCode γ a)
  | refl : TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ →
      TmDeriv Γ γ (.identity A x x) (identityCode a ξ ξ) (.refl x) (reflCode a ξ)
  | sub : TmDeriv Γ γ A a t ξ → SubDeriv Δ δ Γ γ σ s →
      TmDeriv Δ δ (A.sub σ) (subTyCode a s) (t.sub σ) (subTmCode ξ s)
  | pathInduction : CtxDeriv Γ γ → TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ →
      TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T →
      TyDeriv (Δ ++ pathCtx Γ A x) (telTotal T) C c →
      TmDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
        (C.sub (Expr.liftSubN n (reflexiveSub x))) (subTyCode c (rootTailCode a ξ T)) d η →
      TmDeriv Γ γ A a y υ → TmDeriv Γ γ (.identity A x y) (identityCode a ξ υ) p π →
      SubDeriv Γ γ (Δ ++ pathCtx Γ A x) (telTotal T) (eliminationSub y p args) s →
      TmDeriv Γ γ (C.sub (eliminationSub y p args)) (subTyCode c s)
        (.pathInduction n A x C d y p args) (subTmCode (jCode a ξ T c η) s)
  | pathInductionReindex : CtxDeriv Γ γ → TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ →
      TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T →
      TyDeriv (Δ ++ pathCtx Γ A x) (telTotal T) C c →
      TmDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
        (C.sub (Expr.liftSubN n (reflexiveSub x))) (subTyCode c (rootTailCode a ξ T)) d η →
      SubDeriv Ω ω Γ γ ρ r →
      TmDeriv Ω ω (A.sub ρ) (subTyCode a r) y υ →
      TmDeriv Ω ω (.identity (A.sub ρ) (x.sub ρ) y)
        (identityCode (subTyCode a r) (subTmCode ξ r) υ) p π →
      SubDeriv Ω ω (Δ ++ pathCtx Γ A x) (telTotal T) (argsSub args (consSub p (consSub y ρ))) s →
      TmDeriv Ω ω (C.sub (argsSub args (consSub p (consSub y ρ)))) (subTyCode c s)
        (.pathInduction n (A.sub ρ) (x.sub ρ) (C.sub (Expr.liftSubN (n+2) ρ))
          (d.sub (Expr.liftSubN n ρ)) y p args) (subTmCode (jCode a ξ T c η) s)
  | genericJ : CtxDeriv Γ γ → TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ →
      TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T →
      TyDeriv (Δ ++ pathCtx Γ A x) (telTotal T) C c →
      TmDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
        (C.sub (Expr.liftSubN n (reflexiveSub x))) (subTyCode c (rootTailCode a ξ T)) d η →
      TmDeriv (Δ ++ pathCtx Γ A x) (telTotal T) C c (genericJRaw n A x C d) (jCode a ξ T c η)
  | reindexJBranch : CtxDeriv Γ γ → TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ →
      TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T →
      TyDeriv (Δ ++ pathCtx Γ A x) (telTotal T) C c →
      TmDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
        (C.sub (Expr.liftSubN n (reflexiveSub x))) (subTyCode c (rootTailCode a ξ T)) d η →
      SubDeriv Ω ω Γ γ σ s →
      TmDeriv (subTail (reflexiveSub (x.sub σ)) (subTail (Expr.liftSubN 2 σ) Δ) ++ Ω)
        (branchCode (subTyCode a s) (subTmCode ξ s) (pathTailCode a ξ T s))
        ((C.sub (Expr.liftSubN (n+2) σ)).sub (Expr.liftSubN n (reflexiveSub (x.sub σ))))
        (subTyCode (subTyCode c (pathTailMapCode a ξ T s))
          (rootTailCode (subTyCode a s) (subTmCode ξ s) (pathTailCode a ξ T s)))
        (d.sub (Expr.liftSubN n σ)) (reindexBranchCode a ξ T c η s)
  | conv : TmDeriv Γ γ A a t ξ → TyEqDeriv Γ γ A a B b → (h : a = b) →
      TmDeriv Γ γ B b t (castCode h ξ)

inductive SubDeriv : (Δ : RawCtx) → (δ : CtxCode.{u}) → (Γ : RawCtx) → (γ : CtxCode.{u}) →
    RawSub → (s : SubCode δ γ) → Type (u+1) where
  | id : CtxDeriv Γ γ → SubDeriv Γ γ Γ γ Expr.var (idCode γ)
  | comp : SubDeriv Δ δ Γ γ σ s → SubDeriv Θ θ Δ δ τ t →
      SubDeriv Θ θ Γ γ (fun n => (σ n).sub τ) (compCode s t)
  | weaken : CtxDeriv Γ γ → TyDeriv Γ γ A a →
      SubDeriv (A :: Γ) (extendCode γ a) Γ γ (Expr.var ∘ Nat.succ) (weakenCode γ a)
  | projection : CtxDeriv Γ γ → TelDeriv Γ γ n Δ T →
      SubDeriv (Δ ++ Γ) (telTotal T) Γ γ (fun i => .var (i + n)) (projectionCode T)
  | root : CtxDeriv Γ γ → TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ →
      SubDeriv Γ γ (pathCtx Γ A x) (pathCode a ξ) (reflexiveSub x) (rootCode a ξ)
  | rootTail : CtxDeriv Γ γ → TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ →
      TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T →
      SubDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
        (Δ ++ pathCtx Γ A x) (telTotal T) (Expr.liftSubN n (reflexiveSub x)) (rootTailCode a ξ T)
  | pathTailMap : CtxDeriv Γ γ → TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ →
      TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T → SubDeriv Ω ω Γ γ σ s →
      SubDeriv (subTail (Expr.liftSubN 2 σ) Δ ++ pathCtx Ω (A.sub σ) (x.sub σ))
        (telTotal (pathTailCode a ξ T s)) (Δ ++ pathCtx Γ A x) (telTotal T)
        (Expr.liftSubN (n+2) σ) (pathTailMapCode a ξ T s)
  | pair : TyDeriv Γ γ A a → SubDeriv Δ δ Γ γ σ s →
      TmDeriv Δ δ (A.sub σ) (subTyCode a s) t ξ →
      SubDeriv Δ δ (A :: Γ) (extendCode γ a) (consSub t σ) (pairCode a s ξ)

inductive TyEqDeriv : (Γ : RawCtx) → (γ : CtxCode.{u}) →
    (A : Expr) → TyCode γ → (B : Expr) → TyCode γ → Type (u+1) where
  | refl : TyDeriv Γ γ A a → TyEqDeriv Γ γ A a A a
  | symm : TyEqDeriv Γ γ A a B b → TyEqDeriv Γ γ B b A a
  | trans : TyEqDeriv Γ γ A a B b → TyEqDeriv Γ γ B b C c → TyEqDeriv Γ γ A a C c
  | fiber : TmEqDeriv Γ γ .base (baseCode γ) x ξ y η →
      TyEqDeriv Γ γ (.fiber x) (fiberCode ξ) (.fiber y) (fiberCode η)
  | identity : TyDeriv Γ γ A a → TmEqDeriv Γ γ A a x ξ x' ξ' →
      TmEqDeriv Γ γ A a y η y' η' →
      TyEqDeriv Γ γ (.identity A x y) (identityCode a ξ η)
        (.identity A x' y') (identityCode a ξ' η')
  | identityType : TyEqDeriv Γ γ A a B b → (h : a = b) →
      TmDeriv Γ γ A a x ξ → TmDeriv Γ γ A a y η →
      TyEqDeriv Γ γ (.identity A x y) (identityCode a ξ η)
        (.identity B x y) (identityCode b (castCode h ξ) (castCode h η))
  | subCongr : TyDeriv Γ γ A a → SubEqDeriv Δ δ Γ γ σ s τ t →
      TyEqDeriv Δ δ (A.sub σ) (subTyCode a s) (A.sub τ) (subTyCode a t)
  | sub : TyEqDeriv Γ γ A a B b → SubDeriv Δ δ Γ γ σ s →
      TyEqDeriv Δ δ (A.sub σ) (subTyCode a s) (B.sub σ) (subTyCode b s)
  | subId : TyDeriv Γ γ A a → TyEqDeriv Γ γ (A.sub Expr.var) (subTyCode a (idCode γ)) A a
  | subComp : TyDeriv Γ γ A a → SubDeriv Δ δ Γ γ σ s → SubDeriv Θ θ Δ δ τ t →
      TyEqDeriv Θ θ ((A.sub σ).sub τ) (subTyCode (subTyCode a s) t)
        (A.sub (fun n => (σ n).sub τ)) (subTyCode a (compCode s t))
  | baseSub : SubDeriv Δ δ Γ γ σ s →
      TyEqDeriv Δ δ .base (subTyCode (baseCode γ) s) .base (baseCode δ)
  | fiberSub : TmDeriv Γ γ .base (baseCode γ) x ξ → SubDeriv Δ δ Γ γ σ s →
      TyEqDeriv Δ δ (.fiber (x.sub σ)) (subTyCode (fiberCode ξ) s)
        (.fiber (x.sub σ)) (fiberCode (castCode (baseSub_code s) (subTmCode ξ s)))
  | identitySub : TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ → TmDeriv Γ γ A a y η →
      SubDeriv Δ δ Γ γ σ s →
      TyEqDeriv Δ δ ((Expr.identity A x y).sub σ) (subTyCode (identityCode a ξ η) s)
        (.identity (A.sub σ) (x.sub σ) (y.sub σ))
        (identityCode (subTyCode a s) (subTmCode ξ s) (subTmCode η s))

inductive TmEqDeriv : (Γ : RawCtx) → (γ : CtxCode.{u}) →
    (A : Expr) → (a : TyCode γ) → Expr → TmCode γ a → Expr → TmCode γ a → Type (u+1) where
  | refl : TmDeriv Γ γ A a t ξ → TmEqDeriv Γ γ A a t ξ t ξ
  | symm : TmEqDeriv Γ γ A a t ξ v ν → TmEqDeriv Γ γ A a v ν t ξ
  | trans : TmEqDeriv Γ γ A a t ξ v ν → TmEqDeriv Γ γ A a v ν w ω →
      TmEqDeriv Γ γ A a t ξ w ω
  | conv : TmEqDeriv Γ γ A a t ξ v ν → TyEqDeriv Γ γ A a B b → (h : a = b) →
      TmEqDeriv Γ γ B b t (castCode h ξ) v (castCode h ν)
  | sub : TmEqDeriv Γ γ A a t ξ v ν → SubDeriv Δ δ Γ γ σ s →
      TmEqDeriv Δ δ (A.sub σ) (subTyCode a s) (t.sub σ) (subTmCode ξ s)
        (v.sub σ) (subTmCode ν s)
  | subId : TmDeriv Γ γ A a x ξ →
      TmEqDeriv Γ γ A a (x.sub Expr.var)
        (castCode (subTyId_code a) (subTmCode ξ (idCode γ))) x ξ
  | subComp : TmDeriv Γ γ A a x ξ → SubDeriv Δ δ Γ γ σ s → SubDeriv Θ θ Δ δ τ t →
      TmEqDeriv Θ θ (A.sub (fun n => (σ n).sub τ)) (subTyCode a (compCode s t))
        ((x.sub σ).sub τ) (castCode (subTyComp_code a s t) (subTmCode (subTmCode ξ s) t))
        (x.sub (fun n => (σ n).sub τ)) (subTmCode ξ (compCode s t))
  | reflSub : TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ → SubDeriv Δ δ Γ γ σ s →
      TmEqDeriv Δ δ (.identity (A.sub σ) (x.sub σ) (x.sub σ))
        (identityCode (subTyCode a s) (subTmCode ξ s) (subTmCode ξ s))
        ((Expr.refl x).sub σ) (castCode (identitySub_code a ξ ξ s) (subTmCode (reflCode a ξ) s))
        (.refl (x.sub σ)) (reflCode (subTyCode a s) (subTmCode ξ s))

  | reflCongr : TmEqDeriv Γ γ A a x ξ y η → (h : ξ = η) →
      TmEqDeriv Γ γ (.identity A x x) (identityCode a ξ ξ)
        (.refl x) (reflCode a ξ) (.refl y)
        (castCode (by rw [h]) (reflCode a η))
  | subCongr : TmDeriv Γ γ A a x ξ → SubEqDeriv Δ δ Γ γ σ s τ t → (h : s = t) →
      TmEqDeriv Δ δ (A.sub σ) (subTyCode a s) (x.sub σ) (subTmCode ξ s)
        (x.sub τ) (castCode (congrArg (subTyCode a) h.symm) (subTmCode ξ t))
  | variablePair : TyDeriv Γ γ A a → SubDeriv Δ δ Γ γ σ s →
      TmDeriv Δ δ (A.sub σ) (subTyCode a s) t ξ →
      TmEqDeriv Δ δ (A.sub σ) (subTyCode a s) t
        (castCode (variablePair_type a s ξ) (subTmCode (varCode γ a) (pairCode a s ξ))) t ξ

  /-- Congruence in the motive and branch of contextual J. The branch
  comparison is in the left motive; its cast is guarded by source conversion. -/
  | jCongr : CtxDeriv Γ γ → TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ →
      TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T →
      TyEqDeriv (Δ ++ pathCtx Γ A x) (telTotal T) C c D c' → (h : c = c') →
      TmEqDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
        (C.sub (Expr.liftSubN n (reflexiveSub x))) (subTyCode c (rootTailCode a ξ T))
        d η d' (castCode (congrArg (fun c => subTyCode c (rootTailCode a ξ T)) h.symm) η') →
      TmEqDeriv (Δ ++ pathCtx Γ A x) (telTotal T) C c
        (genericJRaw n A x C d) (jCode a ξ T c η)
        (genericJRaw n A x D d') (castCode h.symm (jCode a ξ T c' η'))

  /-- Instantiated J respects motive, branch and simultaneous endpoint/tail
  conversion. Both expressions retain their actual source typing derivations. -/
  | jCongrAt {Γ Ω : RawCtx} {γ ω : CtxCode} {A x C D d d' : Expr} {a : TyCode γ}
      {ξ : TmCode γ a} {n : Nat} {Δ : RawCtx} {T : TelCode (pathCode a ξ) n}
      {c c' : TyCode (telTotal T)}
      {η : TmCode (branchCode a ξ T) (subTyCode c (rootTailCode a ξ T))}
      {η' : TmCode (branchCode a ξ T) (subTyCode c' (rootTailCode a ξ T))}
      {args args' : Fin n → Expr} {ρ ρ' : RawSub} {y y' p p' : Expr}
      {s s' : SubCode ω (telTotal T)} :
      TyEqDeriv (Δ ++ pathCtx Γ A x) (telTotal T) C c D c' → (h : c = c') →
      TmEqDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
        (C.sub (Expr.liftSubN n (reflexiveSub x))) (subTyCode c (rootTailCode a ξ T))
        d η d' (castCode (congrArg (fun c => subTyCode c (rootTailCode a ξ T)) h.symm) η') →
      SubEqDeriv Ω ω (Δ ++ pathCtx Γ A x) (telTotal T)
        (argsSub args (consSub p (consSub y ρ))) s
        (argsSub args' (consSub p' (consSub y' ρ'))) s' → (k : s = s') →
      TmDeriv Ω ω (C.sub (argsSub args (consSub p (consSub y ρ)))) (subTyCode c s)
        (.pathInduction n (A.sub ρ) (x.sub ρ) (C.sub (Expr.liftSubN (n+2) ρ))
          (d.sub (Expr.liftSubN n ρ)) y p args) (subTmCode (jCode a ξ T c η) s) →
      TmDeriv Ω ω (D.sub (argsSub args' (consSub p' (consSub y' ρ')))) (subTyCode c' s')
        (.pathInduction n (A.sub ρ') (x.sub ρ') (D.sub (Expr.liftSubN (n+2) ρ'))
          (d'.sub (Expr.liftSubN n ρ')) y' p' args') (subTmCode (jCode a ξ T c' η') s') →
      TmEqDeriv Ω ω (C.sub (argsSub args (consSub p (consSub y ρ)))) (subTyCode c s)
        (.pathInduction n (A.sub ρ) (x.sub ρ) (C.sub (Expr.liftSubN (n+2) ρ))
          (d.sub (Expr.liftSubN n ρ)) y p args) (subTmCode (jCode a ξ T c η) s)
        (.pathInduction n (A.sub ρ') (x.sub ρ') (D.sub (Expr.liftSubN (n+2) ρ'))
          (d'.sub (Expr.liftSubN n ρ')) y' p' args')
        (castCode (congrArg₂ subTyCode h.symm k.symm) (subTmCode (jCode a ξ T c' η') s'))

  | jBeta {Γ : RawCtx} {γ : CtxCode} {A x C d : Expr} {a : TyCode γ}
      {ξ : TmCode γ a} {n : Nat} {Δ : RawCtx} {T : TelCode (pathCode a ξ) n}
      {c : TyCode (telTotal T)} {η : TmCode (branchCode a ξ T) (subTyCode c (rootTailCode a ξ T))}
      {args : Fin n → Expr} {s : SubCode γ (branchCode a ξ T)} :
      TmDeriv Γ γ (C.sub (eliminationSub x (.refl x) args))
        (subTyCode c (compCode (rootTailCode a ξ T) s))
        (.pathInduction n A x C d x (.refl x) args)
        (subTmCode (jCode a ξ T c η) (compCode (rootTailCode a ξ T) s)) →
      TmDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
        (C.sub (Expr.liftSubN n (reflexiveSub x))) (subTyCode c (rootTailCode a ξ T)) d η →
      SubDeriv Γ γ (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
        (argsSub args Expr.var) s →
      TmEqDeriv Γ γ (C.sub (eliminationSub x (.refl x) args))
        (subTyCode c (compCode (rootTailCode a ξ T) s))
        (.pathInduction n A x C d x (.refl x) args)
        (subTmCode (jCode a ξ T c η) (compCode (rootTailCode a ξ T) s))
        (d.sub (argsSub args Expr.var))
        (castCode (subTyComp_code c (rootTailCode a ξ T) s) (subTmCode η s))

  | jBetaReindex {Γ Ω : RawCtx} {γ ω : CtxCode} {A x C d : Expr} {a : TyCode γ}
      {ξ : TmCode γ a} {n : Nat} {Δ : RawCtx} {T : TelCode (pathCode a ξ) n}
      {c : TyCode (telTotal T)} {η : TmCode (branchCode a ξ T) (subTyCode c (rootTailCode a ξ T))}
      {args : Fin n → Expr} {ρ : RawSub} {s : SubCode ω (branchCode a ξ T)} :
      TmDeriv Ω ω (C.sub (argsSub args (consSub (.refl (x.sub ρ)) (consSub (x.sub ρ) ρ))))
        (subTyCode c (compCode (rootTailCode a ξ T) s))
        (.pathInduction n (A.sub ρ) (x.sub ρ) (C.sub (Expr.liftSubN (n+2) ρ))
          (d.sub (Expr.liftSubN n ρ)) (x.sub ρ) (.refl (x.sub ρ)) args)
        (subTmCode (jCode a ξ T c η) (compCode (rootTailCode a ξ T) s)) →
      TmDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
        (C.sub (Expr.liftSubN n (reflexiveSub x))) (subTyCode c (rootTailCode a ξ T)) d η →
      SubDeriv Ω ω (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T) (argsSub args ρ) s →
      TmEqDeriv Ω ω (C.sub (argsSub args (consSub (.refl (x.sub ρ)) (consSub (x.sub ρ) ρ))))
        (subTyCode c (compCode (rootTailCode a ξ T) s))
        (.pathInduction n (A.sub ρ) (x.sub ρ) (C.sub (Expr.liftSubN (n+2) ρ))
          (d.sub (Expr.liftSubN n ρ)) (x.sub ρ) (.refl (x.sub ρ)) args)
        (subTmCode (jCode a ξ T c η) (compCode (rootTailCode a ξ T) s))
        (d.sub (argsSub args ρ))
        (castCode (subTyComp_code c (rootTailCode a ξ T) s) (subTmCode η s))

  | jSub {Γ Ω : RawCtx} {γ ω : CtxCode} {A x C d : Expr} {a : TyCode γ}
      {ξ : TmCode γ a} {n : Nat} {Δ : RawCtx} {T : TelCode (pathCode a ξ) n}
      {c : TyCode (telTotal T)} {η : TmCode (branchCode a ξ T) (subTyCode c (rootTailCode a ξ T))}
      {σ : RawSub} {s : SubCode ω γ} :
      CtxDeriv Γ γ → TyDeriv Γ γ A a → TmDeriv Γ γ A a x ξ →
      TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T →
      TyDeriv (Δ ++ pathCtx Γ A x) (telTotal T) C c →
      TmDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
        (C.sub (Expr.liftSubN n (reflexiveSub x))) (subTyCode c (rootTailCode a ξ T)) d η →
      SubDeriv Ω ω Γ γ σ s →
      TmEqDeriv (subTail (Expr.liftSubN 2 σ) Δ ++ pathCtx Ω (A.sub σ) (x.sub σ))
        (telTotal (pathTailCode a ξ T s)) (C.sub (Expr.liftSubN (n+2) σ))
        (subTyCode c (pathTailMapCode a ξ T s))
        ((genericJRaw n A x C d).sub (Expr.liftSubN (n+2) σ))
        (subTmCode (jCode a ξ T c η) (pathTailMapCode a ξ T s))
        (genericJRaw n (A.sub σ) (x.sub σ)
          (C.sub (Expr.liftSubN (n+2) σ)) (d.sub (Expr.liftSubN n σ)))
        (jCode (subTyCode a s) (subTmCode ξ s) (pathTailCode a ξ T s)
          (subTyCode c (pathTailMapCode a ξ T s)) (reindexBranchCode a ξ T c η s))

inductive SubEqDeriv : (Δ : RawCtx) → (δ : CtxCode.{u}) → (Γ : RawCtx) → (γ : CtxCode.{u}) →
    RawSub → SubCode δ γ → RawSub → SubCode δ γ → Type (u+1) where
  | refl : SubDeriv Δ δ Γ γ σ s → SubEqDeriv Δ δ Γ γ σ s σ s
  | symm : SubEqDeriv Δ δ Γ γ σ s τ t → SubEqDeriv Δ δ Γ γ τ t σ s
  | trans : SubEqDeriv Δ δ Γ γ σ s τ t → SubEqDeriv Δ δ Γ γ τ t υ v →
      SubEqDeriv Δ δ Γ γ σ s υ v
  | comp : SubEqDeriv Δ δ Γ γ σ s σ' s' → SubEqDeriv Θ θ Δ δ τ t τ' t' →
      SubEqDeriv Θ θ Γ γ (fun n => (σ n).sub τ) (compCode s t)
        (fun n => (σ' n).sub τ') (compCode s' t')
  /-- Dependent pairing respects generated equality of both components. -/
  | pairCongr : TyDeriv Γ γ A a → SubEqDeriv Δ δ Γ γ σ s τ t → (h : s = t) →
      TmEqDeriv Δ δ (A.sub σ) (subTyCode a s) x ξ y
        (castCode (congrArg (subTyCode a) h.symm) η) →
      SubEqDeriv Δ δ (A :: Γ) (extendCode γ a)
        (consSub x σ) (pairCode a s ξ) (consSub y τ) (pairCode a t η)
  | idLeft : SubDeriv Δ δ Γ γ σ s →
      SubEqDeriv Δ δ Γ γ σ (compCode (idCode γ) s) σ s
  | idRight : SubDeriv Δ δ Γ γ σ s →
      SubEqDeriv Δ δ Γ γ (fun n => (σ n).sub Expr.var) (compCode s (idCode δ)) σ s
  | assoc : SubDeriv Δ δ Γ γ σ s → SubDeriv Θ θ Δ δ τ t → SubDeriv Ξ χ Θ θ υ v →
      SubEqDeriv Ξ χ Γ γ (fun n => ((σ n).sub τ).sub υ) (compCode (compCode s t) v)
        (fun n => (σ n).sub (fun i => (τ i).sub υ)) (compCode s (compCode t v))
  | weakenPair : TyDeriv Γ γ A a → SubDeriv Δ δ Γ γ σ s →
      TmDeriv Δ δ (A.sub σ) (subTyCode a s) x ξ →
      SubEqDeriv Δ δ Γ γ σ (compCode (weakenCode γ a) (pairCode a s ξ)) σ s
  | pairEta : TyDeriv Γ γ A a → SubDeriv Δ δ (A :: Γ) (extendCode γ a) σ s →
      SubEqDeriv Δ δ (A :: Γ) (extendCode γ a)
        (consSub (σ 0) (fun n => σ (n + 1))) (etaPairCode a s) σ s

end


mutual
/-- Every generated type conversion has its required semantic coherence. -/
theorem typeSound (e : TyEqDeriv Γ γ A a B b) : a = b :=
  match e with
  | .refl _ => rfl
  | .symm e => (typeSound e).symm
  | .trans e f => (typeSound e).trans (typeSound f)
  | .fiber e => congrArg fiberCode (termSound e)
  | .identity _ e f => by rw [termSound e, termSound f]
  | .identityType _ h _ _ => by cases h; rfl
  | .subCongr _ e => by rw [subSound e]
  | .sub e _ => by rw [typeSound e]
  | .subId _ => subTyId_code _
  | .subComp _ _ _ => subTyComp_code _ _ _
  | .baseSub _ => baseSub_code _
  | .fiberSub _ _ => fiberSub_code _ _
  | .identitySub _ _ _ _ => identitySub_code _ _ _ _
termination_by sizeOf e

theorem termSound (e : TmEqDeriv Γ γ A a t ξ v ν) : ξ = ν :=
  match e with
  | .refl _ => rfl
  | .symm e => (termSound e).symm
  | .trans e f => (termSound e).trans (termSound f)
  | .conv e _ _ => by rw [termSound e]
  | .sub e _ => by rw [termSound e]
  | .subId _ => subTmId_code _
  | .subComp _ _ _ => subTmComp_code _ _ _
  | .reflSub _ _ _ => reflSub_code _ _ _
  | .reflCongr _ h => by cases h; rfl
  | .subCongr _ _ h => by cases h; rfl
  | .variablePair _ _ _ => variablePair_code _ _ _
  | .jCongr _ _ _ _ _ h e => by
    have he := termSound e
    cases h
    simp only [castCode] at he ⊢
    rw [he]
  | .jCongrAt _ h e _ k _ _ => by
    have he := termSound e
    cases h
    cases k
    simp only [castCode] at he ⊢
    rw [he]
  | .jBeta _ _ _ => jBetaSub_code _ _ _ _ _ _
  | .jBetaReindex _ _ _ => jBetaSub_code _ _ _ _ _ _
  | .jSub _ _ _ _ _ _ _ => jSub_code _ _ _ _ _ _
termination_by sizeOf e

theorem subSound (e : SubEqDeriv Δ δ Γ γ σ s τ t) : s = t :=
  match e with
  | .refl _ => rfl
  | .symm e => (subSound e).symm
  | .trans e f => (subSound e).trans (subSound f)
  | .comp e f => by rw [subSound e, subSound f]
  | .pairCongr _ _ h e => by
    have he := termSound e
    cases h
    simp only [castCode] at he ⊢
    rw [he]
  | .idLeft _ => funext fun M => M.comp_id_left _
  | .idRight _ => funext fun M => M.comp_id_right _
  | .assoc _ _ _ => funext fun M => M.comp_assoc _ _ _
  | .weakenPair _ _ _ => weakenPair_code _ _ _
  | .pairEta _ _ => etaPair_code _ _
termination_by sizeOf e
end

/-- The public conversion operation derives coherence from the source rule. -/
def TmDeriv.convert (t : TmDeriv Γ γ A a x ξ) (e : TyEqDeriv Γ γ A a B b) :
    TmDeriv Γ γ B b x (castCode (typeSound e) ξ) := .conv t e (typeSound e)

def TmEqDeriv.convert (t : TmEqDeriv Γ γ A a x ξ y η) (e : TyEqDeriv Γ γ A a B b) :
    TmEqDeriv Γ γ B b x (castCode (typeSound e) ξ) y (castCode (typeSound e) η) :=
  .conv t e (typeSound e)

def TyEqDeriv.identityCongr (e : TyEqDeriv Γ γ A a B b)
    (hx : TmDeriv Γ γ A a x ξ) (hy : TmDeriv Γ γ A a y η) :
    TyEqDeriv Γ γ (.identity A x y) (identityCode a ξ η)
      (.identity B x y) (identityCode b (castCode (typeSound e) ξ) (castCode (typeSound e) η)) :=
  .identityType e (typeSound e) hx hy

def TmEqDeriv.reflexivityCongr (e : TmEqDeriv Γ γ A a x ξ y η) :
    TmEqDeriv Γ γ (.identity A x x) (identityCode a ξ ξ)
      (.refl x) (reflCode a ξ) (.refl y)
      (castCode (by rw [termSound e]) (reflCode a η)) :=
  .reflCongr e (termSound e)

def TmEqDeriv.substitutionCongr (hx : TmDeriv Γ γ A a x ξ)
    (e : SubEqDeriv Δ δ Γ γ σ s τ t) :
    TmEqDeriv Δ δ (A.sub σ) (subTyCode a s) (x.sub σ) (subTmCode ξ s)
      (x.sub τ) (castCode (congrArg (subTyCode a) (subSound e).symm) (subTmCode ξ t)) :=
  .subCongr hx e (subSound e)

/-- Public dependent pairing congruence obtains coherence from source equality. -/
def SubEqDeriv.pairingCongr (hA : TyDeriv Γ γ A a)
    (e : SubEqDeriv Δ δ Γ γ σ s τ t)
    (f : TmEqDeriv Δ δ (A.sub σ) (subTyCode a s) x ξ y
      (castCode (congrArg (subTyCode a) (subSound e).symm) η)) :=
  SubEqDeriv.pairCongr hA e (subSound e) f

/-- Replacing a term in a fixed substitution is the common nondependent case. -/
def SubEqDeriv.pairingTerm (hA : TyDeriv Γ γ A a) (hs : SubDeriv Δ δ Γ γ σ s)
    (e : TmEqDeriv Δ δ (A.sub σ) (subTyCode a s) x ξ y η) :=
  SubEqDeriv.pairCongr hA (.refl hs) rfl e

/-- The motive certificate is derived, never supplied by the author. -/
def TmEqDeriv.pathInductionCongr
    (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) (hx : TmDeriv Γ γ A a x ξ)
    (hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T)
    (e : TyEqDeriv (Δ ++ pathCtx Γ A x) (telTotal T) C c D c')
    (f : TmEqDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
      (C.sub (Expr.liftSubN n (reflexiveSub x))) (subTyCode c (rootTailCode a ξ T))
      d η d' (castCode (congrArg (fun c => subTyCode c (rootTailCode a ξ T))
        (typeSound e).symm) η')) :=
  TmEqDeriv.jCongr hΓ hA hx hT e (typeSound e) f

/-- Changing only a motive transports its existing branch by the generated
motive conversion; no branch equality or semantic certificate is an input. -/
def TmEqDeriv.pathInductionMotiveCongr
    (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) (hx : TmDeriv Γ γ A a x ξ)
    (hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T)
    (e : TyEqDeriv (Δ ++ pathCtx Γ A x) (telTotal T) C c D c')
    (hd : TmDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
      (C.sub (Expr.liftSubN n (reflexiveSub x))) (subTyCode c (rootTailCode a ξ T)) d η) :
    TmEqDeriv (Δ ++ pathCtx Γ A x) (telTotal T) C c
      (genericJRaw n A x C d) (jCode a ξ T c η)
      (genericJRaw n A x D d)
      (castCode (typeSound e).symm (jCode a ξ T c'
        (castCode (congrArg (fun c => subTyCode c (rootTailCode a ξ T)) (typeSound e)) η))) := by
  apply pathInductionCongr hΓ hA hx hT e
  have hc : castCode (congrArg (fun c => subTyCode c (rootTailCode a ξ T)) (typeSound e).symm)
      (castCode (congrArg (fun c => subTyCode c (rootTailCode a ξ T)) (typeSound e)) η) = η := by
    generalize typeSound e = h
    cases h
    rfl
  rw [hc]
  exact .refl hd

/-- Endpoint and tail equality is generated by substitution congruence;
all redundant certificates are supplied by the general soundness theorems. -/
def TmEqDeriv.pathInductionAtCongr
    {Γ Ω : RawCtx} {γ ω : CtxCode} {A x C D d d' : Expr} {a : TyCode γ}
    {ξ : TmCode γ a} {n : Nat} {Δ : RawCtx} {T : TelCode (pathCode a ξ) n}
    {c c' : TyCode (telTotal T)}
    {η : TmCode (branchCode a ξ T) (subTyCode c (rootTailCode a ξ T))}
    {η' : TmCode (branchCode a ξ T) (subTyCode c' (rootTailCode a ξ T))}
    {args args' : Fin n → Expr} {ρ ρ' : RawSub} {y y' p p' : Expr}
    {s s' : SubCode ω (telTotal T)}
    (e : TyEqDeriv (Δ ++ pathCtx Γ A x) (telTotal T) C c D c')
    (f : TmEqDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
      (C.sub (Expr.liftSubN n (reflexiveSub x))) (subTyCode c (rootTailCode a ξ T))
      d η d' (castCode (congrArg (fun c => subTyCode c (rootTailCode a ξ T))
        (typeSound e).symm) η'))
    (es : SubEqDeriv Ω ω (Δ ++ pathCtx Γ A x) (telTotal T)
      (argsSub args (consSub p (consSub y ρ))) s
      (argsSub args' (consSub p' (consSub y' ρ'))) s')
    (left : TmDeriv Ω ω (C.sub (argsSub args (consSub p (consSub y ρ)))) (subTyCode c s)
      (.pathInduction n (A.sub ρ) (x.sub ρ) (C.sub (Expr.liftSubN (n+2) ρ))
        (d.sub (Expr.liftSubN n ρ)) y p args) (subTmCode (jCode a ξ T c η) s))
    (right : TmDeriv Ω ω (D.sub (argsSub args' (consSub p' (consSub y' ρ')))) (subTyCode c' s')
      (.pathInduction n (A.sub ρ') (x.sub ρ') (D.sub (Expr.liftSubN (n+2) ρ'))
        (d'.sub (Expr.liftSubN n ρ')) y' p' args') (subTmCode (jCode a ξ T c' η') s')) :=
  TmEqDeriv.jCongrAt e (typeSound e) f es (subSound es) left right

theorem castCode_proof_independent {a b : TyCode γ} (h k : a = b) (ξ : TmCode γ a) :
    castCode h ξ = castCode k ξ := rfl

mutual
/-- Interpretation recurses on constructors and carries agreement with the code
index. This agreement is needed when a later section depends on earlier terms. -/
def interpretCtxChecked (M : Model.{u}) {Γ γ} (h : CtxDeriv Γ γ) :
    { c : M.Context // c = γ M } :=
  match h with
  | .empty => ⟨M.empty, rfl⟩
  | .ext hΓ hA => by
    obtain ⟨c, hc⟩ := interpretCtxChecked M hΓ
    obtain ⟨a, ha⟩ := interpretTyChecked M hA
    subst c; subst a
    exact ⟨M.extend _ _, rfl⟩
  | .path hΓ hA hx => by
    obtain ⟨g, hg⟩ := interpretCtxChecked M hΓ
    obtain ⟨a, ha⟩ := interpretTyChecked M hA
    obtain ⟨x, hx⟩ := interpretTmChecked M hx
    subst g; subst a; subst x
    exact ⟨M.toStructuralModel.pathContext _ _, rfl⟩
  | .telescope hΓ hT => by
    obtain ⟨g, hg⟩ := interpretCtxChecked M hΓ
    obtain ⟨T, hT⟩ := interpretTelChecked M hT
    subst g; subst T
    exact ⟨StructuralModel.Telescope.total _ _, rfl⟩
  | .branch hΓ hA hx hT => by
    obtain ⟨g, hg⟩ := interpretCtxChecked M hΓ
    obtain ⟨a, ha⟩ := interpretTyChecked M hA
    obtain ⟨x, hx⟩ := interpretTmChecked M hx
    obtain ⟨T, hT⟩ := interpretTelChecked M hT
    subst g; subst a; subst x; subst T
    exact ⟨StructuralModel.Telescope.total _
      (StructuralModel.Telescope.pullback _ _ (M.toStructuralModel.rootSub _ _)), rfl⟩
termination_by sizeOf h

def interpretTelChecked (M : Model.{u}) {Γ γ n Δ T} (h : TelDeriv Γ γ n Δ T) :
    { S : StructuralModel.Telescope M.toStructuralModel (γ M) n // S = T M } :=
  match h with
  | .nil hΓ => by
    obtain ⟨c, hc⟩ := interpretCtxChecked M hΓ
    subst c
    exact ⟨.nil, rfl⟩
  | .cons hA ht => by
    obtain ⟨a, ha⟩ := interpretTyChecked M hA
    obtain ⟨t, ht⟩ := interpretTelChecked M ht
    subst a; subst t
    exact ⟨.cons _ _, rfl⟩
  | .pullback hT hs => by
    obtain ⟨T, hT⟩ := interpretTelChecked M hT
    obtain ⟨s, hs⟩ := interpretSubChecked M hs
    subst T; subst s
    exact ⟨StructuralModel.Telescope.pullback _ _ _, rfl⟩
  | .pathReindex hΓ hA hx hT hs => by
    obtain ⟨g, hg⟩ := interpretCtxChecked M hΓ
    obtain ⟨a, ha⟩ := interpretTyChecked M hA
    obtain ⟨x, hx⟩ := interpretTmChecked M hx
    obtain ⟨T, hT⟩ := interpretTelChecked M hT
    obtain ⟨s, hs⟩ := interpretSubChecked M hs
    subst g; subst a; subst x; subst T; subst s
    exact ⟨M.toStructuralModel.pathTail _ _ _ _, rfl⟩
termination_by sizeOf h

def interpretTyChecked (M : Model.{u}) {Γ γ A a} (h : TyDeriv Γ γ A a) :
    { f : M.Family (γ M) // f = a M } :=
  match h with
  | .base hΓ => by
    obtain ⟨c, hc⟩ := interpretCtxChecked M hΓ
    subst c
    exact ⟨M.base _, rfl⟩
  | .fiber hx => by
    obtain ⟨x, hx⟩ := interpretTmChecked M hx
    subst x
    exact ⟨M.fiber _, rfl⟩
  | .identity hA hx hy => by
    obtain ⟨A, hA⟩ := interpretTyChecked M hA
    obtain ⟨x, hx⟩ := interpretTmChecked M hx
    obtain ⟨y, hy⟩ := interpretTmChecked M hy
    subst A; subst x; subst y
    exact ⟨M.identity _ _ _, rfl⟩
  | .sub hA hσ => by
    obtain ⟨A, hA⟩ := interpretTyChecked M hA
    obtain ⟨σ, hσ⟩ := interpretSubChecked M hσ
    subst A; subst σ
    exact ⟨M.subTy _ _, rfl⟩
termination_by sizeOf h

def interpretTmChecked (M : Model.{u}) {Γ γ A a t ξ} (h : TmDeriv Γ γ A a t ξ) :
    { s : M.Section (γ M) (a M) // s = ξ M } :=
  match h with
  | .var hΓ hA => by
    obtain ⟨c, hc⟩ := interpretCtxChecked M hΓ
    obtain ⟨a, ha⟩ := interpretTyChecked M hA
    subst c; subst a
    exact ⟨M.genericVariable _ _, rfl⟩
  | .refl hA hx => by
    obtain ⟨A, hA⟩ := interpretTyChecked M hA
    obtain ⟨x, hx⟩ := interpretTmChecked M hx
    subst A; subst x
    exact ⟨M.reflexivity _ _, rfl⟩
  | .sub ht hσ => by
    obtain ⟨t, ht⟩ := interpretTmChecked M ht
    obtain ⟨σ, hσ⟩ := interpretSubChecked M hσ
    subst t; subst σ
    exact ⟨M.subTm _ _, rfl⟩
  | .pathInduction hΓ hA hx hT hC hd hy hp hs => by
    obtain ⟨g, hg⟩ := interpretCtxChecked M hΓ
    obtain ⟨a, ha⟩ := interpretTyChecked M hA
    obtain ⟨x, hx⟩ := interpretTmChecked M hx
    obtain ⟨T, hT⟩ := interpretTelChecked M hT
    obtain ⟨C, hC⟩ := interpretTyChecked M hC
    obtain ⟨d, hd⟩ := interpretTmChecked M hd
    obtain ⟨y, hy⟩ := interpretTmChecked M hy
    obtain ⟨p, hp⟩ := interpretTmChecked M hp
    obtain ⟨s, hs⟩ := interpretSubChecked M hs
    subst g; subst a; subst x; subst T; subst C; subst d; subst y; subst p; subst s
    exact ⟨M.subTm (M.j _ _ _ _ _) _, rfl⟩
  | .pathInductionReindex hΓ hA hx hT hC hd hr hy hp hs => by
    obtain ⟨g, hg⟩ := interpretCtxChecked M hΓ
    obtain ⟨a, ha⟩ := interpretTyChecked M hA
    obtain ⟨x, hx⟩ := interpretTmChecked M hx
    obtain ⟨T, hT⟩ := interpretTelChecked M hT
    obtain ⟨C, hC⟩ := interpretTyChecked M hC
    obtain ⟨d, hd⟩ := interpretTmChecked M hd
    obtain ⟨r, hr⟩ := interpretSubChecked M hr
    obtain ⟨y, hy⟩ := interpretTmChecked M hy
    obtain ⟨p, hp⟩ := interpretTmChecked M hp
    obtain ⟨s, hs⟩ := interpretSubChecked M hs
    subst g; subst a; subst x; subst T; subst C; subst d; subst r; subst y; subst p; subst s
    exact ⟨M.subTm (M.j _ _ _ _ _) _, rfl⟩
  | .genericJ hΓ hA hx hT hC hd => by
    obtain ⟨g, hg⟩ := interpretCtxChecked M hΓ
    obtain ⟨a, ha⟩ := interpretTyChecked M hA
    obtain ⟨x, hx⟩ := interpretTmChecked M hx
    obtain ⟨T, hT⟩ := interpretTelChecked M hT
    obtain ⟨C, hC⟩ := interpretTyChecked M hC
    obtain ⟨d, hd⟩ := interpretTmChecked M hd
    subst g; subst a; subst x; subst T; subst C; subst d
    exact ⟨M.j _ _ _ _ _, rfl⟩
  | .reindexJBranch hΓ hA hx hT hC hd hs => by
    obtain ⟨g, hg⟩ := interpretCtxChecked M hΓ
    obtain ⟨a, ha⟩ := interpretTyChecked M hA
    obtain ⟨x, hx⟩ := interpretTmChecked M hx
    obtain ⟨T, hT⟩ := interpretTelChecked M hT
    obtain ⟨C, hC⟩ := interpretTyChecked M hC
    obtain ⟨d, hd⟩ := interpretTmChecked M hd
    obtain ⟨s, hs⟩ := interpretSubChecked M hs
    subst g; subst a; subst x; subst T; subst C; subst d; subst s
    exact ⟨M.toStructuralModel.reindexBranch _ _ _ _ _ _, rfl⟩
  | .conv ht _ he => by
    obtain ⟨t, ht⟩ := interpretTmChecked M ht
    cases he
    subst t
    exact ⟨_, rfl⟩
termination_by sizeOf h

def interpretSubChecked (M : Model.{u}) {Δ δ Γ γ σ s} (h : SubDeriv Δ δ Γ γ σ s) :
    { f : M.Substitution (δ M) (γ M) // f = s M } :=
  match h with
  | .id hΓ => by
    obtain ⟨c, hc⟩ := interpretCtxChecked M hΓ
    subst c
    exact ⟨M.idSub _, rfl⟩
  | .comp hσ hτ => by
    obtain ⟨σ, hσ⟩ := interpretSubChecked M hσ
    obtain ⟨τ, hτ⟩ := interpretSubChecked M hτ
    subst σ; subst τ
    exact ⟨M.compSub _ _, rfl⟩
  | .weaken hΓ hA => by
    obtain ⟨c, hc⟩ := interpretCtxChecked M hΓ
    obtain ⟨a, ha⟩ := interpretTyChecked M hA
    subst c; subst a
    exact ⟨M.weaken _ _, rfl⟩
  | .projection hΓ hT => by
    obtain ⟨g, hg⟩ := interpretCtxChecked M hΓ
    obtain ⟨T, hT⟩ := interpretTelChecked M hT
    subst g; subst T
    exact ⟨StructuralModel.Telescope.projection _ _, rfl⟩
  | .root hΓ hA hx => by
    obtain ⟨g, hg⟩ := interpretCtxChecked M hΓ
    obtain ⟨a, ha⟩ := interpretTyChecked M hA
    obtain ⟨x, hx⟩ := interpretTmChecked M hx
    subst g; subst a; subst x
    exact ⟨M.toStructuralModel.rootSub _ _, rfl⟩
  | .rootTail hΓ hA hx hT => by
    obtain ⟨g, hg⟩ := interpretCtxChecked M hΓ
    obtain ⟨a, ha⟩ := interpretTyChecked M hA
    obtain ⟨x, hx⟩ := interpretTmChecked M hx
    obtain ⟨T, hT⟩ := interpretTelChecked M hT
    subst g; subst a; subst x; subst T
    exact ⟨M.toStructuralModel.rootTail _ _ _, rfl⟩
  | .pathTailMap hΓ hA hx hT hs => by
    obtain ⟨g, hg⟩ := interpretCtxChecked M hΓ
    obtain ⟨a, ha⟩ := interpretTyChecked M hA
    obtain ⟨x, hx⟩ := interpretTmChecked M hx
    obtain ⟨T, hT⟩ := interpretTelChecked M hT
    obtain ⟨s, hs⟩ := interpretSubChecked M hs
    subst g; subst a; subst x; subst T; subst s
    exact ⟨M.toStructuralModel.pathTailMap _ _ _ _, rfl⟩
  | .pair hA hσ ht => by
    obtain ⟨a, ha⟩ := interpretTyChecked M hA
    obtain ⟨σ, hσ⟩ := interpretSubChecked M hσ
    obtain ⟨t, ht⟩ := interpretTmChecked M ht
    subst a; subst σ; subst t
    exact ⟨M.pairSub _ _ _, rfl⟩
termination_by sizeOf h
end

def interpretCtx (M : Model) (h : CtxDeriv Γ γ) := (interpretCtxChecked M h).val
def interpretTy (M : Model) (h : TyDeriv Γ γ A a) := (interpretTyChecked M h).val
def interpretTm (M : Model) (h : TmDeriv Γ γ A a t ξ) := (interpretTmChecked M h).val
def interpretSub (M : Model) (h : SubDeriv Δ δ Γ γ σ s) := (interpretSubChecked M h).val

theorem interpretCtx_agrees (M : Model) (h : CtxDeriv Γ γ) : interpretCtx M h = γ M :=
  (interpretCtxChecked M h).property
theorem interpretTy_agrees (M : Model) (h : TyDeriv Γ γ A a) : interpretTy M h = a M :=
  (interpretTyChecked M h).property
theorem interpretTm_agrees (M : Model) (h : TmDeriv Γ γ A a t ξ) : interpretTm M h = ξ M :=
  (interpretTmChecked M h).property
theorem interpretSub_agrees (M : Model) (h : SubDeriv Δ δ Γ γ σ s) : interpretSub M h = s M :=
  (interpretSubChecked M h).property


/-- Canonical endpoint instantiation is assembled from generated source
substitutions. The equality transport below changes raw substitution arithmetic. -/
def SubDeriv.reflexiveEndpoint
    (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) (hx : TmDeriv Γ γ A a x ξ)
    (hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T)
    {args : Fin n → Expr}
    (hs : SubDeriv Γ γ (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
      (argsSub args Expr.var) s) :
    SubDeriv Γ γ (Δ ++ pathCtx Γ A x) (telTotal T)
      (eliminationSub x (.refl x) args) (compCode (rootTailCode a ξ T) s) := by
  have h := SubDeriv.comp (SubDeriv.rootTail hΓ hA hx hT) hs
  rw [liftSubN_argsSub] at h
  simpa only [Expr.sub_id, reflexiveSub, eliminationSub] using h

/-- Reflexive contextual J, with any earlier context and any finite dependent tail. -/
def TmDeriv.reflexiveJ
    (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) (hx : TmDeriv Γ γ A a x ξ)
    (hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T)
    {args : Fin n → Expr}
    (hC : TyDeriv (Δ ++ pathCtx Γ A x) (telTotal T) C c)
    (hd : TmDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
      (C.sub (Expr.liftSubN n (reflexiveSub x))) (subTyCode c (rootTailCode a ξ T)) d η)
    (hs : SubDeriv Γ γ (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
      (argsSub args Expr.var) s) :
    TmDeriv Γ γ (C.sub (eliminationSub x (.refl x) args))
      (subTyCode c (compCode (rootTailCode a ξ T) s))
      (.pathInduction n A x C d x (.refl x) args)
      (subTmCode (jCode a ξ T c η) (compCode (rootTailCode a ξ T) s)) :=
  .pathInduction hΓ hA hx hT hC hd hx (.refl hA hx)
    (SubDeriv.reflexiveEndpoint hΓ hA hx hT hs)

def TmEqDeriv.contextualBeta
    (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) (hx : TmDeriv Γ γ A a x ξ)
    (hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T)
    {args : Fin n → Expr}
    (hC : TyDeriv (Δ ++ pathCtx Γ A x) (telTotal T) C c)
    (hd : TmDeriv (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
      (C.sub (Expr.liftSubN n (reflexiveSub x))) (subTyCode c (rootTailCode a ξ T)) d η)
    (hs : SubDeriv Γ γ (subTail (reflexiveSub x) Δ ++ Γ) (branchCode a ξ T)
      (argsSub args Expr.var) s) :
    TmEqDeriv Γ γ (C.sub (eliminationSub x (.refl x) args))
      (subTyCode c (compCode (rootTailCode a ξ T) s))
      (.pathInduction n A x C d x (.refl x) args)
      (subTmCode (jCode a ξ T c η) (compCode (rootTailCode a ξ T) s))
      (d.sub (argsSub args Expr.var))
      (castCode (subTyComp_code c (rootTailCode a ξ T) s) (subTmCode η s)) :=
  .jBeta (TmDeriv.reflexiveJ hΓ hA hx hT hC hd hs) hd hs

/-- The guarded coherence proof cannot change the resulting source derivation. -/
theorem TmDeriv.conv_proof_independent (t : TmDeriv Γ γ A a x ξ)
    (e : TyEqDeriv Γ γ A a B b) (h k : a = b) :
    TmDeriv.conv t e h = TmDeriv.conv t e k := rfl

namespace Checked

def emptyContext : CtxDeriv [] emptyCode := .empty
def emptyBase : TyDeriv [] emptyCode .base (baseCode emptyCode) := .base emptyContext
def pointContext : CtxDeriv [.base] (extendCode emptyCode (baseCode emptyCode)) :=
  .ext emptyContext emptyBase

def point := TmDeriv.convert (TmDeriv.var emptyContext emptyBase)
  (TyEqDeriv.baseSub (SubDeriv.weaken emptyContext emptyBase))

def reflexivity := TmDeriv.refl (TyDeriv.base pointContext) point

/-- Reusable source reflexivity is interpreted by each supplied model's rule. -/
theorem reflexivity_interpretation (M : Model) :
    HEq (interpretTm M reflexivity) (M.reflexivity _ (interpretTm M point)) := by
  rw [interpretTm_agrees, interpretTm_agrees]
  rfl

/-- The semantic equality used for conversion is generated from base reindexing. -/
theorem point_conversion (M : Model) :
    HEq (interpretTm M point)
      (M.genericVariable M.empty (M.base M.empty)) := by
  rw [interpretTm_agrees]
  exact castCode_eval _ _ M

end Checked
end SquareKit.Internal.PathTransport.Typed
