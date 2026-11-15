import SquareKit.Internal.PathTransport.InterpretationMaps
import SquareKit.Internal.PathTransport.Typed

/-! Signature-preserving maps act on the existing generated interpretation.
The two signature laws supplement the structural and primitive J laws; no
preservation of arbitrary model-indexed annotation functions is assumed. -/

namespace SquareKit.Internal.PathTransport.Typed
universe u v

/-- A structural/J map together with preservation of the supported signature. -/
structure SignatureMap (M : Model.{u}) (N : Model.{v}) extends ModelMap M N where
  base : ∀ Γ, family (M.base Γ) = N.base (context Γ)
  fiber : ∀ {Γ} (x : M.Section Γ (M.base Γ)),
    family (M.fiber x) = N.fiber
      (cast (congrArg (N.Section (context Γ)) (base Γ)) (mapTm x))

namespace SignatureMap
variable {M N : Model.{u}} (F : SignatureMap M N)
open StructuralModel

/-- These predicates retain the shared indices needed by mutual induction. -/
def CtxPres (γ : CtxCode.{u}) : Prop := F.context (γ M) = γ N
def TyPres {γ : CtxCode.{u}} (a : TyCode γ) : Prop :=
  F.CtxPres γ ∧ HEq (F.family (a M)) (a N)
def TmPres {γ : CtxCode.{u}} {a : TyCode γ} (x : TmCode γ a) : Prop :=
  F.TyPres a ∧ HEq (F.mapTm (x M)) (x N)
def SubPres {δ γ : CtxCode.{u}} (s : SubCode δ γ) : Prop :=
  F.CtxPres δ ∧ F.CtxPres γ ∧ HEq (F.substitution (s M)) (s N)
def TelPres {γ : CtxCode.{u}} {n : Nat} (T : TelCode γ n) : Prop :=
  F.CtxPres γ ∧ HEq (F.telescope (T M)) (T N)

private theorem extend_pres {γ : CtxCode} {a : TyCode γ} (ha : F.TyPres a) :
    F.CtxPres (extendCode γ a) :=
  (F.extend _).trans (N.toStructuralModel.extend_heq ha.1 ha.2)

private theorem path_pres {γ : CtxCode} {a : TyCode γ} {x : TmCode γ a}
    (hx : F.TmPres x) : F.CtxPres (pathCode a x) :=
  (F.pathContext _ _).trans (N.toStructuralModel.pathContext_heq hx.1.1 hx.1.2 hx.2)

private theorem total_pres {γ : CtxCode} {n} {T : TelCode γ n} (hT : F.TelPres T) :
    F.CtxPres (telTotal T) :=
  (F.telescope_total _).trans (Telescope.total_heq N.toStructuralModel hT.1 hT.2)

private theorem base_pres {γ : CtxCode} (hγ : F.CtxPres γ) : F.TyPres (baseCode γ) := by
  refine ⟨hγ, (heq_of_eq (F.base _)).trans ?_⟩
  exact (show ∀ {Γ Δ : N.Context}, Γ = Δ → HEq (N.base Γ) (N.base Δ) from
    fun h => by cases h; rfl) hγ

private theorem fiber_heq {Γ Δ : N.Context} {x : N.Section Γ (N.base Γ)}
    {y : N.Section Δ (N.base Δ)} (hΓ : Γ = Δ) (hx : HEq x y) :
    HEq (N.fiber x) (N.fiber y) := by
  cases hΓ; cases eq_of_heq hx; rfl

private theorem fiber_pres {γ : CtxCode} {x : TmCode γ (baseCode γ)} (hx : F.TmPres x) :
    F.TyPres (fiberCode x) := by
  refine ⟨hx.1.1, (heq_of_eq (F.fiber _)).trans ?_⟩
  exact fiber_heq hx.1.1 ((cast_heq _ _).trans hx.2)

private theorem identity_pres {γ : CtxCode} {a : TyCode γ} {x y : TmCode γ a}
    (hx : F.TmPres x) (hy : F.TmPres y) : F.TyPres (identityCode a x y) :=
  ⟨hx.1.1, (heq_of_eq (F.identity _ _ _)).trans
    (N.toStructuralModel.identity_heq hx.1.1 hx.1.2 hx.2 hy.2)⟩

private theorem subTy_pres {γ δ : CtxCode} {a : TyCode γ} {s : SubCode δ γ}
    (ha : F.TyPres a) (hs : F.SubPres s) : F.TyPres (subTyCode a s) :=
  ⟨hs.1, (heq_of_eq (F.subTy _ _)).trans
    (N.toStructuralModel.subTy_heq ha.1 hs.1 ha.2 hs.2.2)⟩

private theorem subTm_pres {γ δ : CtxCode} {a : TyCode γ} {x : TmCode γ a}
    {s : SubCode δ γ} (hx : F.TmPres x) (hs : F.SubPres s) : F.TmPres (subTmCode x s) :=
  ⟨subTy_pres F hx.1 hs, (F.subTm _ _).trans
    (N.toStructuralModel.subTm_heq hx.1.1 hs.1 hx.1.2 hx.2 hs.2.2)⟩

private theorem weaken_pres {γ : CtxCode} {a : TyCode γ} (ha : F.TyPres a) :
    F.SubPres (weakenCode γ a) :=
  ⟨extend_pres F ha, ha.1, (F.weaken _).trans (N.toStructuralModel.weaken_heq ha.1 ha.2)⟩

private theorem var_pres {γ : CtxCode} {a : TyCode γ} (ha : F.TyPres a) :
    F.TmPres (varCode γ a) :=
  ⟨subTy_pres F ha (weaken_pres F ha),
    (F.mapVariable _).trans (N.toStructuralModel.variable_heq ha.1 ha.2)⟩

private theorem refl_heq {Γ Δ : N.Context} {A : N.Family Γ} {B : N.Family Δ}
    {x : N.Section Γ A} {y : N.Section Δ B} (hΓ : Γ = Δ) (hA : HEq A B) (hx : HEq x y) :
    HEq (N.reflexivity A x) (N.reflexivity B y) := by
  cases hΓ; cases eq_of_heq hA; cases eq_of_heq hx; rfl

private theorem refl_pres {γ : CtxCode} {a : TyCode γ} {x : TmCode γ a}
    (hx : F.TmPres x) : F.TmPres (reflCode a x) :=
  ⟨identity_pres F hx hx, (F.reflexivity _ _).trans (refl_heq hx.1.1 hx.1.2 hx.2)⟩

private theorem id_pres {γ : CtxCode} (hγ : F.CtxPres γ) : F.SubPres (idCode γ) := by
  refine ⟨hγ, hγ, (heq_of_eq (F.id _)).trans ?_⟩
  exact (show ∀ {Γ Δ : N.Context}, Γ = Δ → HEq (N.idSub Γ) (N.idSub Δ) from
    fun h => by cases h; rfl) hγ

private theorem comp_pres {γ δ θ : CtxCode} {s : SubCode δ γ} {t : SubCode θ δ}
    (hs : F.SubPres s) (ht : F.SubPres t) : F.SubPres (compCode s t) :=
  ⟨ht.1, hs.2.1, (heq_of_eq (F.comp _ _)).trans
    (N.toStructuralModel.comp_heq hs.2.1 hs.1 ht.1 hs.2.2 ht.2.2)⟩

private theorem pair_pres {γ δ : CtxCode} {a : TyCode γ} {s : SubCode δ γ}
    {x : TmCode δ (subTyCode a s)} (ha : F.TyPres a) (hs : F.SubPres s)
    (hx : F.TmPres x) : F.SubPres (pairCode a s x) := by
  refine ⟨hs.1, extend_pres F ha, (F.pair _ _ _).trans ?_⟩
  exact N.toStructuralModel.pair_heq ha.1 hs.1 ha.2 hs.2.2
    ((cast_heq _ _).trans hx.2)

private theorem nil_pres {γ : CtxCode} (hγ : F.CtxPres γ) : F.TelPres (telNil γ) := by
  refine ⟨hγ, ?_⟩
  change HEq (Telescope.nil : Telescope N.toStructuralModel (F.context (γ M)) 0)
    (Telescope.nil : Telescope N.toStructuralModel (γ N) 0)
  exact (show ∀ {Γ Δ : N.Context}, Γ = Δ →
    HEq (Telescope.nil : Telescope N.toStructuralModel Γ 0)
      (Telescope.nil : Telescope N.toStructuralModel Δ 0) from
    fun h => by cases h; rfl) hγ

private theorem cons_pres {γ : CtxCode} {a : TyCode γ} {n}
    {T : TelCode (extendCode γ a) n} (ha : F.TyPres a) (hT : F.TelPres T) :
    F.TelPres (telCons a T) := by
  refine ⟨ha.1, ?_⟩
  exact Telescope.cons_heq N.toStructuralModel ha.1 ha.2 ((cast_heq _ _).trans hT.2)

private theorem pullback_pres {γ δ : CtxCode} {n} {T : TelCode γ n} {s : SubCode δ γ}
    (hT : F.TelPres T) (hs : F.SubPres s) : F.TelPres (telPullback T s) :=
  ⟨hs.1, (heq_of_eq (F.telescope_pullback _ _)).trans
    (Telescope.pullback_heq N.toStructuralModel hT.1 hs.1 hT.2 hs.2.2)⟩

private theorem projection_pres {γ : CtxCode} {n} {T : TelCode γ n}
    (hT : F.TelPres T) : F.SubPres (projectionCode T) :=
  ⟨total_pres F hT, hT.1, (F.telescope_projection _).trans
    (Telescope.projection_heq N.toStructuralModel hT.1 hT.2)⟩

private theorem root_pres {γ : CtxCode} {a : TyCode γ} {x : TmCode γ a}
    (hx : F.TmPres x) : F.SubPres (rootCode a x) :=
  ⟨hx.1.1, path_pres F hx, (F.rootSub _ _).trans
    (N.toStructuralModel.rootSub_heq hx.1.1 hx.1.2 hx.2)⟩

private theorem branch_pres {γ : CtxCode} {a : TyCode γ} {x : TmCode γ a} {n}
    {T : TelCode (pathCode a x) n} (hx : F.TmPres x) (hT : F.TelPres T) :
    F.CtxPres (branchCode a x T) := total_pres F (pullback_pres F hT (root_pres F hx))

private theorem rootTail_congr {Γ Γ' : N.Context} (hΓ : Γ = Γ')
    {A : N.Family Γ} {A' : N.Family Γ'} (hA : HEq A A')
    {x : N.Section Γ A} {x' : N.Section Γ' A'} (hx : HEq x x')
    {n} {T : Telescope N.toStructuralModel (N.toStructuralModel.pathContext A x) n}
    {T' : Telescope N.toStructuralModel (N.toStructuralModel.pathContext A' x') n}
    (hT : HEq T T') :
    HEq (N.toStructuralModel.rootTail A x T) (N.toStructuralModel.rootTail A' x' T') := by
  cases hΓ; cases eq_of_heq hA; cases eq_of_heq hx; cases eq_of_heq hT; rfl

private theorem rootTail_pres {γ : CtxCode} {a : TyCode γ} {x : TmCode γ a} {n}
    {T : TelCode (pathCode a x) n} (hx : F.TmPres x) (hT : F.TelPres T) :
    F.SubPres (rootTailCode a x T) :=
  ⟨branch_pres F hx hT, total_pres F hT, (F.rootTail _ _ _).trans
    (rootTail_congr hx.1.1 hx.1.2 hx.2 ((cast_heq _ _).trans hT.2))⟩

private theorem pathTail_congr {Γ Γ' Δ Δ' : N.Context} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    {A : N.Family Γ} {A' : N.Family Γ'} (hA : HEq A A')
    {x : N.Section Γ A} {x' : N.Section Γ' A'} (hx : HEq x x')
    {n} {T : Telescope N.toStructuralModel (N.toStructuralModel.pathContext A x) n}
    {T' : Telescope N.toStructuralModel (N.toStructuralModel.pathContext A' x') n}
    (hT : HEq T T') {s : N.Substitution Δ Γ} {s' : N.Substitution Δ' Γ'} (hs : HEq s s') :
    HEq (N.toStructuralModel.pathTail A x T s) (N.toStructuralModel.pathTail A' x' T' s') := by
  cases hΓ; cases hΔ; cases eq_of_heq hA; cases eq_of_heq hx
  cases eq_of_heq hT; cases eq_of_heq hs; rfl

private theorem pathTail_pres {γ δ : CtxCode} {a : TyCode γ} {x : TmCode γ a} {n}
    {T : TelCode (pathCode a x) n} {s : SubCode δ γ}
    (hx : F.TmPres x) (hT : F.TelPres T) (hs : F.SubPres s) :
    F.TelPres (pathTailCode a x T s) :=
  ⟨path_pres F (subTm_pres F hx hs), (F.pathTail _ _ _ _).trans
    (pathTail_congr hx.1.1 hs.1 hx.1.2 hx.2 ((cast_heq _ _).trans hT.2) hs.2.2)⟩

private theorem pathTailMap_congr {Γ Γ' Δ Δ' : N.Context} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    {A : N.Family Γ} {A' : N.Family Γ'} (hA : HEq A A')
    {x : N.Section Γ A} {x' : N.Section Γ' A'} (hx : HEq x x')
    {n} {T : Telescope N.toStructuralModel (N.toStructuralModel.pathContext A x) n}
    {T' : Telescope N.toStructuralModel (N.toStructuralModel.pathContext A' x') n}
    (hT : HEq T T') {s : N.Substitution Δ Γ} {s' : N.Substitution Δ' Γ'} (hs : HEq s s') :
    HEq (N.toStructuralModel.pathTailMap A x T s)
      (N.toStructuralModel.pathTailMap A' x' T' s') := by
  cases hΓ; cases hΔ; cases eq_of_heq hA; cases eq_of_heq hx
  cases eq_of_heq hT; cases eq_of_heq hs; rfl

private theorem pathTailMap_pres {γ δ : CtxCode} {a : TyCode γ} {x : TmCode γ a} {n}
    {T : TelCode (pathCode a x) n} {s : SubCode δ γ}
    (hx : F.TmPres x) (hT : F.TelPres T) (hs : F.SubPres s) :
    F.SubPres (pathTailMapCode a x T s) :=
  ⟨total_pres F (pathTail_pres F hx hT hs), total_pres F hT, (F.pathTailMap _ _ _ _).trans
    (pathTailMap_congr hx.1.1 hs.1 hx.1.2 hx.2 ((cast_heq _ _).trans hT.2) hs.2.2)⟩

private theorem j_pres {γ : CtxCode} {a : TyCode γ} {x : TmCode γ a} {n}
    {T : TelCode (pathCode a x) n} {c : TyCode (telTotal T)}
    {d : TmCode (branchCode a x T) (subTyCode c (rootTailCode a x T))}
    (hx : F.TmPres x) (hT : F.TelPres T) (hc : F.TyPres c) (hd : F.TmPres d) :
    F.TmPres (jCode a x T c d) :=
  ⟨hc, (F.mapJ _ _ _ _ _).trans (N.j_heq hx.1.1 hx.1.2 hx.2
    ((cast_heq _ _).trans hT.2) ((cast_heq _ _).trans hc.2)
    ((F.jBranch_heq _ _ _ _ _).trans hd.2))⟩

private theorem reindexBranch_congr {Γ Γ' Δ Δ' : N.Context} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    {A : N.Family Γ} {A' : N.Family Γ'} (hA : HEq A A')
    {x : N.Section Γ A} {x' : N.Section Γ' A'} (hx : HEq x x')
    {n} {T : Telescope N.toStructuralModel (N.toStructuralModel.pathContext A x) n}
    {T' : Telescope N.toStructuralModel (N.toStructuralModel.pathContext A' x') n}
    (hT : HEq T T') {s : N.Substitution Δ Γ} {s' : N.Substitution Δ' Γ'} (hs : HEq s s')
    {C : N.Family T.total} {C' : N.Family T'.total} (hC : HEq C C')
    {d : N.Section _ (N.subTy C (N.toStructuralModel.rootTail A x T))}
    {d' : N.Section _ (N.subTy C' (N.toStructuralModel.rootTail A' x' T'))} (hd : HEq d d') :
    HEq (N.toStructuralModel.reindexBranch A x T s C d)
      (N.toStructuralModel.reindexBranch A' x' T' s' C' d') := by
  cases hΓ; cases hΔ; cases eq_of_heq hA; cases eq_of_heq hx
  cases eq_of_heq hT; cases eq_of_heq hs; cases eq_of_heq hC; cases eq_of_heq hd; rfl

private theorem reindexBranch_pres {γ δ : CtxCode} {a : TyCode γ} {x : TmCode γ a} {n}
    {T : TelCode (pathCode a x) n} {c : TyCode (telTotal T)}
    {d : TmCode (branchCode a x T) (subTyCode c (rootTailCode a x T))} {s : SubCode δ γ}
    (hx : F.TmPres x) (hT : F.TelPres T) (hc : F.TyPres c) (hd : F.TmPres d)
    (hs : F.SubPres s) : F.TmPres (reindexBranchCode a x T c d s) :=
  ⟨subTy_pres F (subTy_pres F hc (pathTailMap_pres F hx hT hs))
      (rootTail_pres F (subTm_pres F hx hs) (pathTail_pres F hx hT hs)),
    (F.reindexBranch _ _ _ _ _ _).trans (reindexBranch_congr hx.1.1 hs.1 hx.1.2 hx.2
      ((cast_heq _ _).trans hT.2) hs.2.2 ((cast_heq _ _).trans hc.2)
      ((F.jBranch_heq _ _ _ _ _).trans hd.2))⟩

private theorem cast_pres {γ : CtxCode} {a b : TyCode γ} {x : TmCode γ a}
    (e : a = b) (hx : F.TmPres x) : F.TmPres (castCode e x) := by
  cases e
  exact hx

mutual
/-- Preservation is proved for generated contexts, including path and branch contexts. -/
theorem generatedCtx (h : CtxDeriv Γ γ) : F.CtxPres γ :=
  match h with
  | .empty => F.empty
  | .ext _ ha => extend_pres F (generatedTy ha)
  | .path _ _ hx => path_pres F (generatedTm hx)
  | .telescope _ hT => total_pres F (generatedTel hT)
  | .branch _ _ hx hT => branch_pres F (generatedTm hx) (generatedTel hT)
termination_by sizeOf h

/-- Every binder and every generated pullback is preserved. -/
theorem generatedTel (h : TelDeriv Γ γ n Δ T) : F.TelPres T :=
  match h with
  | .nil hγ => nil_pres F (generatedCtx hγ)
  | .cons ha hT => cons_pres F (generatedTy ha) (generatedTel hT)
  | .pullback hT hs => pullback_pres F (generatedTel hT) (generatedSub hs)
  | .pathReindex _ _ hx hT hs =>
      pathTail_pres F (generatedTm hx) (generatedTel hT) (generatedSub hs)
termination_by sizeOf h

/-- Signature preservation suffices for all generated families. -/
theorem generatedTy (h : TyDeriv Γ γ A a) : F.TyPres a :=
  match h with
  | .base hγ => base_pres F (generatedCtx hγ)
  | .fiber hx => fiber_pres F (generatedTm hx)
  | .identity _ hx hy => identity_pres F (generatedTm hx) (generatedTm hy)
  | .sub ha hs => subTy_pres F (generatedTy ha) (generatedSub hs)
termination_by sizeOf h

/-- This includes generic J, reindexed branches, and generated conversion. -/
theorem generatedTm (h : TmDeriv Γ γ A a t x) : F.TmPres x :=
  match h with
  | .var _ ha => var_pres F (generatedTy ha)
  | .refl _ hx => refl_pres F (generatedTm hx)
  | .sub hx hs => subTm_pres F (generatedTm hx) (generatedSub hs)
  | .pathInduction _ _ hx hT hc hd _ _ hs =>
      subTm_pres F (j_pres F (generatedTm hx) (generatedTel hT)
        (generatedTy hc) (generatedTm hd)) (generatedSub hs)
  | .pathInductionReindex _ _ hx hT hc hd _ _ _ hs =>
      subTm_pres F (j_pres F (generatedTm hx) (generatedTel hT)
        (generatedTy hc) (generatedTm hd)) (generatedSub hs)
  | .genericJ _ _ hx hT hc hd =>
      j_pres F (generatedTm hx) (generatedTel hT) (generatedTy hc) (generatedTm hd)
  | .reindexJBranch _ _ hx hT hc hd hs =>
      reindexBranch_pres F (generatedTm hx) (generatedTel hT)
        (generatedTy hc) (generatedTm hd) (generatedSub hs)
  | .conv hx _ e => cast_pres F e (generatedTm hx)
termination_by sizeOf h

/-- The substitution result retains both endpoint context equalities. -/
theorem generatedSub (h : SubDeriv Δ δ Γ γ σ s) : F.SubPres s :=
  match h with
  | .id hγ => id_pres F (generatedCtx hγ)
  | .comp hs ht => comp_pres F (generatedSub hs) (generatedSub ht)
  | .weaken _ ha => weaken_pres F (generatedTy ha)
  | .projection _ hT => projection_pres F (generatedTel hT)
  | .root _ _ hx => root_pres F (generatedTm hx)
  | .rootTail _ _ hx hT => rootTail_pres F (generatedTm hx) (generatedTel hT)
  | .pathTailMap _ _ hx hT hs =>
      pathTailMap_pres F (generatedTm hx) (generatedTel hT) (generatedSub hs)
  | .pair ha hs hx => pair_pres F (generatedTy ha) (generatedSub hs) (generatedTm hx)
termination_by sizeOf h
end

/-- The same context derivation can be interpreted before or after mapping. -/
theorem interpretCtx (h : CtxDeriv Γ γ) :
    F.context (Typed.interpretCtx M h) = Typed.interpretCtx N h := by
  rw [interpretCtx_agrees, interpretCtx_agrees]
  exact generatedCtx F h

/-- Heterogeneous equality retains the generated family over its mapped context. -/
theorem interpretTy (h : TyDeriv Γ γ A a) :
    HEq (F.family (Typed.interpretTy M h)) (Typed.interpretTy N h) := by
  rw [interpretTy_agrees, interpretTy_agrees]
  exact (generatedTy F h).2

/-- Preservation of the existing recursive interpreter, including dependent J. -/
theorem interpretTm (h : TmDeriv Γ γ A a t x) :
    HEq (F.mapTm (Typed.interpretTm M h)) (Typed.interpretTm N h) := by
  rw [interpretTm_agrees, interpretTm_agrees]
  exact (generatedTm F h).2

/-- Preservation of the existing substitution interpreter at both endpoints. -/
theorem interpretSub (h : SubDeriv Δ δ Γ γ σ s) :
    HEq (F.substitution (Typed.interpretSub M h)) (Typed.interpretSub N h) := by
  rw [interpretSub_agrees, interpretSub_agrees]
  exact (generatedSub F h).2.2

/-- Identity maps provide a usable signature-preserving instance in every model. -/
def identityMap (M : Model.{u}) : SignatureMap M M where
  toModelMap := ModelMap.identityMap M
  base _ := rfl
  fiber _ := rfl

end SignatureMap
end SquareKit.Internal.PathTransport.Typed
