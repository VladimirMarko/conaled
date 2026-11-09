import SquareKit.Internal.DependentJudgments.LeftConcatSemantics
import SquareKit.Internal.DependentJudgments.DerivedGroupoidSemantics

/-! The guarded left-path recipe in the ordinary groupoid model. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation.LeftSemantics.Groupoid
open GuardedTheory CategoryTheory PathTransport.GroupoidModel PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => Instance.fullModel C B
abbrev recipe : Expression (Fin 7) := leftConcat (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6)

def environment {G : Grpd.{u,u}} (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) : Fin 7 → Value (M).toStructuralModel :=
  ![.context G, .family G (constant C), .term G (constant C) ⟨x⟩,
    .term G (constant C) ⟨y⟩, .term G (constant C) ⟨z⟩,
    .term G (identityFamily (constant C) x y) ⟨p⟩,
    .term G (identityFamily (constant C) y z) ⟨q⟩]

abbrev paths {G : Grpd.{u,u}} (x : Section (constant (Γ := G) C)) : Grpd.{u,u} :=
  (M).toStructuralModel.pathContext (constant C) ⟨x⟩
abbrev withZ {G : Grpd.{u,u}} (x : Section (constant (Γ := G) C)) : Grpd.{u,u} :=
  (M).extend (paths C B x) (constant C)
abbrev movingZ {G : Grpd.{u,u}} (x : Section (constant (Γ := G) C)) :=
  (PathTransport.GroupoidModel.DerivedSemantics.endpoint x).reindex (PathTransport.GroupoidModel.weaken (constant C))
abbrev zAtZ {G : Grpd.{u,u}} (x : Section (constant (Γ := G) C)) :=
  «variable» (constant (Γ := paths C B x) C)
abbrev qFamily {G : Grpd.{u,u}} (x : Section (constant (Γ := G) C)) : (M).Family (withZ C B x) :=
  identityFamily (constant C) (movingZ C x) (zAtZ C B x)
abbrev tel {G : Grpd.{u,u}} (x : Section (constant (Γ := G) C)) :
    StructuralModel.Telescope (M).toStructuralModel ((M).toStructuralModel.pathContext (constant C) ⟨x⟩) 2 :=
  .cons (constant C) (.cons (qFamily C B x) .nil)

abbrev projection {G : Grpd.{u,u}} (x : Section (constant (Γ := G) C)) :=
  PathTransport.GroupoidModel.weaken (qFamily C B x) ⋙
    PathTransport.GroupoidModel.weaken (constant (Γ := paths C B x) C)
abbrev fixed {G : Grpd.{u,u}} (x : Section (constant (Γ := G) C)) :=
  x.reindex (projection C B x ⋙ PathComparison.retract (constant C) x)
abbrev finalZ {G : Grpd.{u,u}} (x : Section (constant (Γ := G) C)) :=
  (zAtZ C B x).reindex (PathTransport.GroupoidModel.weaken (qFamily C B x))
abbrev motive {G : Grpd.{u,u}} (x : Section (constant (Γ := G) C)) : (M).Family (tel C B x).total :=
  identityFamily (constant C) (fixed C B x) (finalZ C B x)
abbrev rootFunctor {G : Grpd.{u,u}} (x : Section (constant (Γ := G) C)) :=
  ((M).toStructuralModel.rootTail (constant C) ⟨x⟩ (tel C B x)).down


theorem tail_eval {G : Grpd.{u,u}} (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) :
    ((LeftConcatFrame.tail (.var 0) (.var 1) (.var 2)).code (path (.var 1) (.var 2))).eval
      (algebra M) (environment C B x y z p q) =
    .telescope ((M).toStructuralModel.pathContext (constant C) ⟨x⟩) 2 (tel C B x) := by
  simp [Reference.Tail.code, LeftConcatFrame.pathType,
    LeftConcatFrame.pathProjection, LeftConcatFrame.qType, LeftConcatFrame.zType,
    LeftConcatFrame.zProjection, LeftConcatFrame.movingZ, LeftConcatFrame.moving,
    LeftConcatFrame.z, Contextual.pathFamily, Term.eval, algebra, operation,
    DependentJudgments.operation, environment, tel, qFamily, movingZ, zAtZ, StructuralModel.pathContext, StructuralModel.pathFamily]
  constructor <;> rfl

theorem motive_eval {G : Grpd.{u,u}} (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) :
    (LeftConcatFrame.motive (.var 0) (.var 1) (.var 2)).eval
      (algebra M) (environment C B x y z p q) =
    .family (tel C B x).total (motive C B x) := by
  simp [LeftConcatFrame.motive, LeftConcatFrame.finalType, LeftConcatFrame.finalFixed,
    LeftConcatFrame.finalZ, LeftConcatFrame.qProjection, LeftConcatFrame.withZ,
    LeftConcatFrame.pathType, LeftConcatFrame.pathProjection, LeftConcatFrame.qType,
    LeftConcatFrame.zType, LeftConcatFrame.zProjection, LeftConcatFrame.movingZ,
    LeftConcatFrame.moving, LeftConcatFrame.z, LeftConcatFrame.fixedZ, LeftConcatFrame.fixed,
    Contextual.pathFamily, Term.eval, algebra, operation, DependentJudgments.operation,
    environment, tel, StructuralModel.pathContext, StructuralModel.pathFamily]
  constructor <;> rfl

def branch {G : Grpd.{u,u}} (x : Section (constant (Γ := G) C)) :
    (M).Section (StructuralModel.Telescope.pullback (M).toStructuralModel (tel C B x)
      ((M).toStructuralModel.rootSub (constant C) ⟨x⟩)).total
      ((M).subTy (motive C B x) ((M).toStructuralModel.rootTail (constant C) ⟨x⟩ (tel C B x))) :=
  ⟨(«variable» (qFamily C B x)).reindex (rootFunctor C B x)⟩


theorem pathType_eval {G : Grpd.{u,u}} (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) :
    (LeftConcatFrame.pathType (.var 0) (.var 1) (.var 2)).eval
      (algebra M) (environment C B x y z p q) =
    .family (paths C B x) (constant C) := by
  simp [LeftConcatFrame.pathType, LeftConcatFrame.pathProjection, Contextual.pathFamily,
    Term.eval, algebra, operation, DependentJudgments.operation, environment,
    StructuralModel.pathContext, StructuralModel.pathFamily]
  rfl

theorem qType_eval {G : Grpd.{u,u}} (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) :
    (LeftConcatFrame.qType (.var 0) (.var 1) (.var 2)).eval
      (algebra M) (environment C B x y z p q) =
    .family (withZ C B x) (qFamily C B x) := by
  simp [LeftConcatFrame.pathType, LeftConcatFrame.pathProjection, LeftConcatFrame.qType,
    LeftConcatFrame.zType, LeftConcatFrame.zProjection, LeftConcatFrame.movingZ,
    LeftConcatFrame.moving, LeftConcatFrame.z, Contextual.pathFamily,
    Term.eval, algebra, operation, DependentJudgments.operation, environment,
    StructuralModel.pathContext, StructuralModel.pathFamily]
  constructor <;> rfl

theorem rootMap_eval {G : Grpd.{u,u}} (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) :
    ((LeftConcatFrame.tail (.var 0) (.var 1) (.var 2)).map (.var 0) (root (.var 1) (.var 2))).eval
      (algebra M) (environment C B x y z p q) =
    .substitution (StructuralModel.Telescope.pullback (M).toStructuralModel (tel C B x)
      ((M).toStructuralModel.rootSub (constant C) ⟨x⟩)).total
      (tel C B x).total ((M).toStructuralModel.rootTail (constant C) ⟨x⟩ (tel C B x)) := by
  let ρ := environment C B x y z p q
  have ha := pathType_eval C B x y z p q
  have hr : (root (.var 1) (.var 2)).eval (algebra M) ρ =
      .substitution G (paths C B x) ((M).toStructuralModel.rootSub (constant C) ⟨x⟩) := by
    simp [Term.eval, algebra, operation, ρ, environment]
  have hl := liftSyntax_eval M ρ (.var 0) _ _ _ _ _ _ rfl ha hr
  have hg : (extend (.var 0) (subTy (LeftConcatFrame.pathType (.var 0) (.var 1) (.var 2))
      (root (.var 1) (.var 2)))).eval (algebra M) ρ =
      .context ((M).extend G ((M).subTy (constant C) ((M).toStructuralModel.rootSub (constant C) ⟨x⟩))) := by
    have ht := DerivedSemantics.subTy_eval M ρ _ _ _ _ _ _ ha hr
    change DependentJudgments.operation (M).toStructuralModel .extend
      ![ρ 0, (subTy _ _).eval (algebra M) ρ] = _
    rw [ht]
    simp [DependentJudgments.operation, ρ, environment]
  exact liftSyntax_eval M ρ _ _ _ _ _ _ _ hg (qType_eval C B x y z p q) hl

theorem branch_eval {G : Grpd.{u,u}} (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) :
    (subTm (LeftConcatFrame.q (.var 0) (.var 1) (.var 2))
      ((LeftConcatFrame.tail (.var 0) (.var 1) (.var 2)).map (.var 0) (root (.var 1) (.var 2)))).eval
      (algebra M) (environment C B x y z p q) =
    .term (StructuralModel.Telescope.pullback (M).toStructuralModel (tel C B x)
      ((M).toStructuralModel.rootSub (constant C) ⟨x⟩)).total
      ((M).subTy (motive C B x) ((M).toStructuralModel.rootTail (constant C) ⟨x⟩ (tel C B x)))
      (branch C B x) := by
  have hq := qType_eval C B x y z p q
  have hp := pathType_eval C B x y z p q
  have hctx : (LeftConcatFrame.withZ (.var 0) (.var 1) (.var 2)).eval
      (algebra M) (environment C B x y z p q) = .context (withZ C B x) := by
    change DependentJudgments.operation (M).toStructuralModel .extend
      ![(path (.var 1) (.var 2)).eval (algebra M) _,
        (LeftConcatFrame.pathType (.var 0) (.var 1) (.var 2)).eval (algebra M) _] = _
    rw [hp]
    simp [Term.eval, algebra, operation, DependentJudgments.operation, environment]
  have hv : (LeftConcatFrame.q (.var 0) (.var 1) (.var 2)).eval
      (algebra M) (environment C B x y z p q) =
      .term (tel C B x).total ((M).subTy (qFamily C B x)
        ((M).weaken (withZ C B x) (qFamily C B x)))
        ((M).genericVariable (withZ C B x) (qFamily C B x)) := by
    change DependentJudgments.operation (M).toStructuralModel .generic
      ![(LeftConcatFrame.withZ (.var 0) (.var 1) (.var 2)).eval (algebra M) _,
        (LeftConcatFrame.qType (.var 0) (.var 1) (.var 2)).eval (algebra M) _] = _
    rw [hctx, hq]
    simp [DependentJudgments.operation]
    rfl
  exact DerivedSemantics.subTm_eval M _ _ _ _ _ _ _ _ hv (rootMap_eval C B x y z p q)

def arguments {G : Grpd.{u,u}} (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) : (M).Substitution G (tel C B x).total :=
  (M).pairSub (qFamily C B x)
    ((M).pairSub (constant C)
      ((M).toStructuralModel.endpointSub (constant C) ⟨x⟩ ⟨y⟩ ⟨p⟩) ⟨z⟩) ⟨q⟩

theorem arguments_eval {G : Grpd.{u,u}} (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) :
    (LeftConcatArguments.atQ (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6)).eval
      (algebra M) (environment C B x y z p q) =
    .substitution G (tel C B x).total (arguments C B x y z p q) := by
  have he := DerivedSemantics.endpoint_eval M (environment C B x y z p q)
    (.var 0) (.var 1) (.var 2) (.var 3) (.var 5) G (constant C) ⟨x⟩ ⟨y⟩ ⟨p⟩ rfl rfl rfl rfl rfl
  have hz := DerivedSemantics.pair_eval M (environment C B x y z p q)
    _ _ (.var 4) _ _ (constant C) _ ⟨z⟩ (pathType_eval C B x y z p q) he rfl
  exact DerivedSemantics.pair_eval M (environment C B x y z p q)
    _ _ (.var 6) (withZ C B x) G (qFamily C B x)
      ((M).pairSub (constant C)
        ((M).toStructuralModel.endpointSub (constant C) ⟨x⟩ ⟨y⟩ ⟨p⟩) ⟨z⟩)
      ⟨q⟩ (qType_eval C B x y z p q) hz rfl

/-- The selected first-path J, with its nonempty dependent tail. -/
def selected {G : Grpd.{u,u}} (x : Section (constant (Γ := G) C)) :=
  (M).j (constant C) ⟨x⟩ (tel C B x) (motive C B x) (branch C B x)

theorem recipe_eval {G : Grpd.{u,u}} (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) :
    recipe.eval (algebra M) (environment C B x y z p q) =
    .term G (identityFamily (constant C) x z)
      ((M).subTm (selected C B x) (arguments C B x y z p q)) :=
  leftConcat_eval M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
    (tail_eval C B x y z p q) (motive_eval C B x y z p q)
    (branch_eval C B x y z p q) (arguments_eval C B x y z p q)

def composite {G : Grpd.{u,u}} (x : Section (constant (Γ := G) C)) : Section (motive C B x) :=
  PathTransport.GroupoidModel.DerivedSemantics.composePaths (constant C)
    (fixed C B x) ((movingZ C x).reindex (PathTransport.GroupoidModel.weaken (qFamily C B x)))
    (finalZ C B x) ((ConcatSemantics.pathWitness C x).reindex (projection C B x))
    («variable» (qFamily C B x))

/-- Discrete identity fibers identify this first-path eliminator by its retained
q branch. No right-path recipe is used in the comparison. -/
theorem selected_composite {G : Grpd.{u,u}} (x : Section (constant (Γ := G) C)) :
    (selected C B x).down = composite C B x := by
  apply Instance.contextualJ_unique
  apply Section.ext_discrete
  intro g
  apply Discrete.ext
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- Both arbitrary path sections, including their selected arrows, survive
interpretation of the generated guarded expression. -/
theorem recipe_composite {G : Grpd.{u,u}} (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) :
    recipe.eval (algebra M) (environment C B x y z p q) =
    .term G (identityFamily (constant C) x z)
      ⟨PathTransport.GroupoidModel.DerivedSemantics.composePaths (constant C) x y z p q⟩ := by
  rw [recipe_eval]
  apply congrArg (@Value.term (M).toStructuralModel G (identityFamily (constant C) x z))
  apply ULift.ext
  change (selected C B x).down.reindex (arguments C B x y z p q).down = _
  rw [selected_composite]
  rfl

/-- Arbitrary schematic expressions and contexts evaluate to composition when
the family evaluates to the constant groupoid C. The Fin 7 recipe is only the
proof template; callers supply no frame or branch annotation equalities. -/
theorem eval_composite {V : Type} (ρ : V → Value (M).toStructuralModel)
    (g a sx sy sz sp sq : Expression V) (G : Grpd.{u,u})
    (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z))
    (hg : g.eval (algebra M) ρ = .context G)
    (ha : a.eval (algebra M) ρ = .family G (constant C))
    (hx : sx.eval (algebra M) ρ = .term G (constant C) ⟨x⟩)
    (hy : sy.eval (algebra M) ρ = .term G (constant C) ⟨y⟩)
    (hz : sz.eval (algebra M) ρ = .term G (constant C) ⟨z⟩)
    (hp : sp.eval (algebra M) ρ = .term G (identityFamily (constant C) x y) ⟨p⟩)
    (hq : sq.eval (algebra M) ρ = .term G (identityFamily (constant C) y z) ⟨q⟩) :
    (leftConcat g a sx sy sz sp sq).eval (algebra M) ρ =
    .term G (identityFamily (constant C) x z)
      ⟨PathTransport.GroupoidModel.DerivedSemantics.composePaths (constant C) x y z p q⟩ := by
  have he : (fun i => (![g, a, sx, sy, sz, sp, sq] i).eval (algebra M) ρ) =
      environment C B x y z p q := by
    funext i
    fin_cases i <;> first | exact hg | exact ha | exact hx | exact hy | exact hz | exact hp | exact hq
  have hs : recipe.subst ![g, a, sx, sy, sz, sp, sq] = leftConcat g a sx sy sz sp sq :=
    LeftConcatRecipe.leftConcat_subst _ _ _ _ _ _ _ _
  rw [← hs, Term.eval_subst, he]
  exact recipe_composite C B x y z p q

/-- The chosen arrow, rather than its action on a fiber, is the observation. -/
theorem recipe_action {G : Grpd.{u,u}} (x y z : Section (constant (Γ := G) C))
    (p : Section (identityFamily (constant C) x y))
    (q : Section (identityFamily (constant C) y z)) (g : G) :
    Option.map (fun t : (M).Section G (identityFamily (constant C) x z) => (t.down.obj g).as)
      ((recipe.eval (algebra M) (environment C B x y z p q)).termAt G
        (identityFamily (constant C) x z)) = some ((p.obj g).as ≫ (q.obj g).as) := by
  rw [recipe_composite]
  simp only [Value.termAt_term, Option.map_some]
  rfl

/-- Both source interfaces select the same path section in the ordinary
model. This comparison does not equate their syntax or their derivations. -/
theorem recipe_frozen (hΓ : CtxDeriv Γ γ) {x y z : Authoring.BasePoint Γ γ}
    (p : Authoring.Path x y) (q : Authoring.Path y z) :
    recipe.eval (algebra M)
      (environment C B (x.code M).down (y.code M).down (z.code M).down
        (p.code M).down (q.code M).down) =
    .term (γ M) (identityFamily (constant C) (x.code M).down (z.code M).down)
      (interpretTm M (Authoring.concat hΓ p q).deriv) := by
  rw [recipe_composite, interpretTm_agrees]
  have h := ConcatSemantics.concat_section C B hΓ x p q
  exact congrArg (fun t => @Value.term (M).toStructuralModel (γ M)
    (identityFamily (constant C) (x.code M).down (z.code M).down) (ULift.up t)) h.symm
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation.LeftSemantics.Groupoid
