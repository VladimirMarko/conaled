import SquareKit.Internal.DependentJudgments.DerivedCertificates
import SquareKit.Internal.PathTransport.Endpoints

/-! Identification of generated path recipes with their semantic operations.
The source arguments remain schematic. Index conversions use the constructed
comprehension equations, rather than assuming a transport comparison. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open GuardedTheory PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u
variable (M : PathTransport.Typed.Model.{u}) {V : Type}
variable (ρ : V → Value M.toStructuralModel)

theorem subTm_eval (t s : Expression V) (Γ Δ : M.Context)
    (A : M.Family Γ) (v : M.Section Γ A) (σ : M.Substitution Δ Γ)
    (ht : t.eval (algebra M) ρ = .term Γ A v)
    (hs : s.eval (algebra M) ρ = .substitution Δ Γ σ) :
    (subTm t s).eval (algebra M) ρ = .term Δ (M.subTy A σ) (M.subTm v σ) := by
  change DependentJudgments.operation M.toStructuralModel .subTm
    ![t.eval (algebra M) ρ, s.eval (algebra M) ρ] = _
  rw [ht, hs]
  simp [DependentJudgments.operation]

theorem subTy_eval (a s : Expression V) (Γ Δ : M.Context)
    (A : M.Family Γ) (σ : M.Substitution Δ Γ)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hs : s.eval (algebra M) ρ = .substitution Δ Γ σ) :
    (subTy a s).eval (algebra M) ρ = .family Δ (M.subTy A σ) := by
  change DependentJudgments.operation M.toStructuralModel .subTy
    ![a.eval (algebra M) ρ, s.eval (algebra M) ρ] = _
  rw [ha, hs]
  simp [DependentJudgments.operation]

theorem pair_eval (a s t : Expression V) (Γ Δ : M.Context)
    (A : M.Family Γ) (σ : M.Substitution Δ Γ) (v : M.Section Δ (M.subTy A σ))
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hs : s.eval (algebra M) ρ = .substitution Δ Γ σ)
    (ht : t.eval (algebra M) ρ = .term Δ (M.subTy A σ) v) :
    (pair a s t).eval (algebra M) ρ = .substitution Δ (M.extend Γ A) (M.pairSub A σ v) := by
  change DependentJudgments.operation M.toStructuralModel .pair
    ![a.eval (algebra M) ρ, s.eval (algebra M) ρ, t.eval (algebra M) ρ] = _
  rw [ha, hs, ht]
  simp [DependentJudgments.operation]

theorem identity_eval (a sx sy : Expression V) (Γ : M.Context)
    (A : M.Family Γ) (x y : M.Section Γ A)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hx : sx.eval (algebra M) ρ = .term Γ A x)
    (hy : sy.eval (algebra M) ρ = .term Γ A y) :
    (identity a sx sy).eval (algebra M) ρ = .family Γ (M.identity A x y) := by
  change operation M .identity ![a.eval (algebra M) ρ, sx.eval (algebra M) ρ,
    sy.eval (algebra M) ρ] = _
  rw [ha, hx, hy]
  simp [operation]

theorem reflexivity_eval (a sx : Expression V) (Γ : M.Context)
    (A : M.Family Γ) (x : M.Section Γ A)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hx : sx.eval (algebra M) ρ = .term Γ A x) :
    (reflexivity a sx).eval (algebra M) ρ = .term Γ (M.identity A x x) (M.reflexivity A x) := by
  change operation M .reflexivity ![a.eval (algebra M) ρ, sx.eval (algebra M) ρ] = _
  rw [ha, hx]
  simp [operation]

/-- The source section constructor evaluates to the existing comprehension section. -/
theorem sectionSub_eval (g a t : Expression V)
    (Γ : M.Context) (A : M.Family Γ) (x : M.Section Γ A)
    (hg : g.eval (algebra M) ρ = .context Γ)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (ht : t.eval (algebra M) ρ = .term Γ A x) :
    (sectionSub g a t).eval (algebra M) ρ =
      .substitution Γ (M.extend Γ A) (M.toStructuralModel.sectionSub A x) := by
  simp only [Term.eval, algebra] at hg ha ht
  simp only [identitySub, Term.eval, FinitaryTerm.fold, algebra,
    DependentJudgments.operation, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, hg, ha, ht, Value.substitutionAt_substitution]
  have hx : Value.term Γ A x = .term Γ (M.subTy A (M.idSub Γ))
      (cast (congrArg (M.Section Γ) (M.subTy_id A).symm) x) :=
    Value.term_eq (M.subTy_id A).symm (cast_heq _ _).symm
  rw [hx, Value.termAt_term]
  rfl

theorem pathFamily_eval (g a t : Expression V)
    (Γ : M.Context) (A : M.Family Γ) (x : M.Section Γ A)
    (hg : g.eval (algebra M) ρ = .context Γ)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (ht : t.eval (algebra M) ρ = .term Γ A x) :
    (Contextual.pathFamily g a t).eval (algebra M) ρ =
      .family (M.extend Γ A) (M.toStructuralModel.pathFamily A x) := by
  simp only [Term.eval, algebra] at hg ha ht
  simp [Contextual.pathFamily, Term.eval, algebra, operation,
    DependentJudgments.operation, hg, ha, ht, StructuralModel.pathFamily]

theorem endpoint_eval (g a sx sy sp : Expression V)
    (Γ : M.Context) (A : M.Family Γ) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y))
    (hg : g.eval (algebra M) ρ = .context Γ)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hx : sx.eval (algebra M) ρ = .term Γ A x)
    (hy : sy.eval (algebra M) ρ = .term Γ A y)
    (hp : sp.eval (algebra M) ρ = .term Γ (M.identity A x y) p) :
    (endpoint g a sx sy sp).eval (algebra M) ρ =
      .substitution Γ (M.toStructuralModel.pathContext A x)
        (M.toStructuralModel.endpointSub A x y p) := by
  have hf := pathFamily_eval M ρ g a sx Γ A x hg ha hx
  have hs := sectionSub_eval M ρ g a sy Γ A y hg ha hy
  simp only [Term.eval, algebra] at hf hs hp
  simp only [Term.eval, FinitaryTerm.fold, algebra,
    DependentJudgments.operation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hf, hs, hp,
    Value.substitutionAt_substitution]
  have he : Value.term Γ (M.identity A x y) p =
      .term Γ (M.subTy (M.toStructuralModel.pathFamily A x) (M.toStructuralModel.sectionSub A y))
        (cast (congrArg (M.Section Γ) (M.toStructuralModel.pathFamily_at A x y).symm) p) :=
    Value.term_eq (M.toStructuralModel.pathFamily_at A x y).symm (cast_heq _ _).symm
  rw [he, Value.termAt_term]
  rfl

theorem pathProjection_eval (g a sx : Expression V)
    (Γ : M.Context) (A : M.Family Γ) (x : M.Section Γ A)
    (hg : g.eval (algebra M) ρ = .context Γ)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hx : sx.eval (algebra M) ρ = .term Γ A x) :
    (weaken (extend g a) (Contextual.pathFamily g a sx)).eval (algebra M) ρ =
      .substitution (M.toStructuralModel.pathContext A x) (M.extend Γ A)
        (M.weaken _ (M.toStructuralModel.pathFamily A x)) := by
  have hf := pathFamily_eval M ρ g a sx Γ A x hg ha hx
  simp only [Term.eval, algebra] at hg ha hf
  simp [Term.eval, algebra, DependentJudgments.operation, hg, ha, hf,
    StructuralModel.pathContext]

/-- Empty-tail based J retains the supplied motive and reflexive branch. -/
theorem basedJ_eval (a sx sd sb : Expression V)
    (Γ : M.Context) (A : M.Family Γ) (x : M.Section Γ A)
    (D : M.Family (M.toStructuralModel.pathContext A x))
    (d : M.Section Γ (M.subTy D (M.toStructuralModel.rootSub A x)))
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hx : sx.eval (algebra M) ρ = .term Γ A x)
    (hD : sd.eval (algebra M) ρ = .family (M.toStructuralModel.pathContext A x) D)
    (hd : sb.eval (algebra M) ρ = .term Γ (M.subTy D (M.toStructuralModel.rootSub A x)) d) :
    (basedJ a sx sd sb).eval (algebra M) ρ =
      .term (M.toStructuralModel.pathContext A x) D (M.j A x .nil D d) := by
  simp only [Term.eval, algebra] at ha hx hD hd
  simp [basedJ, Term.eval, algebra, operation, ha, hx, hD, hd,
    problem, tail, Telescope.pullback, Telescope.reindex, Telescope.total,
    StructuralModel.rootTail, Telescope.liftSub]

/-- The generic transport motive over the actual endpoint-and-path context. -/
def motive {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (x : M.Section Γ A) : M.Family (M.toStructuralModel.pathContext A x) :=
  M.subTy B (M.weaken _ (M.toStructuralModel.pathFamily A x))

theorem motive_root {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (x : M.Section Γ A) :
    M.subTy (motive M A B x) (M.toStructuralModel.rootSub A x) =
      M.subTy B (M.toStructuralModel.sectionSub A x) := by
  rw [motive, M.subTy_comp, M.toStructuralModel.weaken_root]

theorem motive_endpoint {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y)) :
    M.subTy (motive M A B x) (M.toStructuralModel.endpointSub A x y p) =
      M.subTy B (M.toStructuralModel.sectionSub A y) := by
  rw [motive, M.subTy_comp, StructuralModel.endpointSub, M.weaken_pair]

/-- J applied to B at the moving endpoint, with its branch converted by the
proved root equation. This definition exposes the operation to be identified. -/
def transportSection {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (x : M.Section Γ A) (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A x))) :
    M.Section (M.toStructuralModel.pathContext A x) (motive M A B x) :=
  M.j A x .nil (motive M A B x)
    (cast (congrArg (M.Section Γ) (motive_root M A B x).symm) b)

def transportValue {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y))
    (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A x))) :
    M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A y)) :=
  cast (congrArg (M.Section Γ) (motive_endpoint M A B x y p))
    (M.subTm (transportSection M A B x b) (M.toStructuralModel.endpointSub A x y p))

theorem transportGeneric_eval (g a sb sx su : Expression V)
    (Γ : M.Context) (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (x : M.Section Γ A) (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A x)))
    (hg : g.eval (algebra M) ρ = .context Γ)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hB : sb.eval (algebra M) ρ = .family (M.extend Γ A) B)
    (hx : sx.eval (algebra M) ρ = .term Γ A x)
    (hb : su.eval (algebra M) ρ = .term Γ (M.subTy B (M.toStructuralModel.sectionSub A x)) b) :
    (transportGeneric g a sb sx su).eval (algebra M) ρ =
      .term (M.toStructuralModel.pathContext A x) (motive M A B x) (transportSection M A B x b) := by
  have hw := pathProjection_eval M ρ g a sx Γ A x hg ha hx
  have hm := subTy_eval M ρ sb _ _ _ B _ hB hw
  exact basedJ_eval M ρ a sx _ su Γ A x (motive M A B x) _ ha hx hm
    (hb.trans (Value.term_eq (motive_root M A B x).symm (cast_heq _ _).symm))

theorem transport_eval (g a sb sx sy sp su : Expression V)
    (Γ : M.Context) (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y))
    (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A x)))
    (hg : g.eval (algebra M) ρ = .context Γ)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hB : sb.eval (algebra M) ρ = .family (M.extend Γ A) B)
    (hx : sx.eval (algebra M) ρ = .term Γ A x)
    (hy : sy.eval (algebra M) ρ = .term Γ A y)
    (hp : sp.eval (algebra M) ρ = .term Γ (M.identity A x y) p)
    (hb : su.eval (algebra M) ρ = .term Γ
      (M.subTy B (M.toStructuralModel.sectionSub A x)) b) :
    (Contextual.transport g a sb sx sy sp su).eval (algebra M) ρ =
      .term Γ (M.subTy B (M.toStructuralModel.sectionSub A y))
        (transportValue M A B x y p b) := by
  have hf := pathFamily_eval M ρ g a sx Γ A x hg ha hx
  have hm : (transportMotive g a sb sx).eval (algebra M) ρ =
      .family (M.toStructuralModel.pathContext A x) (motive M A B x) := by
    simp only [Term.eval, algebra] at hg ha hB hf
    simp [transportMotive, Term.eval, algebra, DependentJudgments.operation,
      hg, ha, hB, hf, motive, StructuralModel.pathContext]
  let d := cast (congrArg (M.Section Γ) (motive_root M A B x).symm) b
  have hd : su.eval (algebra M) ρ =
      .term Γ (M.subTy (motive M A B x) (M.toStructuralModel.rootSub A x)) d :=
    hb.trans (Value.term_eq (motive_root M A B x).symm (cast_heq _ _).symm)
  have hj := basedJ_eval M ρ a sx (transportMotive g a sb sx) su Γ A x
    (motive M A B x) d ha hx hm hd
  have he := endpoint_eval M ρ g a sx sy sp Γ A x y p hg ha hx hy hp
  change (algebra M).operation (.inl .subTm)
    (fun i => (![basedJ a sx (transportMotive g a sb sx) su,
      endpoint g a sx sy sp] i).eval (algebra M) ρ) = _
  change DependentJudgments.operation M.toStructuralModel .subTm
    ![(basedJ a sx (transportMotive g a sb sx) su).eval (algebra M) ρ,
      (endpoint g a sx sy sp).eval (algebra M) ρ] = _
  rw [hj, he]
  simp only [DependentJudgments.operation, Matrix.cons_val_one,
    Matrix.cons_val_zero, Value.termIn_term]
  exact Value.term_eq (motive_endpoint M A B x y p) (cast_heq _ _).symm

/-- Semantic reflexive computation follows the selected J beta rule. -/
theorem transportValue_refl {Γ : M.Context} (A : M.Family Γ)
    (B : M.Family (M.extend Γ A)) (x : M.Section Γ A)
    (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A x))) :
    transportValue M A B x x (M.reflexivity A x) b = b := by
  apply eq_of_heq
  apply (cast_heq _ _).trans
  exact (M.j_beta A x .nil _ _).trans (cast_heq _ _)

/-- Concatenation is transport in the based identity family, followed by its
constructed endpoint type conversion. -/
def concatValue {Γ : M.Context} (A : M.Family Γ) (x y z : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) (q : M.Section Γ (M.identity A y z)) :
    M.Section Γ (M.identity A x z) :=
  cast (congrArg (M.Section Γ) (M.toStructuralModel.pathFamily_at A x z))
    (transportValue M A (M.toStructuralModel.pathFamily A x) y z q
      (cast (congrArg (M.Section Γ) (M.toStructuralModel.pathFamily_at A x y).symm) p))

theorem concat_eval (g a sx sy sz sp sq : Expression V)
    (Γ : M.Context) (A : M.Family Γ) (x y z : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) (q : M.Section Γ (M.identity A y z))
    (hg : g.eval (algebra M) ρ = .context Γ)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hx : sx.eval (algebra M) ρ = .term Γ A x)
    (hy : sy.eval (algebra M) ρ = .term Γ A y)
    (hz : sz.eval (algebra M) ρ = .term Γ A z)
    (hp : sp.eval (algebra M) ρ = .term Γ (M.identity A x y) p)
    (hq : sq.eval (algebra M) ρ = .term Γ (M.identity A y z) q) :
    (Contextual.concat g a sx sy sz sp sq).eval (algebra M) ρ =
      .term Γ (M.identity A x z) (concatValue M A x y z p q) := by
  have hf := pathFamily_eval M ρ g a sx Γ A x hg ha hx
  have h := transport_eval M ρ g a (Contextual.pathFamily g a sx) sy sz sq sp
    Γ A (M.toStructuralModel.pathFamily A x) y z q
    (cast (congrArg (M.Section Γ) (M.toStructuralModel.pathFamily_at A x y).symm) p)
    hg ha hf hy hz hq
    (hp.trans (Value.term_eq (M.toStructuralModel.pathFamily_at A x y).symm (cast_heq _ _).symm))
  exact h.trans (Value.term_eq (M.toStructuralModel.pathFamily_at A x z) (cast_heq _ _).symm)

/-- The dependent action's source is transport of t[x], not t[x] itself. -/
def apdMotiveValue {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (x : M.Section Γ A) (t : M.Section (M.extend Γ A) B) :
    M.Family (M.toStructuralModel.pathContext A x) :=
  M.identity (motive M A B x)
    (transportSection M A B x (M.subTm t (M.toStructuralModel.sectionSub A x)))
    (M.subTm t (M.weaken _ (M.toStructuralModel.pathFamily A x)))

theorem transportSection_root {Γ : M.Context} (A : M.Family Γ)
    (B : M.Family (M.extend Γ A)) (x : M.Section Γ A)
    (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A x))) :
    HEq (M.subTm (transportSection M A B x b) (M.toStructuralModel.rootSub A x)) b :=
  (M.j_beta A x .nil _ _).trans (cast_heq _ _)

theorem apdMotive_root {Γ : M.Context} (A : M.Family Γ)
    (B : M.Family (M.extend Γ A)) (x : M.Section Γ A) (t : M.Section (M.extend Γ A) B) :
    M.subTy (apdMotiveValue M A B x t) (M.toStructuralModel.rootSub A x) =
      M.identity (M.subTy B (M.toStructuralModel.sectionSub A x))
        (M.subTm t (M.toStructuralModel.sectionSub A x))
        (M.subTm t (M.toStructuralModel.sectionSub A x)) := by
  rw [apdMotiveValue, M.identity_sub]
  apply M.toStructuralModel.identity_congr (motive_root M A B x)
    (transportSection_root M A B x _)
  apply (M.subTm_comp _ _ _).trans
  rw [M.toStructuralModel.weaken_root]

theorem apdMotive_endpoint {Γ : M.Context} (A : M.Family Γ)
    (B : M.Family (M.extend Γ A)) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) (t : M.Section (M.extend Γ A) B) :
    M.subTy (apdMotiveValue M A B x t) (M.toStructuralModel.endpointSub A x y p) =
      M.identity (M.subTy B (M.toStructuralModel.sectionSub A y))
        (transportValue M A B x y p (M.subTm t (M.toStructuralModel.sectionSub A x)))
        (M.subTm t (M.toStructuralModel.sectionSub A y)) := by
  rw [apdMotiveValue, M.identity_sub]
  apply M.toStructuralModel.identity_congr (motive_endpoint M A B x y p) (cast_heq _ _).symm
  apply (M.subTm_comp _ _ _).trans
  rw [StructuralModel.endpointSub, M.weaken_pair]

/-- The selected semantic dependent action, including its transported source.
Both casts are supplied by the constructed motive equations above. -/
def apdValue {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y))
    (t : M.Section (M.extend Γ A) B) :
    M.Section Γ (M.identity (M.subTy B (M.toStructuralModel.sectionSub A y))
      (transportValue M A B x y p (M.subTm t (M.toStructuralModel.sectionSub A x)))
      (M.subTm t (M.toStructuralModel.sectionSub A y))) :=
  cast (congrArg (M.Section Γ) (apdMotive_endpoint M A B x y p t))
    (M.subTm (M.j A x .nil (apdMotiveValue M A B x t)
      (cast (congrArg (M.Section Γ) (apdMotive_root M A B x t).symm)
        (M.reflexivity _ (M.subTm t (M.toStructuralModel.sectionSub A x)))))
      (M.toStructuralModel.endpointSub A x y p))

/-- Evaluation retains the selected J term of dependent action and both
endpoints, including the transported source term. -/
theorem apd_eval (g a sb sx sy sp st : Expression V)
    (Γ : M.Context) (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y))
    (t : M.Section (M.extend Γ A) B)
    (hg : g.eval (algebra M) ρ = .context Γ)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hB : sb.eval (algebra M) ρ = .family (M.extend Γ A) B)
    (hx : sx.eval (algebra M) ρ = .term Γ A x)
    (hy : sy.eval (algebra M) ρ = .term Γ A y)
    (hp : sp.eval (algebra M) ρ = .term Γ (M.identity A x y) p)
    (ht : st.eval (algebra M) ρ = .term (M.extend Γ A) B t) :
    (apd g a sb sx sy sp st).eval (algebra M) ρ =
      .term Γ (M.identity (M.subTy B (M.toStructuralModel.sectionSub A y))
        (transportValue M A B x y p (M.subTm t (M.toStructuralModel.sectionSub A x)))
        (M.subTm t (M.toStructuralModel.sectionSub A y))) (apdValue M A B x y p t) := by
  have hs := sectionSub_eval M ρ g a sx Γ A x hg ha hx
  have hw := pathProjection_eval M ρ g a sx Γ A x hg ha hx
  have htx := subTm_eval M ρ st _ _ _ B t _ ht hs
  have hBx := subTy_eval M ρ sb _ _ _ B _ hB hs
  have hBt := subTy_eval M ρ sb _ _ _ B _ hB hw
  have hleft := transportGeneric_eval M ρ g a sb sx _ Γ A B x _ hg ha hB hx htx
  have hright := subTm_eval M ρ st _ _ _ B t _ ht hw
  have hD := identity_eval M ρ _ _ _ _ _ _ _ hBt hleft hright
  have hb := reflexivity_eval M ρ _ _ _ _ _ hBx htx
  let d := cast (congrArg (M.Section Γ) (apdMotive_root M A B x t).symm)
    (M.reflexivity _ (M.subTm t (M.toStructuralModel.sectionSub A x)))
  have hj := basedJ_eval M ρ a sx (apdMotive g a sb sx st) (apdBranch g a sb sx st)
    Γ A x (apdMotiveValue M A B x t) d ha hx hD
    (hb.trans (Value.term_eq (apdMotive_root M A B x t).symm (cast_heq _ _).symm))
  have he := endpoint_eval M ρ g a sx sy sp Γ A x y p hg ha hx hy hp
  have h := subTm_eval M ρ _ _ _ _ _ _ _ hj he
  exact h.trans (Value.term_eq (apdMotive_endpoint M A B x y p t) (cast_heq _ _).symm)

/-- The path-context map sends a generic q to the selected concat(p,q). -/
def concatMapValue {Γ : M.Context} (A : M.Family Γ) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) :
    M.Substitution (M.toStructuralModel.pathContext A y) (M.toStructuralModel.pathContext A x) :=
  M.pairSub (M.toStructuralModel.pathFamily A x)
    (M.weaken _ (M.toStructuralModel.pathFamily A y))
    (transportSection M A (M.toStructuralModel.pathFamily A x) y
      (cast (congrArg (M.Section Γ) (M.toStructuralModel.pathFamily_at A x y).symm) p))

theorem concatMap_projection {Γ : M.Context} (A : M.Family Γ) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) :
    M.compSub (M.weaken _ (M.toStructuralModel.pathFamily A x)) (concatMapValue M A x y p) =
      M.weaken _ (M.toStructuralModel.pathFamily A y) := M.weaken_pair _ _ _

theorem concatMap_root {Γ : M.Context} (A : M.Family Γ) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) :
    M.compSub (concatMapValue M A x y p) (M.toStructuralModel.rootSub A y) =
      M.toStructuralModel.endpointSub A x y p := by
  unfold concatMapValue
  rw [M.toStructuralModel.pair_naturality]
  apply eq_of_heq
  apply M.toStructuralModel.pair_heq rfl rfl HEq.rfl
    (heq_of_eq (M.toStructuralModel.weaken_root A y))
  exact (cast_heq _ _).trans (transportSection_root M A _ y _)

theorem concatMap_endpoint {Γ : M.Context} (A : M.Family Γ) (x y z : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) (q : M.Section Γ (M.identity A y z)) :
    M.compSub (concatMapValue M A x y p) (M.toStructuralModel.endpointSub A y z q) =
      M.toStructuralModel.endpointSub A x z (concatValue M A x y z p q) := by
  unfold concatMapValue
  rw [M.toStructuralModel.pair_naturality]
  apply eq_of_heq
  apply M.toStructuralModel.pair_heq rfl rfl HEq.rfl
    (heq_of_eq (M.weaken_pair _ _ _))
  exact (cast_heq _ _).trans
    ((cast_heq _ _).symm.trans ((cast_heq _ _).symm.trans (cast_heq _ _).symm))

theorem etaRight_type {Γ : M.Context} (A : M.Family Γ)
    (B : M.Family (M.extend Γ A)) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) :
    M.subTy (motive M A B x) (concatMapValue M A x y p) = motive M A B y := by
  rw [motive, M.subTy_comp, concatMap_projection]
  rfl

def etaRightValue {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y))
    (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A x))) :
    M.Section (M.toStructuralModel.pathContext A y) (motive M A B y) :=
  cast (congrArg (M.Section _) (etaRight_type M A B x y p))
    (M.subTm (transportSection M A B x b) (concatMapValue M A x y p))

def etaMotiveValue {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y))
    (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A x))) :
    M.Family (M.toStructuralModel.pathContext A y) :=
  M.identity (motive M A B y) (transportSection M A B y (transportValue M A B x y p b))
    (etaRightValue M A B x y p b)

theorem etaRight_root {Γ : M.Context} (A : M.Family Γ)
    (B : M.Family (M.extend Γ A)) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y))
    (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A x))) :
    HEq (M.subTm (etaRightValue M A B x y p b) (M.toStructuralModel.rootSub A y))
      (transportValue M A B x y p b) := by
  apply (M.toStructuralModel.subTm_congr (etaRight_type M A B x y p).symm (cast_heq _ _) _).trans
  apply (M.subTm_comp _ _ _).trans
  have h : HEq (M.subTm (transportSection M A B x b)
      (M.compSub (concatMapValue M A x y p) (M.toStructuralModel.rootSub A y)))
      (M.subTm (transportSection M A B x b) (M.toStructuralModel.endpointSub A x y p)) := by
    rw [concatMap_root]
  exact h.trans (cast_heq _ _).symm

theorem etaRight_endpoint {Γ : M.Context} (A : M.Family Γ)
    (B : M.Family (M.extend Γ A)) (x y z : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) (q : M.Section Γ (M.identity A y z))
    (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A x))) :
    HEq (M.subTm (etaRightValue M A B x y p b) (M.toStructuralModel.endpointSub A y z q))
      (transportValue M A B x z (concatValue M A x y z p q) b) := by
  apply (M.toStructuralModel.subTm_congr (etaRight_type M A B x y p).symm (cast_heq _ _) _).trans
  apply (M.subTm_comp _ _ _).trans
  have h : HEq (M.subTm (transportSection M A B x b)
      (M.compSub (concatMapValue M A x y p) (M.toStructuralModel.endpointSub A y z q)))
      (M.subTm (transportSection M A B x b)
        (M.toStructuralModel.endpointSub A x z (concatValue M A x y z p q))) := by
    rw [concatMap_endpoint]
  exact h.trans (cast_heq _ _).symm

theorem etaMotive_root {Γ : M.Context} (A : M.Family Γ)
    (B : M.Family (M.extend Γ A)) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y))
    (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A x))) :
    M.subTy (etaMotiveValue M A B x y p b) (M.toStructuralModel.rootSub A y) =
      M.identity (M.subTy B (M.toStructuralModel.sectionSub A y))
        (transportValue M A B x y p b) (transportValue M A B x y p b) := by
  rw [etaMotiveValue, M.identity_sub]
  exact M.toStructuralModel.identity_congr (motive_root M A B y)
    (transportSection_root M A B y _) (etaRight_root M A B x y p b)

theorem etaMotive_endpoint {Γ : M.Context} (A : M.Family Γ)
    (B : M.Family (M.extend Γ A)) (x y z : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) (q : M.Section Γ (M.identity A y z))
    (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A x))) :
    M.subTy (etaMotiveValue M A B x y p b) (M.toStructuralModel.endpointSub A y z q) =
      M.identity (M.subTy B (M.toStructuralModel.sectionSub A z))
        (transportValue M A B y z q (transportValue M A B x y p b))
        (transportValue M A B x z (concatValue M A x y z p q) b) := by
  rw [etaMotiveValue, M.identity_sub]
  exact M.toStructuralModel.identity_congr (motive_endpoint M A B y z q)
    (cast_heq _ _).symm (etaRight_endpoint M A B x y z p q b)

/-- The selected semantic composition certificate uses the same right-path J
as the generated recipe; its branch is reflexivity at the retained value. -/
def etaValue {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (x y z : M.Section Γ A) (p : M.Section Γ (M.identity A x y))
    (q : M.Section Γ (M.identity A y z))
    (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A x))) :
    M.Section Γ (M.identity (M.subTy B (M.toStructuralModel.sectionSub A z))
      (transportValue M A B y z q (transportValue M A B x y p b))
      (transportValue M A B x z (concatValue M A x y z p q) b)) :=
  cast (congrArg (M.Section Γ) (etaMotive_endpoint M A B x y z p q b))
    (M.subTm (M.j A y .nil (etaMotiveValue M A B x y p b)
      (cast (congrArg (M.Section Γ) (etaMotive_root M A B x y p b).symm)
        (M.reflexivity _ (transportValue M A B x y p b))))
      (M.toStructuralModel.endpointSub A y z q))

theorem concatMap_eval (g a sx sy sp : Expression V)
    (Γ : M.Context) (A : M.Family Γ) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y))
    (hg : g.eval (algebra M) ρ = .context Γ)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hx : sx.eval (algebra M) ρ = .term Γ A x)
    (hy : sy.eval (algebra M) ρ = .term Γ A y)
    (hp : sp.eval (algebra M) ρ = .term Γ (M.identity A x y) p) :
    (concatMap g a sx sy sp).eval (algebra M) ρ =
      .substitution (M.toStructuralModel.pathContext A y) (M.toStructuralModel.pathContext A x)
        (concatMapValue M A x y p) := by
  have hf := pathFamily_eval M ρ g a sx Γ A x hg ha hx
  have hw := pathProjection_eval M ρ g a sy Γ A y hg ha hy
  let b := cast (congrArg (M.Section Γ) (M.toStructuralModel.pathFamily_at A x y).symm) p
  have ht := transportGeneric_eval M ρ g a (Contextual.pathFamily g a sx) sy sp
    Γ A (M.toStructuralModel.pathFamily A x) y b hg ha hf hy
    (hp.trans (Value.term_eq (M.toStructuralModel.pathFamily_at A x y).symm (cast_heq _ _).symm))
  exact pair_eval M ρ _ _ _ _ _ _ _ _ hf hw ht

/-- The actual generated eta recipe evaluates to the selected semantic J
certificate. Neither its motive equation nor its branch comparison is assumed. -/
theorem eta_eval (g a sb sx sy sz sp sq su : Expression V)
    (Γ : M.Context) (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (x y z : M.Section Γ A) (p : M.Section Γ (M.identity A x y))
    (q : M.Section Γ (M.identity A y z))
    (b : M.Section Γ (M.subTy B (M.toStructuralModel.sectionSub A x)))
    (hg : g.eval (algebra M) ρ = .context Γ)
    (ha : a.eval (algebra M) ρ = .family Γ A)
    (hB : sb.eval (algebra M) ρ = .family (M.extend Γ A) B)
    (hx : sx.eval (algebra M) ρ = .term Γ A x)
    (hy : sy.eval (algebra M) ρ = .term Γ A y)
    (hz : sz.eval (algebra M) ρ = .term Γ A z)
    (hp : sp.eval (algebra M) ρ = .term Γ (M.identity A x y) p)
    (hq : sq.eval (algebra M) ρ = .term Γ (M.identity A y z) q)
    (hb : su.eval (algebra M) ρ = .term Γ (M.subTy B (M.toStructuralModel.sectionSub A x)) b) :
    (eta g a sb sx sy sz sp sq su).eval (algebra M) ρ =
      .term Γ (M.identity (M.subTy B (M.toStructuralModel.sectionSub A z))
        (transportValue M A B y z q (transportValue M A B x y p b))
        (transportValue M A B x z (concatValue M A x y z p q) b)) (etaValue M A B x y z p q b) := by
  have htr := transport_eval M ρ g a sb sx sy sp su Γ A B x y p b hg ha hB hx hy hp hb
  have hleft := transportGeneric_eval M ρ g a sb sy _ Γ A B y _ hg ha hB hy htr
  have hgen := transportGeneric_eval M ρ g a sb sx su Γ A B x b hg ha hB hx hb
  have hmap := concatMap_eval M ρ g a sx sy sp Γ A x y p hg ha hx hy hp
  have hraw := subTm_eval M ρ _ _ _ _ _ _ _ hgen hmap
  have hright : (etaRight g a sb sx sy sp su).eval (algebra M) ρ =
      .term (M.toStructuralModel.pathContext A y) (motive M A B y) (etaRightValue M A B x y p b) :=
    hraw.trans (Value.term_eq (etaRight_type M A B x y p) (cast_heq _ _).symm)
  have hw := pathProjection_eval M ρ g a sy Γ A y hg ha hy
  have hBt := subTy_eval M ρ sb _ _ _ B _ hB hw
  have hD := identity_eval M ρ _ _ _ _ _ _ _ hBt hleft hright
  have hs := sectionSub_eval M ρ g a sy Γ A y hg ha hy
  have hBy := subTy_eval M ρ sb _ _ _ B _ hB hs
  have hbranch := reflexivity_eval M ρ _ _ _ _ _ hBy htr
  let d := cast (congrArg (M.Section Γ) (etaMotive_root M A B x y p b).symm)
    (M.reflexivity _ (transportValue M A B x y p b))
  have hj := basedJ_eval M ρ a sy (etaMotive g a sb sx sy sp su) (etaBranch g a sb sx sy sp su)
    Γ A y (etaMotiveValue M A B x y p b) d ha hy hD
    (hbranch.trans (Value.term_eq (etaMotive_root M A B x y p b).symm (cast_heq _ _).symm))
  have he := endpoint_eval M ρ g a sy sz sq Γ A y z q hg ha hy hz hq
  have h := subTm_eval M ρ _ _ _ _ _ _ _ hj he
  exact h.trans (Value.term_eq (etaMotive_endpoint M A B x y z p q b) (cast_heq _ _).symm)

end SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics

