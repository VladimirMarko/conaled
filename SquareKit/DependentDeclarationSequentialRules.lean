import SquareKit.DependentProjectionSequentialRules
import SquareKit.DependentPairDeclarations

/-! Closed, ordered declaration rules for both independently specified pair languages. -/
namespace SquareKit.DependentDeclarationSequentialRules
open DependentTheoryMaps DependentPairPresentations DependentPairJudgments
open DependentPairDeclarations DependentSequentialRules

def presentation : Bool → Signature
  | false => projectionSignature
  | true => eliminationSignature

def declarations : (k : Bool) → OperationMap signature (presentation k)
  | false => projection
  | true => elimination

def rawDeclarations (k : Bool) (M : Metavariables) :
    OperationMap signature (extend (presentation k) M) := by
  cases k
  · exact ⟨fun decl args => .app (.inl (.declaration decl)) args, fun _ _ _ => rfl⟩
  · exact ⟨fun decl args => .app (.inl (.declaration decl)) args, fun _ _ _ => rfl⟩

@[simp] theorem eval_N (k : Bool) (ρ : X → Expr (presentation k) V)
    (a : Assignment (presentation k) M V) :
    instantiate ρ a (Terms.N (rawDeclarations k M)) = Terms.N (declarations k) := by
  cases k <;> simp only [Terms.N, rawDeclarations, declarations, projection, elimination, instantiate]
  all_goals congr 1; funext i; exact Fin.elim0 i

@[simp] theorem eval_B (k : Bool) (ρ : X → Expr (presentation k) V)
    (a : Assignment (presentation k) M V) (n : Expr (extend (presentation k) M) X) :
    instantiate ρ a (Terms.B (rawDeclarations k M) n) =
      Terms.B (declarations k) (instantiate ρ a n) := by
  cases k <;> simp only [Terms.B, rawDeclarations, declarations, projection, elimination, instantiate]
  all_goals
    congr 1
    funext i
    change Fin 1 at i
    fin_cases i
    exact instantiate_weaken ρ a n

@[simp] theorem eval_C (k : Bool) (ρ : X → Expr (presentation k) V)
    (a : Assignment (presentation k) M V) (n y : Expr (extend (presentation k) M) X) :
    instantiate ρ a (Terms.C (rawDeclarations k M) n y) =
      Terms.C (declarations k) (instantiate ρ a n) (instantiate ρ a y) := by
  cases k <;> simp only [Terms.C, rawDeclarations, declarations, projection, elimination, instantiate]
  all_goals
    congr 1
    funext i
    change Fin 2 at i
    fin_cases i <;> exact instantiate_weaken ρ a _

@[simp] theorem eval_s (k : Bool) (ρ : X → Expr (presentation k) V)
    (a : Assignment (presentation k) M V) (n : Expr (extend (presentation k) M) X) :
    instantiate ρ a (Terms.s (rawDeclarations k M) n) =
      Terms.s (declarations k) (instantiate ρ a n) := by
  cases k <;> simp only [Terms.s, rawDeclarations, declarations, projection, elimination, instantiate]
  all_goals
    congr 1
    funext i
    change Fin 1 at i
    fin_cases i
    exact instantiate_weaken ρ a n

@[simp] theorem eval_d (k : Bool) (ρ : X → Expr (presentation k) V)
    (a : Assignment (presentation k) M V) (n : Expr (extend (presentation k) M) X) :
    instantiate ρ a (Terms.d (rawDeclarations k M) n) =
      Terms.d (declarations k) (instantiate ρ a n) := by
  cases k <;> simp only [Terms.d, rawDeclarations, declarations, projection, elimination, instantiate]
  all_goals
    congr 1
    funext i
    change Fin 1 at i
    fin_cases i
    exact instantiate_weaken ρ a n

@[simp] theorem eval_t (k : Bool) (ρ : X → Expr (presentation k) V)
    (a : Assignment (presentation k) M V) (n : Expr (extend (presentation k) M) X) :
    instantiate ρ a (Terms.t (rawDeclarations k M) n) =
      Terms.t (declarations k) (instantiate ρ a n) := by
  cases k <;> simp only [Terms.t, rawDeclarations, declarations, projection, elimination, instantiate]
  all_goals
    congr 1
    funext i
    change Fin 1 at i
    fin_cases i
    exact instantiate_weaken ρ a n

@[simp] theorem eval_u (k : Bool) (ρ : X → Expr (presentation k) V)
    (a : Assignment (presentation k) M V) (n : Expr (extend (presentation k) M) X) :
    instantiate ρ a (Terms.u (rawDeclarations k M) n) =
      Terms.u (declarations k) (instantiate ρ a n) := by
  cases k <;> simp only [Terms.u, rawDeclarations, declarations, projection, elimination, instantiate]
  all_goals
    congr 1
    funext i
    change Fin 1 at i
    fin_cases i
    exact instantiate_weaken ρ a n

abbrev metas (n : Nat) : Metavariables := ⟨n, fun _ => 0⟩
def arg (i : Fin n) : Expr (extend S (metas n)) Empty := unzero (metaApplication i)

def nullary (k : Bool) : DependentSequentialRules.Rule (presentation k) (metas 0) :=
  ⟨[], .type (Terms.N (rawDeclarations k _))⟩

inductive Unary where | B | s | d | t | u

def unary (k : Bool) (r : Unary) : DependentSequentialRules.Rule (presentation k) (metas 1) :=
  let D := rawDeclarations k (metas 1)
  let n := arg 0
  ⟨[⟨0, .empty, .term n (Terms.N D)⟩], match r with
    | .B => .type (Terms.B D n)
    | .s => .term (Terms.s D n) (Terms.N D)
    | .d => .term (Terms.d D n) (Terms.N D)
    | .t => .term (Terms.t D n) (Terms.B D (Terms.s D n))
    | .u => .term (Terms.u D n) (Terms.C D (Terms.s D n) (Terms.t D n))⟩

def binary (k : Bool) : DependentSequentialRules.Rule (presentation k) (metas 2) :=
  let D := rawDeclarations k (metas 2)
  let n := arg 0
  let y := arg 1
  ⟨[⟨0, .empty, .term n (Terms.N D)⟩, ⟨0, .empty, .term y (Terms.B D n)⟩],
    .type (Terms.C D n y)⟩

def Unary.contextual (r : Unary) (Γ : Context S V) (n : Expr S V) :
    DependentPairDeclarations.Rule S := match r with
  | .B => .B Γ n
  | .s => .s Γ n
  | .d => .d Γ n
  | .t => .t Γ n
  | .u => .u Γ n

def values (es : Fin n → Expr S V) : Assignment S (metas n) V := fun i => zero (es i)

@[simp] theorem eval_arg (es : Fin n → Expr S V) (i : Fin n) :
    instantiate Empty.elim (values es) (arg i) = es i := by
  have h := DependentProjectionSequentialRules.eval_unzero_meta (values es) i rfl
  change instantiate Empty.elim (values es) (arg i) = unzero (zero (es i)) at h
  simpa only [unzero_zero] using h

theorem nullary_instance (k : Bool) (Γ : Context (presentation k) V) :
    (nullary k).instantiate Γ (values (fun i : Fin 0 => i.elim0)) =
      DependentPairDeclarations.Rule.schema (declarations k) (.N Γ) := by
  dsimp [nullary, DependentSequentialRules.Rule.instantiate, List.map,
    form, expression, assignment, boundVariables, Scope]
  simp only [eval_N]
  rfl

theorem unary_instance (k : Bool) (r : Unary) (Γ : Context (presentation k) V)
    (n : Expr (presentation k) V) :
    (unary k r).instantiate Γ (values (fun _ => n)) =
      DependentPairDeclarations.Rule.schema (declarations k) (r.contextual Γ n) := by
  cases r <;>
    dsimp [unary, DependentSequentialRules.Rule.instantiate, List.map,
      RelativeJudgment.instantiate, Telescope.instantiate, form, expression,
      assignment, boundVariables, Scope] <;>
    simp only [eval_N, eval_B, eval_C, eval_s, eval_d, eval_t, eval_u, eval_arg] <;> rfl

theorem binary_instance (k : Bool) (Γ : Context (presentation k) V)
    (n y : Expr (presentation k) V) :
    (binary k).instantiate Γ (values ![n, y]) =
      DependentPairDeclarations.Rule.schema (declarations k) (.C Γ n y) := by
  dsimp [binary, DependentSequentialRules.Rule.instantiate, List.map,
    RelativeJudgment.instantiate, Telescope.instantiate, form, expression,
    assignment, boundVariables, Scope]
  simp only [eval_N, eval_B, eval_C, eval_arg]
  rfl

/-- Every declaration schema in either language is an ambient instance of
its closed rule. The order N, B, C, s, d, t, u retains the declared dependencies. -/
structure Encoding (k : Bool) (r : DependentPairDeclarations.Rule (presentation k)) where
  metas : Metavariables
  rule : DependentSequentialRules.Rule (presentation k) metas
  values : Assignment (presentation k) metas (r.schema (declarations k)).conclusion.Scope
  instance_eq : rule.instantiate (r.schema (declarations k)).conclusion.context values =
    r.schema (declarations k)

def encode (k : Bool) (r : DependentPairDeclarations.Rule (presentation k)) : Encoding k r := by
  cases r with
  | N Γ => exact ⟨metas 0, nullary k, values (fun i : Fin 0 => i.elim0), nullary_instance k Γ⟩
  | B Γ n => exact ⟨metas 1, unary k .B, values (fun _ => n), unary_instance k .B Γ n⟩
  | C Γ n y => exact ⟨metas 2, binary k, values ![n,y], binary_instance k Γ n y⟩
  | s Γ m => exact ⟨metas 1, unary k .s, values (fun _ => m), unary_instance k .s Γ m⟩
  | d Γ m => exact ⟨metas 1, unary k .d, values (fun _ => m), unary_instance k .d Γ m⟩
  | t Γ m => exact ⟨metas 1, unary k .t, values (fun _ => m), unary_instance k .t Γ m⟩
  | u Γ m => exact ⟨metas 1, unary k .u, values (fun _ => m), unary_instance k .u Γ m⟩

end SquareKit.DependentDeclarationSequentialRules
