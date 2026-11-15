import SquareKit.StaticFunctionSpecialization

/-! An instrumented syntax traversal. Work counts visited constructors and
materialized substitution images, including the weakening of an image under a
binder. This is a syntax-work model, not host allocation or elapsed time. -/
namespace StaticFunction
open FirstOrderCompiler

def nodes : Term P Γ a → Nat
  | .var _ | .unit => 1
  | .pair t u | .letE t u => 1 + nodes t + nodes u
  | .fst t | .snd t | .prim _ t => 1 + nodes t

/-- An image carries the work needed to obtain it, e.g. weakening beneath let.
Its constructor count is charged again when copied into the residual tree. -/
abbrev Images (P : Ty → Ty → Type) (Γ Δ : Ctx) := {a : Ty} → Var Γ a → Term P Δ a × Nat

def liftImages (s : Images P Γ Δ) : Images P (a :: Γ) (a :: Δ)
  | _, .here => (.var .here,0)
  | _, .there v =>
      let image := s v
      (Term.rename (fun w => .there w) image.1,image.2 + nodes image.1)

def measuredSub (s : Images P Γ Δ) : Term P Γ a → Term P Δ a × Nat
  | .var v => let image := s v; (image.1,1 + image.2 + nodes image.1)
  | .unit => (.unit,1)
  | .pair t u =>
      let x := measuredSub s t; let y := measuredSub s u
      (.pair x.1 y.1,1+x.2+y.2)
  | .fst t => let x := measuredSub s t; (.fst x.1,1+x.2)
  | .snd t => let x := measuredSub s t; (.snd x.1,1+x.2)
  | .letE t u =>
      let x := measuredSub s t; let y := measuredSub (liftImages s) u
      (.letE x.1 y.1,1+x.2+y.2)
  | .prim p t => let x := measuredSub s t; (.prim p x.1,1+x.2)

theorem measuredSub_correct (s : Images P Γ Δ) (t : Term P Γ a) :
    (measuredSub s t).1 = Term.subst (fun v => (s v).1) t := by
  induction t generalizing Δ with
  | var v => rfl
  | unit => rfl
  | pair t u ht hu => simp only [measuredSub, Term.subst, ht, hu]
  | fst t ht => simp only [measuredSub, Term.subst, ht]
  | snd t ht => simp only [measuredSub, Term.subst, ht]
  | prim p t ht => simp only [measuredSub, Term.subst, ht]
  | letE t u ht hu =>
    simp only [measuredSub, Term.subst, ht, hu]
    congr 1
    congr 1
    funext a v
    cases v <;> rfl

def singleImages (arg : Term P Γ a) : Images P (a :: Γ) Γ :=
  fun v => (Term.single arg v,0)

/-- The returned syntax is the syntax subsequently compiled. Costs accompany
that traversal; they are not reconstructed from target tick measurements. -/
def measured : Expr P Γ a → Term P Γ a × Nat
  | .value t => (t,1)
  | .apply body arg =>
      let x := measured arg
      let r := measuredSub (singleImages x.1) body
      (r.1,1+x.2+r.2)
  | .pair t u =>
      let x := measured t; let y := measured u
      (.pair x.1 y.1,1+x.2+y.2)
  | .fst t => let x := measured t; (.fst x.1,1+x.2)
  | .snd t => let x := measured t; (.snd x.1,1+x.2)
  | .mapPair body arg =>
      let x := measured arg
      let l := measuredSub (singleImages (.fst x.1)) body
      let r := measuredSub (singleImages (.snd x.1)) body
      (.pair l.1 r.1,4+x.2+l.2+r.2)

theorem measured_correct (e : Expr P Γ a) : (measured e).1 = e.residual := by
  induction e with
  | value t => rfl
  | apply body arg ih => simp only [measured, measuredSub_correct, singleImages, ih, Expr.residual]
  | pair t u ht hu => simp only [measured, ht, hu, Expr.residual]
  | fst t ht => simp only [measured, ht, Expr.residual]
  | snd t ht => simp only [measured, ht, Expr.residual]
  | mapPair body arg ih => simp only [measured, measuredSub_correct, singleImages, ih, Expr.residual]

/-- Repeated identity mapping keeps its applications and copies. Even this
semantically trivial family has exponentially growing residual trees. -/
def duplication (n : Nat) : Expr P [Ty.prod .base .base] (.prod .base .base) :=
  match n with
  | 0 => .value (.var .here)
  | n+1 => .mapPair (.var .here) (duplication n)

theorem duplication_nodes (n : Nat) : nodes (duplication (P := P) n).residual + 3 = 4 * 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [duplication, Expr.residual, Term.subst, Term.single, nodes, Nat.pow_succ]
    omega

end StaticFunction
