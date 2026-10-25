import SquareKit.Internal.CoreSyntax
import SquareKit.Internal.GraphTargetComparison

/-! Pure, explicit graph emission. Every application carries its primitive's
universe and type arguments; no elaborator inference participates. -/
namespace SquareKit.Internal.GraphEmissionPure
open Lean GraphTarget
abbrev E := CoreSyntax.Expr

structure Model where
  level : Level
  carrier : Ty → E
  first : E
  second : E

def Model.arrow (m : Model) : Graph.Arrow s t → E
  | .first => m.first
  | .second => m.second

def Model.map (m : Model) (f : E → E) : Model :=
  ⟨m.level, fun s => f (m.carrier s), f m.first, f m.second⟩

def Model.shift (m : Model) := m.map CoreSyntax.Expr.shift
abbrev Assignment (Γ : List Ty) := ∀ {s}, Var Γ s → E

def extend (ρ : Assignment Γ) (x : E) : Assignment (s :: Γ)
  | _, .zero => x
  | _, .succ i => ρ i

def shift (ρ : Assignment Γ) : Assignment Γ := fun i => (ρ i).shift

def term (m : Model) (ρ : Assignment Γ) : GraphTarget.Term Γ s → E
  | .var i => ρ i
  | .app f t => .app (m.arrow f) (term m ρ t)

def eq (m : Model) (s : Ty) (a b : E) : E :=
  .app3 (.const ``Eq [m.level]) (m.carrier s) a b

def conj (p q : E) : E := .app2 (.const ``And []) p q

def ex (m : Model) (s : Ty) (p : E) : E :=
  .app2 (.const ``Exists [m.level]) (m.carrier s) (.lam (m.carrier s) p)

def formula (m : Model) (ρ : Assignment Γ) : GraphTarget.Formula Γ → E
  | .eq (s := s) a b => eq m s (term m ρ a) (term m ρ b)
  | .conj p q => conj (formula m ρ p) (formula m ρ q)
  | .ex (s := s) p => ex m s (formula m.shift (extend (shift ρ) (.bvar 0)) p)

def pred (m : Model) (ρ : Assignment Γ) (p : GraphTarget.Formula (s :: Γ)) : E :=
  .lam (m.carrier s) (formula m.shift (extend (shift ρ) (.bvar 0)) p)

/-- Proof variables are included in the same de Bruijn stack as object variables.
Entering any binder shifts the whole model and every assigned expression. -/
def code (m : Model) (ρ : Assignment Γ) {p q : GraphTarget.Formula Γ}
    (d : Code p q) (h : E) : E :=
  match d with
  | .ident => h
  | .cut d e => code m ρ e (code m ρ d h)
  | .left (p := p) (q := q) =>
      .apps (.const ``And.left []) [formula m ρ p, formula m ρ q, h]
  | .right (p := p) (q := q) =>
      .apps (.const ``And.right []) [formula m ρ p, formula m ρ q, h]
  | .pair (q := q) (r := r) d e =>
      .apps (.const ``And.intro []) [formula m ρ q, formula m ρ r,
        code m ρ d h, code m ρ e h]
  | @Code.refl _ _ s t =>
      .apps (.const ``Eq.refl [m.level]) [m.carrier s, term m ρ t]
  | @Code.symm _ _ s a b d =>
      .apps (.const ``Eq.symm [m.level])
        [m.carrier s, term m ρ a, term m ρ b, code m ρ d h]
  | @Code.trans _ _ s a b c d e =>
      .apps (.const ``Eq.trans [m.level])
        [m.carrier s, term m ρ a, term m ρ b, term m ρ c, code m ρ d h, code m ρ e h]
  | @Code.congr _ _ s a b t f d =>
      .apps (.const ``congrArg [m.level, m.level])
        [m.carrier s, m.carrier t, term m ρ a, term m ρ b, m.arrow f, code m ρ d h]
  | .intro (s := s) p t =>
      .apps (.const ``Exists.intro [m.level])
        [m.carrier s, pred m ρ p, term m ρ t, h]
  | .subst σ d => code m (fun i => term m ρ (σ i)) d h
  | @Code.elim Γ s p q d =>
      let m' := m.shift
      let ρ' : Assignment (s :: Γ) := extend (shift ρ) (.bvar 0)
      let branch := CoreSyntax.Expr.lam (m.carrier s) (.lam (formula m' ρ' p)
        (code m'.shift (shift ρ') d (.bvar 0)))
      .apps (.const ``Exists.elim [m.level])
        [m.carrier s, pred m ρ p, formula m ρ q, h, branch]
  | @Code.elimWith Γ s p a q d =>
      let m' := m.shift
      let ρ' : Assignment (s :: Γ) := extend (shift ρ) (.bvar 0)
      let hh := CoreSyntax.Expr.apps (.const ``And.left []) [formula m ρ a, formula m ρ (.ex p), h]
      let he := CoreSyntax.Expr.apps (.const ``And.right []) [formula m ρ a, formula m ρ (.ex p), h]
      let pair := CoreSyntax.Expr.apps (.const ``And.intro [])
        [formula m'.shift (shift ρ') a.shift, formula m'.shift (shift ρ') p,
          hh.shift.shift, .bvar 0]
      let branch := CoreSyntax.Expr.lam (m.carrier s) (.lam (formula m' ρ' p)
        (code m'.shift (shift ρ') d pair))
      .apps (.const ``Exists.elim [m.level])
        [m.carrier s, pred m ρ p, formula m ρ q, he, branch]

/-- The five graph parameters, newest first: g, f, C, B, A. -/
def parameterModel : Model :=
  ⟨.succ (.param `v), (fun | .input => .bvar 4 | .middle => .bvar 3 | .output => .bvar 2),
    .bvar 1, .bvar 0⟩

/-- The context is newest first; outer telescope binders visit its tail first. -/
def context (m : Model) (Γ : List Ty)
    (k : Model → Assignment Γ → E × E) : E × E :=
  match Γ with
  | [] => k m (fun i => nomatch i)
  | s :: Γ => context m Γ fun m' ρ =>
      let r := k m'.shift (extend (shift ρ) (.bvar 0))
      (.all (m'.carrier s) r.1, .lam (m'.carrier s) r.2)

def closeParameters (isType : Bool) (body : E) : E :=
  let bind := if isType then CoreSyntax.Expr.all else CoreSyntax.Expr.lam
  let u := CoreSyntax.Expr.sort (.succ (.param `v))
  bind u (bind u (bind u
    (bind (.all (.bvar 2) (.bvar 2))
      (bind (.all (.bvar 2) (.bvar 2)) body))))

def emitCore (d : GraphTarget.Declaration) : E × E :=
  let r := context parameterModel d.context fun m ρ =>
    (.all (formula m ρ d.premise) (formula m.shift (shift ρ) d.conclusion),
      .lam (formula m ρ d.premise) (code m.shift (shift ρ) d.code (.bvar 0)))
  (closeParameters true r.1, closeParameters false r.2)

def emit (d : GraphTarget.Declaration) : Lean.Expr × Lean.Expr :=
  let (ty, body) := emitCore d
  (ty.toLean, body.toLean)

/-- One universe parameter and no auxiliary declarations are installed. -/
def constantInfo (name : Lean.Name) (d : GraphTarget.Declaration) : Lean.ConstantInfo :=
  .thmInfo { name, levelParams := [`v], type := (emit d).1, value := (emit d).2 }

def declaration (name : Lean.Name) (d : GraphTarget.Declaration) : Lean.Declaration :=
  .thmDecl { name, levelParams := [`v], type := (emit d).1, value := (emit d).2 }

theorem constantInfo_type (name : Lean.Name) (d : GraphTarget.Declaration) :
    (constantInfo name d).type = (emit d).1 := rfl

theorem constantInfo_value (name : Lean.Name) (d : GraphTarget.Declaration) :
    (constantInfo name d).value? true = some (emit d).2 := rfl

theorem emit_decodes (d : GraphTarget.Declaration) :
    CoreSyntax.Expr.ofLean (emit d).1 = some (emitCore d).1 ∧
    CoreSyntax.Expr.ofLean (emit d).2 = some (emitCore d).2 := by
  simp [emit]

theorem term_subst (m : Model) (ρ : Assignment Δ) (σ : GraphTarget.Sub Γ Δ)
    (t : GraphTarget.Term Γ s) :
    term m ρ (t.subst σ) = term m (fun i => term m ρ (σ i)) t := by
  induction t with
  | var => rfl
  | app f t ih => simp only [GraphTarget.Term.subst, term, ih]

theorem term_shift (m : Model) (ρ : Assignment Γ) (x : E) (t : GraphTarget.Term Γ s) :
    term m (extend (s := b) ρ x) t.shift = term m ρ t := by
  simp only [GraphTarget.Term.shift, term_subst, term, extend]

theorem arrow_map (m : Model) (f : E → E) (a : Graph.Arrow s t) :
    (m.map f).arrow a = f (m.arrow a) := by cases a <;> rfl

theorem term_rename (m : Model) (ρ : Assignment Γ) (r : Nat → Nat)
    (t : GraphTarget.Term Γ s) :
    term (m.map (·.rename r)) (fun i => (ρ i).rename r) t = (term m ρ t).rename r := by
  induction t with
  | var => rfl
  | app f t ih => simp only [term, arrow_map, ih, CoreSyntax.Expr.rename]

theorem model_rename_shift (m : Model) (r : Nat → Nat) :
    (m.map (·.rename r)).shift = m.shift.map (·.rename (CoreSyntax.liftRen r)) := by
  cases m
  simp only [Model.shift, Model.map, CoreSyntax.Expr.shift, CoreSyntax.Expr.rename_comp]
  rfl

theorem formula_rename (m : Model) (ρ : Assignment Γ) (r : Nat → Nat)
    (p : GraphTarget.Formula Γ) :
    formula (m.map (·.rename r)) (fun i => (ρ i).rename r) p =
      (formula m ρ p).rename r := by
  induction p generalizing m r with
  | eq a b =>
    simp only [formula, term_rename]
    rfl
  | conj p q hp hq => simp only [formula, conj, hp, hq,
      CoreSyntax.Expr.app2, CoreSyntax.Expr.rename]
  | @ex s Γ p ih =>
    have h : (fun {t} (i : Var (s :: Γ) t) =>
        extend (shift (fun i => (ρ i).rename r)) (.bvar 0) i) =
        (fun {t} (i : Var (s :: Γ) t) =>
          (extend (shift ρ) (.bvar 0) i).rename (CoreSyntax.liftRen r)) := by
      funext t i
      cases i with
      | zero => rfl
      | succ i => simp only [extend, shift, CoreSyntax.Expr.shift, CoreSyntax.Expr.rename_comp]; rfl
    simp only [formula, ex, model_rename_shift, h, ih]
    rfl


@[simp] theorem formula_weaken (m : Model) (a : Assignment Γ) (p : GraphTarget.Formula Γ) :
    formula m.shift (shift a) p = (formula m a p).shift :=
  formula_rename m a Nat.succ p


theorem formula_subst (m : Model) (ρ : Assignment Δ) (σ : GraphTarget.Sub Γ Δ)
    (p : GraphTarget.Formula Γ) :
    formula m ρ (p.subst σ) = formula m (fun i => term m ρ (σ i)) p := by
  induction p generalizing Δ m with
  | eq a b => simp only [GraphTarget.Formula.subst, formula, term_subst]
  | conj p q hp hq => simp only [GraphTarget.Formula.subst, formula, hp, hq]
  | @ex s Γ p ih =>
    simp only [GraphTarget.Formula.subst, formula, ih]
    congr 1
    apply congrArg (fun ρ : Assignment (s :: Γ) => formula m.shift ρ p)
    funext t i
    cases i with
    | zero => rfl
    | succ i =>
      simp only [GraphTarget.Sub.lift, term_shift, extend, shift, Model.shift]
      exact term_rename m ρ Nat.succ (σ i)

theorem formula_shift (m : Model) (ρ : Assignment Γ) (x : E) (p : GraphTarget.Formula Γ) :
    formula m (extend (s := b) ρ x) p.shift = formula m ρ p := by
  simp only [GraphTarget.Formula.shift, formula_subst, term, extend]


theorem term_coreSubst (m : Model) (a : Assignment Γ) (σ : Nat → E)
    (t : GraphTarget.Term Γ s) :
    term (m.map (·.subst σ)) (fun i => (a i).subst σ) t = (term m a t).subst σ := by
  induction t with
  | var => rfl
  | app f t ih => simp only [term, arrow_map, ih, CoreSyntax.Expr.subst]

theorem model_subst_shift (m : Model) (σ : Nat → E) :
    (m.map (·.subst σ)).shift = m.shift.map (·.subst (CoreSyntax.liftSub σ)) := by
  cases m
  simp only [Model.shift, Model.map, CoreSyntax.Expr.subst_shift]

theorem formula_coreSubst (m : Model) (a : Assignment Γ) (σ : Nat → E)
    (p : GraphTarget.Formula Γ) :
    formula (m.map (·.subst σ)) (fun i => (a i).subst σ) p =
      (formula m a p).subst σ := by
  induction p generalizing m σ with
  | eq x y => simp only [formula, term_coreSubst]; rfl
  | conj p q hp hq => simp only [formula, conj, hp, hq,
      CoreSyntax.Expr.app2, CoreSyntax.Expr.subst]
  | @ex s Γ p ih =>
    have h : (fun {t} (i : Var (s :: Γ) t) =>
        extend (shift (fun i => (a i).subst σ)) (.bvar 0) i) =
        (fun {t} (i : Var (s :: Γ) t) =>
          (extend (shift a) (.bvar 0) i).subst (CoreSyntax.liftSub σ)) := by
      funext t i
      cases i with
      | zero => rfl
      | succ i => simp only [extend, shift, CoreSyntax.Expr.subst_shift]
    simp only [formula, ex, model_subst_shift, h, ih]
    rfl

def singleCore (t : E) : Nat → E
  | 0 => t
  | n + 1 => .bvar n

theorem shift_single (a t : E) : a.shift.subst (singleCore t) = a := by
  rw [CoreSyntax.Expr.shift, CoreSyntax.Expr.subst_rename]
  exact CoreSyntax.Expr.subst_id a

theorem model_shift_single (m : Model) (t : E) :
    m.shift.map (·.subst (singleCore t)) = m := by
  cases m
  simp only [Model.shift, Model.map, shift_single]

theorem formula_instantiate (m : Model) (a : Assignment Γ)
    (p : GraphTarget.Formula (s :: Γ)) (t : GraphTarget.Term Γ s) :
    formula m a (p.instantiate t) =
      (formula m.shift (extend (shift a) (.bvar 0)) p).subst (singleCore (term m a t)) := by
  rw [← formula_coreSubst, model_shift_single]
  simp only [GraphTarget.Formula.instantiate, formula_subst]
  apply congrArg (fun a : Assignment (s :: Γ) => formula m a p)
  funext b i
  cases i with
  | zero => rfl
  | succ i => exact (shift_single _ _).symm

/-- Syntactic interpretation of the object fragment. Primitive applications,
their universe and carrier arguments, and the object assignment are explicit. -/
inductive TermDenotes (M : Interpretation Graph.Arrow) :
    {Γ : List Ty} → Model → Assignment Γ → Env M Γ → E → {s : Ty} → M.Carrier s → Prop where
  | var (i : Var Γ s) : TermDenotes M m a ρ (a i) (ρ i)
  | app (f : Graph.Arrow s t) : TermDenotes M m a ρ e x →
      TermDenotes M m a ρ (.app (m.arrow f) e) (M.arrow f x)

/-- The proposition grammar is interpreted from its primitive syntax. In the
existential case, bvar 0 denotes the newly bound object; outer syntax shifts. -/
inductive FormulaDenotes (M : Interpretation Graph.Arrow) :
    {Γ : List Ty} → Model → Assignment Γ → Env M Γ → E → Prop → Prop where
  | eq {s : Ty} {x y : M.Carrier s} : TermDenotes M m a ρ e x → TermDenotes M m a ρ f y →
      FormulaDenotes M m a ρ
        (.app3 (.const ``Eq [m.level]) (m.carrier s) e f) (x = (y : M.Carrier s))
  | conj : FormulaDenotes M m a ρ p P → FormulaDenotes M m a ρ q Q →
      FormulaDenotes M m a ρ (.app2 (.const ``And []) p q) (P ∧ Q)
  | ex {Γ : List Ty} {a : Assignment Γ} {ρ : Env M Γ} (s : Ty) (P : M.Carrier s → Prop) :
      (∀ x, FormulaDenotes M m.shift (extend (shift a) (.bvar 0)) (ρ.extend x) p (P x)) →
      FormulaDenotes M m a ρ
        (.app2 (.const ``Exists [m.level]) (m.carrier s) (.lam (m.carrier s) p)) (∃ x, P x)

theorem term_denotes (M : Interpretation Graph.Arrow) (m : Model) (a : Assignment Γ)
    (ρ : Env M Γ) (t : GraphTarget.Term Γ s) :
    TermDenotes M m a ρ (term m a t) (t.eval M ρ) := by
  induction t with
  | var i => exact .var i
  | app f t ih => exact .app f ih

theorem formula_denotes (M : Interpretation Graph.Arrow) (m : Model) (a : Assignment Γ)
    (ρ : Env M Γ) (p : GraphTarget.Formula Γ) :
    FormulaDenotes M m a ρ (formula m a p) (p.eval M ρ) := by
  induction p generalizing m with
  | eq t u => exact .eq (term_denotes M m a ρ t) (term_denotes M m a ρ u)
  | conj p q hp hq => exact .conj (hp m a ρ) (hq m a ρ)
  | @ex s Γ p ih => exact .ex s _ (fun x => ih m.shift _ (ρ.extend x))

/-- Actual Lean proposition syntax has the independently interpreted meaning,
using the proved decoder connection rather than equality of host proofs. -/
theorem formula_toLean_denotes (M : Interpretation Graph.Arrow) (m : Model)
    (a : Assignment Γ) (ρ : Env M Γ) (p : GraphTarget.Formula Γ) :
    CoreSyntax.InLean (fun e => FormulaDenotes M m a ρ e (p.eval M ρ))
      (formula m a p).toLean :=
  (CoreSyntax.inLean_toLean _ _).mpr (formula_denotes M m a ρ p)

end SquareKit.Internal.GraphEmissionPure
