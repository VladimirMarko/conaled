import SquareKit.Internal.ModalAccess.Fragment
import Mathlib.Data.Sigma.Basic
import Dependent

/-! Experimental dependent telescopes over the restricted environments of #375.
Keys act by pullback. This is a shallow family model with generated structural
syntax, not a model of modal type constructors or the full MTT calculus. -/
namespace SquareKit.Internal.ModalAccess.Comprehension

universe u

/-- A telescope is generated from a base by dependent extension. Its index is
its concrete carrier, so a later declaration can depend on every earlier value. -/
inductive Context : Type u → Type (u + 1)
  | base (B : Type u) : Context B
  | ext {G : Type u} (Γ : Context G) (A : G → Type u) : Context (Sigma A)

abbrev Ty {G : Type u} (_Γ : Context G) := G → Type u

/-- Concrete substitutions; no global interpretation theorem is a field. -/
abbrev Map {G D : Type u} (_Δ : Context D) (_Γ : Context G) := D → G

namespace Model
variable {G D E : Type u}

abbrev reindex (A : G → Type u) (σ : D → G) : D → Type u :=
  DependentSquares.tySub A σ

abbrev term (A : G → Type u) := DependentSquares.Tm A

abbrev subst {A : G → Type u} (t : term A) (σ : D → G) : term (reindex A σ) :=
  DependentSquares.tmSub t σ

abbrev projection {A : G → Type u} : Sigma A → G := DependentSquares.p

abbrev newest {A : G → Type u} : term (reindex A (projection (A := A))) :=
  DependentSquares.q

abbrev pair {A : G → Type u} (σ : D → G) (t : term (reindex A σ)) : D → Sigma A :=
  DependentSquares.extend σ t

@[simp] theorem reindex_id (A : G → Type u) : reindex A id = A :=
  DependentSquares.tySub_id A
@[simp] theorem reindex_comp (A : G → Type u) (σ : D → G) (τ : E → D) :
    reindex (reindex A σ) τ = reindex A (σ ∘ τ) := DependentSquares.tySub_comp A σ τ
@[simp] theorem subst_id {A : G → Type u} (t : term A) : subst t id = t :=
  DependentSquares.tmSub_id t
@[simp] theorem subst_comp {A : G → Type u} (t : term A) (σ : D → G) (τ : E → D) :
    subst (subst t σ) τ = subst t (σ ∘ τ) := DependentSquares.tmSub_comp t σ τ
@[simp] theorem projection_pair {A : G → Type u} (σ : D → G)
    (t : term (reindex A σ)) : projection ∘ pair σ t = σ := DependentSquares.p_extend σ t
@[simp] theorem variable_pair {A : G → Type u} (σ : D → G)
    (t : term (reindex A σ)) : subst newest (pair σ t) = t := DependentSquares.q_extend σ t

theorem pair_eta {A : G → Type u} (f : D → Sigma A) :
    pair (projection ∘ f) (fun d => (f d).2) = f := DependentSquares.extend_eta_sub f

/-- Comprehension universal property, including the dependent second component. -/
theorem pair_unique {A : G → Type u} (f : D → Sigma A) (σ : D → G)
    (t : term (reindex A σ)) (hp : ∀ d, (f d).1 = σ d)
    (hq : ∀ d, HEq (f d).2 (t d)) : f = pair σ t := by
  funext d
  exact Sigma.ext (hp d) (hq d)

/-- Pullback of an extension along any change of base. -/
abbrev lift {A : G → Type u} (σ : D → G) : Sigma (reindex A σ) → Sigma A :=
  DependentSquares.lift σ

@[simp] theorem projection_lift {A : G → Type u} (σ : D → G) :
    projection ∘ lift (A := A) σ = σ ∘ projection := rfl
@[simp] theorem lift_id {A : G → Type u} : lift (A := A) id = id := rfl
@[simp] theorem lift_comp {A : G → Type u} (σ : D → G) (τ : E → D) :
    lift (A := A) σ ∘ lift (A := reindex A σ) τ = lift (A := A) (σ ∘ τ) := rfl

/-- The pullback square is universal, not just commutative. -/
def pullbackFactor {A : G → Type u} (σ : D → G) (f : E → Sigma A)
    (g : E → D) (h : ∀ e, (f e).1 = σ (g e)) : E → Sigma (reindex A σ) :=
  fun e => ⟨g e, (show A (σ (g e)) from (h e) ▸ (f e).2)⟩

theorem pullbackFactor_lift {A : G → Type u} (σ : D → G) (f : E → Sigma A)
    (g : E → D) (h : ∀ e, (f e).1 = σ (g e)) :
    lift σ ∘ pullbackFactor σ f g h = f := by
  funext e
  dsimp [lift, pullbackFactor]
  apply Sigma.ext (h e).symm
  exact (eqRec_heq (h e) ((f e).2))

theorem pullbackFactor_projection {A : G → Type u} (σ : D → G) (f : E → Sigma A)
    (g : E → D) (h : ∀ e, (f e).1 = σ (g e)) :
    projection ∘ pullbackFactor σ f g h = g := rfl

theorem pullbackFactor_unique {A : G → Type u} (σ : D → G) (f : E → Sigma A)
    (g : E → D) (h : ∀ e, (f e).1 = σ (g e))
    (q : E → Sigma (reindex A σ)) (hp : projection ∘ q = g)
    (hl : lift σ ∘ q = f) : q = pullbackFactor σ f g h := by
  funext e
  apply Sigma.ext (congrFun hp e)
  have hx : HEq (q e).2 (f e).2 := by
    have hh := congrFun hl e
    exact (Sigma.mk.inj_iff.mp hh).2
  exact hx.trans (eqRec_heq (h e) ((f e).2)).symm

end Model

/-- Generated well-typed structural terms. `primitive` is a declared local
operation of the shallow family signature. Its arguments already exclude
inaccessible variables. No arbitrary environment outside G is supplied. -/
inductive Term : {G : Type u} → (Γ : Context G) → (A : G → Type u) → Type (u + 1)
  | primitive {G} {Γ : Context G} {A} : Model.term A → Term Γ A
  | variable {G} {Γ : Context G} {A : G → Type u} :
      Term (.ext Γ A) (Model.reindex A Model.projection)
  | subst {G D} {Γ : Context G} {Δ : Context D} {A : G → Type u}
      (t : Term Γ A) (σ : D → G) : Term Δ (Model.reindex A σ)

/-- Evaluation is recursive over generated term construction. -/
def Term.eval {G : Type u} {Γ : Context G} {A} : Term Γ A → Model.term A
  | .primitive t => t
  | .variable => Model.newest
  | .subst t σ => Model.subst t.eval σ

@[simp] theorem Term.eval_subst {G D : Type u} {Γ : Context G} {Δ : Context D}
    {A : G → Type u} (t : Term Γ A) (σ : D → G) :
    (Term.subst (Δ := Δ) t σ).eval = Model.subst t.eval σ := rfl

/-- Generated structural substitutions. Pairing requires an actual typed term;
composition and extension do not ask for a whole-program preservation proof. -/
inductive Sub : {G D : Type u} → Context D → Context G → Type (u + 1)
  | identity {G} (Γ : Context G) : Sub Γ Γ
  | base {G D} (f : D → G) : Sub (.base D) (.base G)
  | projection {G} (Γ : Context G) (A : G → Type u) : Sub (.ext Γ A) Γ
  | comp {G D E} {Γ : Context G} {Δ : Context D} {Θ : Context E} :
      Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  | extend {G D} {Γ : Context G} {Δ : Context D} (A : G → Type u)
      (σ : D → G) (t : Term Δ (Model.reindex A σ)) : Sub Δ (.ext Γ A)

def Sub.eval {G D : Type u} {Γ : Context G} {Δ : Context D} : Sub Δ Γ → D → G
  | .identity _ => id
  | .base f => f
  | .projection _ _ => Model.projection
  | .comp σ τ => σ.eval ∘ τ.eval
  | .extend _ σ t => Model.pair σ t.eval

@[simp] theorem Sub.eval_id {G : Type u} (Γ : Context G) :
    (Sub.identity Γ).eval = id := rfl
@[simp] theorem Sub.eval_comp {G D E : Type u} {Γ : Context G} {Δ : Context D}
    {Θ : Context E} (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    (Sub.comp σ τ).eval = σ.eval ∘ τ.eval := rfl

theorem Sub.id_left {G D : Type u} {Γ : Context G} {Δ : Context D} (σ : Sub Δ Γ) :
    (Sub.comp (.identity Γ) σ).eval = σ.eval := rfl

theorem Sub.id_right {G D : Type u} {Γ : Context G} {Δ : Context D} (σ : Sub Δ Γ) :
    (Sub.comp σ (.identity Δ)).eval = σ.eval := rfl

theorem Sub.assoc {G D E F : Type u} {Γ : Context G} {Δ : Context D}
    {Θ : Context E} {Ξ : Context F} (σ : Sub Δ Γ) (τ : Sub Θ Δ) (υ : Sub Ξ Θ) :
    (Sub.comp (Sub.comp σ τ) υ).eval = (Sub.comp σ (Sub.comp τ υ)).eval := rfl

/-- Term and type substitution use the same interpreted substitution. -/
def Term.substitute {G D : Type u} {Γ : Context G} {Δ : Context D}
    {A : G → Type u} (t : Term Γ A) (σ : Sub Δ Γ) :
    Term Δ (Model.reindex A σ.eval) := .subst t σ.eval

theorem Term.two_substitutions {G D E : Type u} {Γ : Context G} {Δ : Context D}
    {Θ : Context E} {A : G → Type u} (t : Term Γ A)
    (σ : Sub Δ Γ) (τ : Sub Θ Δ) :
    ((t.substitute σ).substitute τ).eval = (t.substitute (.comp σ τ)).eval := rfl

/-- Locked base context, using exactly #375's accessible-value environments. -/
def locked {n} (Γ : Ctx n) (w : Word) : Context (Env Γ w) := .base _

def keySub {n} {Γ : Ctx n} {u v} (k : Cell u v) : Sub (locked Γ v) (locked Γ u) :=
  .base (Env.key k)

/-- Changing locks pulls the dependent declaration back; it cannot leave the
old type in place. This is the concrete key/comprehension square. -/
def keyExtension {n} {Γ : Ctx n} {u v} (k : Cell u v) (A : Env Γ u → Type) :
    Sub (.ext (locked Γ v) (Model.reindex A (Env.key k))) (.ext (locked Γ u) A) :=
  .extend A (Env.key k ∘ Model.projection) .variable

@[simp] theorem keyExtension_eval {n} {Γ : Ctx n} {u v}
    (k : Cell u v) (A : Env Γ u → Type) :
    (keyExtension k A).eval = Model.lift (A := A) (Env.key k) := rfl

theorem key_comprehension {n} {Γ : Ctx n} {u v}
    (k : Cell u v) (A : Env Γ u → Type) :
    Model.projection ∘ (keyExtension k A).eval =
      (keySub k).eval ∘ Model.projection := rfl

theorem key_extension_comp {n} {Γ : Ctx n} {u v w}
    (k : Cell u v) (h : Cell v w) (A : Env Γ u → Type) :
    (keyExtension k A).eval ∘
      (keyExtension h (Model.reindex A (Env.key k))).eval =
      (keyExtension (k.comp h) A).eval := rfl

/-- Base substitution and keys agree on arbitrary dependent types, not just
Boolean observations. The inherited naturality theorem supplies the square. -/
theorem type_substitution_key {n m} {Γ : Ctx n} {Δ : Ctx m} {u v}
    (σ : ModalAccess.Sub Δ Γ) (k : Cell u v) (A : Env Γ u → Type) :
    (fun ρ : Env Δ v => A ((σ.eval ρ).key k)) =
      (fun ρ : Env Δ v => A (σ.eval (ρ.key k))) := by
  funext ρ
  rw [ModalAccess.Sub.eval_key]

/-- Compare the entire selected value in its varying family. -/
theorem term_substitution_key {n m} {Γ : Ctx n} {Δ : Ctx m} {u v}
    (σ : ModalAccess.Sub Δ Γ) (k : Cell u v) {A : Env Γ u → Type}
    (t : (ρ : Env Γ u) → A ρ) (ρ : Env Δ v) :
    (⟨(σ.eval ρ).key k, t ((σ.eval ρ).key k)⟩ : Sigma A) =
      ⟨σ.eval (ρ.key k), t (σ.eval (ρ.key k))⟩ := by
  rw [ModalAccess.Sub.eval_key]

/-- Every old Boolean term and identity family is a specialization. -/
def booleanTerm {n} {Γ : Ctx n} {w} (t : ModalAccess.Term Γ w) :
    Term (locked Γ w) (fun _ => Bool) := .primitive t.eval

def identityType {n} {Γ : Ctx n} {w} (s t : ModalAccess.Term Γ w) :
    Ty (locked Γ w) := IdFamily s t

def oldSelected {n} {Γ : Ctx n} {w} (t : Selected Γ w) :
    Term (locked Γ w) (fun _ => Observation) := .primitive t.eval

theorem recover_boolean {n} {Γ : Ctx n} {w} (t : ModalAccess.Term Γ w) :
    (booleanTerm t).eval = t.eval := rfl

theorem recover_selected {n} {Γ : Ctx n} {w} (t : Selected Γ w) :
    (oldSelected t).eval = t.eval := rfl

end SquareKit.Internal.ModalAccess.Comprehension
