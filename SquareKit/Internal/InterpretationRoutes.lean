import SquareKit.Internal.Squares

/-! Componentwise interpretation routes for families of Set models.
Experimental bounded transport from #119; see
`docs/research/branching-graph-transport.md`. Syntax translation is identity.
-/
namespace SquareKit.Internal.InterpretationRoutes
universe u v w w' w''
variable {S : Type u} {F P : S → S → Type u}

/-- An external family of existing interpretations, not an internal setting. -/
abbrev Models (I : Type w) (F P : S → S → Type u) :=
  I → Interpretation.{u,v} F P

/-- A route selects components. Repeated selections and discarded components
are permitted; no inverse or reflection principle is required. -/
def reindex {I : Type w} {J : Type w'} (M : Models I F P) (r : J → I) :
    Models J F P := M ∘ r

/-- Context interpretation is componentwise and includes empty contexts. -/
abbrev Context {I : Type w} (M : Models I F P) (Γ : List S) (i : I) := Env (M i) Γ

def term {I : Type w} (M : Models I F P) (t : Term F Γ s) (i : I)
    (ρ : Context M Γ i) : (M i).Carrier s := t.eval (M i) ρ

def formula {I : Type w} (M : Models I F P) (p : Formula F Γ P) (i : I)
    (ρ : Context M Γ i) : Prop := p.eval (M i) ρ

/-- Each component quantifies over its own environments. Requiring a global
pair of environments here would lose information when one carrier is empty. -/
def Valid {I : Type w} (M : Models I F P) (p q : Formula F Γ P) : Prop :=
  ∀ i, Internal.Valid (M i) p q

theorem derivation {I : Type w} (M : Models I F P) (d : Derives p q) : Valid M p q :=
  fun i => sound (M i) d

theorem preserve {I : Type w} {J : Type w'} (M : Models I F P) (r : J → I)
    (h : Valid M p q) : Valid (reindex M r) p q := fun j => h (r j)

theorem context_route {I : Type w} {J : Type w'} (M : Models I F P) (r : J → I)
    (Γ : List S) (j : J) : Context (reindex M r) Γ j = Context M Γ (r j) := rfl

theorem term_route {I : Type w} {J : Type w'} (M : Models I F P) (r : J → I)
    (t : Term F Γ s) (j : J) (ρ : Context M Γ (r j)) :
    term (reindex M r) t j ρ = term M t (r j) ρ := rfl

theorem formula_route {I : Type w} {J : Type w'} (M : Models I F P) (r : J → I)
    (p : Formula F Γ P) (j : J) (ρ : Context M Γ (r j)) :
    formula (reindex M r) p j ρ ↔ formula M p (r j) ρ := Iff.rfl

/-- Substitution evaluates in the selected context, including lifted
substitution under every existential binder. -/
theorem substitution {I : Type w} {J : Type w'} (M : Models I F P) (r : J → I)
    (p : Formula F Γ P) (σ : Sub F Γ Δ) (j : J) (ρ : Context M Δ (r j)) :
    formula (reindex M r) (p.subst σ) j ρ ↔
      formula M p (r j) (fun x => term M (σ x) (r j) ρ) :=
  formula_subst (M (r j)) p σ ρ

theorem term_substitution {I : Type w} {J : Type w'} (M : Models I F P) (r : J → I)
    (t : Term F Γ s) (σ : Sub F Γ Δ) (j : J) (ρ : Context M Δ (r j)) :
    term (reindex M r) (t.subst σ) j ρ =
      term M t (r j) (fun x => term M (σ x) (r j) ρ) :=
  term_subst (M (r j)) σ ρ t

theorem existential_route {I : Type w} {J : Type w'} (M : Models I F P) (r : J → I)
    (p : Formula F (s :: Γ) P) (j : J) (ρ : Context M Γ (r j)) :
    formula (reindex M r) (.ex p) j ρ ↔
      ∃ x, formula M p (r j) (ρ.extend x) := Iff.rfl

/-- Identity, composition and associativity of these strict routes reduce;
no categorical isomorphism is silently replaced by equality. -/
theorem reindex_id {I : Type w} (M : Models I F P) : reindex M id = M := rfl

theorem reindex_comp {I : Type w} {J : Type w'} {K : Type w''} (M : Models I F P) (r : J → I) (s : K → J) :
    reindex (reindex M r) s = reindex M (r ∘ s) := rfl

abbrev Pair (F P : S → S → Type u) := Models Bool F P

def pair (M₀ M₁ : Interpretation.{u,v} F P) : Pair F P
  | false => M₀
  | true => M₁

def swap (M : Pair F P) : Pair F P := reindex M Bool.not

def project (M : Pair F P) (b : Bool) : Interpretation F P := M b

/-- Direct π₀ and π₁ after swap agree as whole interpretations, hence on
carriers, arrows, predicates, environments, terms and formulas. -/
theorem swap_project (M : Pair F P) (b : Bool) : project (swap M) (!b) = project M b := by
  cases b <;> rfl

theorem swap_swap (M : Pair F P) : swap (swap M) = M := by
  funext b
  cases b <;> rfl

/-- Comparison of the two selected paths; reduction retains the entire model. -/
theorem first_via_swap (M : Pair F P) :
    reindex (swap M) (fun _ : Unit => true) =
      reindex M (fun _ : Unit => false) := rfl

/-- Both branches reuse exactly the source graph derivations. -/
theorem graph {I : Type w} (M : Models I F NoRelations) (f : F a b) (g : F b c)
    (i : I) (ρ : Context M [a, c] i) :
    formula M (Graph.composite f g) i ρ ↔ formula M (Graph.result f g) i ρ :=
  ⟨derivation M (Graph.forward f g) i ρ, derivation M (Graph.backward f g) i ρ⟩

/-- Joint observation reflects equality of arbitrary paired arrows. A single
projection has no such contract. -/
theorem joint_reflection {A B : Bool → Type v} (f g : ∀ b, A b → B b)
    (h₀ : f false = g false) (h₁ : f true = g true) : f = g := by
  funext b
  cases b
  · exact h₀
  · exact h₁
end SquareKit.Internal.InterpretationRoutes
