import Applications.Elaboration.Constraints

/-! Declarative admissibility, deterministic resolution, and a bounded elaborator.
The admitted source fragment is typed before this pass. Overloaded outer literals
require an expected type; no priority between their two meanings is implicit. -/
namespace Elaboration

inductive Phrase (Γ Δ : List Ty) where
  | term : Source Γ Δ t → Phrase Γ Δ
  | overloaded : Nat → Phrase Γ Δ

/-- Matching an optional expected type is an independent policy judgment. -/
def Matches (expected : Option Ty) (t : Ty) : Prop := expected = none ∨ expected = some t

inductive Resolves : Phrase Γ Δ → Option Ty → {t : Ty} → Source Γ Δ t → Prop where
  | term (s : Source Γ Δ t) (h : Matches expected t) : Resolves (.term s) expected s
  | nat (n : Nat) : Resolves (.overloaded n) (some .nat) (.lit n)
  | packet (n : Nat) : Resolves (.overloaded n) (some .packet) (.vector 0 (.lit n) (.lit 0))

structure Output (Γ Δ : List Ty) where
  inferred : Ty
  code : Core Γ Δ inferred
  constraints : List Obligation

abbrev Output.extendedSignature (o : Output Γ Δ) : List Ty := o.inferred :: Δ

/-- The relation leaves target representations free, provided they retain the
source meaning and exactly its obligation meaning. Scoping is carried by Var;
target sort and unresolved-assignment typing have separate roles. -/
def Elaborates (p : Phrase Γ Δ) (expected : Option Ty) (o : Output Γ Δ) : Prop :=
  ∃ s : Source Γ Δ o.inferred,
    Resolves p expected s ∧ Faithful s o.code ∧
    (∀ θ, Solves θ o.constraints ↔ Solves θ s.requirements) ∧
    (∀ θ, Solves θ o.constraints ↔ o.code.Typed θ)

inductive Diagnostic where
  | ambiguous
  | expectedMismatch
  | unresolved : Obligation → Diagnostic
  deriving DecidableEq, Repr

/-- Resolution is finite case analysis. The typed source body is recursively
lowered only after the expected-type policy admits its sort. -/
def resolve (p : Phrase Γ Δ) (expected : Option Ty) :
    Except Diagnostic ((t : Ty) × Source Γ Δ t) :=
  match p, expected with
  | .term s, none => .ok ⟨_, s⟩
  | .term (t := t) s, some u =>
    if t = u then .ok ⟨_, s⟩ else .error .expectedMismatch
  | .overloaded n, some .nat => .ok ⟨_, .lit n⟩
  | .overloaded n, some .packet => .ok ⟨_, .vector 0 (.lit n) (.lit 0)⟩
  | .overloaded _, none => .error .ambiguous

theorem resolve_sound {p : Phrase Γ Δ} {expected r}
    (h : resolve p expected = .ok r) : Resolves p expected r.2 := by
  cases p with
  | term s =>
    cases expected with
    | none => cases h; exact .term s (Or.inl rfl)
    | some u =>
      simp only [resolve] at h
      split at h
      next he => cases h; exact .term s (Or.inr (congrArg some he.symm))
      next => contradiction
  | overloaded n =>
    cases expected with
    | none => contradiction
    | some t =>
      cases t <;> cases h
      · exact .nat n
      · exact .packet n

theorem resolve_complete {p : Phrase Γ Δ} {expected t} {s : Source Γ Δ t}
    (h : Resolves p expected s) : resolve p expected = .ok ⟨t, s⟩ := by
  cases h with
  | term s h => rcases h with h | h <;> subst h <;> simp [resolve]
  | nat => rfl
  | packet => rfl

abbrev emit (s : Source Γ Δ t) : Output Γ Δ := ⟨t, lower s, s.requirements⟩

def elaborate (p : Phrase Γ Δ) (expected : Option Ty) : Except Diagnostic (Output Γ Δ) :=
  (resolve p expected).map fun r => emit r.2

theorem emit_admissible {p : Phrase Γ Δ} {expected} {s : Source Γ Δ t}
    (h : Resolves p expected s) : Elaborates p expected (emit s) :=
  ⟨s, h, lower_sound s, fun _ => Iff.rfl, fun θ => (lower_typed s θ).symm⟩

theorem elaborate_sound {p : Phrase Γ Δ} {expected o}
    (h : elaborate p expected = .ok o) : Elaborates p expected o := by
  unfold elaborate at h
  cases hr : resolve p expected with
  | error e => simp [hr, Except.map] at h
  | ok r =>
    simp [hr, Except.map] at h
    subst o
    exact emit_admissible (resolve_sound hr)

/-- Completeness is for this typed, annotated fragment and explicit overload
policy. It does not claim to solve arbitrary dependent inference. -/
theorem elaborate_complete {p : Phrase Γ Δ} {expected t} {s : Source Γ Δ t}
    (h : Resolves p expected s) : elaborate p expected = .ok (emit s) := by
  simp [elaborate, resolve_complete h, Except.map]

theorem unresolved_overload (n : Nat) :
    ¬ ∃ (t : Ty) (s : Source Γ Δ t), Resolves (.overloaded n) none s := by
  rintro ⟨t, s, h⟩
  cases h

/-- Coherence is semantic, not equality of generated programs. -/
theorem elaborations_coherent {p : Phrase Γ Δ} {e} {a b : Output Γ Δ}
    (ha : Elaborates p e a) (hb : Elaborates p e b) :
    ∃ h : a.inferred = b.inferred,
      ∀ μ ρ δ, h ▸ a.code.eval μ ρ δ = b.code.eval μ ρ δ := by
  rcases a with ⟨ta, ac, acs⟩
  rcases b with ⟨bt, bc, bcs⟩
  obtain ⟨s, hs, hf, _⟩ := ha
  obtain ⟨t, ht, hg, _⟩ := hb
  have he : Sigma.mk ta s = Sigma.mk bt t :=
    Except.ok.inj ((resolve_complete hs).symm.trans (resolve_complete ht))
  cases he
  exact ⟨rfl, fun μ ρ δ => (hf μ ρ δ).trans (hg μ ρ δ).symm⟩

def Obligation.check (θ : Assignment) : Obligation → Bool
  | .assigned k => (θ.metas k).isSome
  | .universeZero k => θ.level k == some 0
  | .metaEq k n => θ.metas k == some n

theorem Obligation.check_correct (θ : Assignment) (c : Obligation) :
    c.check θ = true ↔ c.Holds θ := by
  cases c <;> simp [check, Holds, Option.isSome_iff_exists]

/-- The returned first failed obligation is actionable data, not a claim that
its constraint has no possible future solution. -/
def checkConstraints (θ : Assignment) : List Obligation → Except Diagnostic Unit
  | [] => .ok ()
  | c :: cs => if c.check θ then checkConstraints θ cs else .error (.unresolved c)

theorem checkConstraints_correct (θ : Assignment) (cs : List Obligation) :
    checkConstraints θ cs = .ok () ↔ Solves θ cs := by
  induction cs with
  | nil => simp [checkConstraints, Solves]
  | cons c cs ih =>
    simp only [checkConstraints]
    split
    next h => simp [ih, Solves, ← Obligation.check_correct, h]
    next h => simp [Solves, ← Obligation.check_correct, h]

/-- Final output retains executable code, a type, constraints and an assignment.
There is no proposition-valued field that manufactures acceptance. -/
structure Final (Γ Δ : List Ty) where
  output : Output Γ Δ
  assignment : Assignment

def finalize (θ : Assignment) (o : Output Γ Δ) : Except Diagnostic (Final Γ Δ) :=
  (checkConstraints θ o.constraints).map fun _ => ⟨o, θ⟩

def Accepted (p : Phrase Γ Δ) (e : Option Ty) (f : Final Γ Δ) : Prop :=
  Elaborates p e f.output ∧ Solves f.assignment f.output.constraints

theorem finalize_sound {p : Phrase Γ Δ} {e} {o : Output Γ Δ} {θ f}
    (ho : Elaborates p e o) (h : finalize θ o = .ok f) : Accepted p e f := by
  unfold finalize at h
  cases hc : checkConstraints θ o.constraints with
  | error d => simp [hc, Except.map] at h
  | ok u =>
    cases u
    simp [hc, Except.map] at h
    subst f
    exact ⟨ho, (checkConstraints_correct θ o.constraints).mp hc⟩

def emptyValuation : Valuation [] := fun x => nomatch x

/-- Install a closed declaration. Old constants keep their values and the new
head holds the actual computed dependent data. -/
def install (f : Final [] Δ) (δ : Valuation Δ) : Valuation f.output.extendedSignature :=
  δ.extend (f.output.code.eval f.assignment.value emptyValuation δ)

theorem install_old (f : Final [] Δ) (δ : Valuation Δ) (x : Var Δ t) :
    install f δ (.there x) = δ x := rfl

theorem install_source {p : Phrase [] Δ} {e} {f : Final [] Δ}
    (h : Accepted p e f) :
    ∃ s : Source [] Δ f.output.inferred, Resolves p e s ∧
      ∀ δ, install f δ .here = s.eval f.assignment.value emptyValuation δ := by
  obtain ⟨s, hs, hf, _⟩ := h.1
  exact ⟨s, hs, fun δ => hf _ _ δ⟩

/-- Full closed-declaration judgment, including the extended environment.
The signature extension is indexed by the inferred sort; the relation checks
old declarations and the source meaning of the newly installed value. -/
def DeclarationElaborates (δ : Valuation Δ) (p : Phrase [] Δ) (e : Option Ty)
    (f : Final [] Δ) (δ' : Valuation f.output.extendedSignature) : Prop :=
  Accepted p e f ∧
  (∀ {t} (x : Var Δ t), δ' (.there x) = δ x) ∧
  ∃ s : Source [] Δ f.output.inferred, Resolves p e s ∧
    δ' .here = s.eval f.assignment.value emptyValuation δ

theorem install_admissible {δ : Valuation Δ} {p : Phrase [] Δ} {e f}
    (h : Accepted p e f) : DeclarationElaborates δ p e f (install f δ) := by
  obtain ⟨s, hs, hv⟩ := install_source h
  exact ⟨h, fun _ => rfl, s, hs, hv δ⟩

/-- A rejected constraint is present and currently false. This is not a proof
of global unsatisfiability or nontermination of another search procedure. -/
theorem checkConstraints_diagnostic {θ : Assignment} {cs : List Obligation} {c}
    (h : checkConstraints θ cs = .error (.unresolved c)) :
    c ∈ cs ∧ ¬ c.Holds θ := by
  induction cs with
  | nil => contradiction
  | cons d ds ih =>
    simp only [checkConstraints] at h
    split at h
    next hd =>
      obtain ⟨hm, hn⟩ := ih h
      exact ⟨List.mem_cons_of_mem d hm, hn⟩
    next hd =>
      cases h
      exact ⟨List.mem_cons_self, fun hc => hd ((Obligation.check_correct θ c).mpr hc)⟩

end Elaboration
