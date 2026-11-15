import SquareKit.CertifiedIndexConversion

/-! Selected dependent conversion, open mixed peaks, and rejected semantic overclaims. -/
namespace CertifiedIndexConversion.Examples
open Expr

def source (n : Expr) := double (add zero n)
def target (n : Expr) := add n n

/-- The named explicit proof recipe, before invoking any conversion checker. -/
theorem explicit (n : Expr) : Converts (source n) (target n) :=
  .trans (.step (.underDouble (.addZero n))) (.step (.double n))

def clientCert (n : Expr) : Certificate := ⟨normalize (target n)⟩

theorem client_checked (n : Expr) : check (source n) (target n) (clientCert n) = true := by
  simp [check, clientCert, source, target, normalize, addNF]

/-- The original selected section, independently specified in Fin. -/
def last (ρ : Nat → Nat) (e : Expr) : Fin (meaning ρ e + 1) :=
  ⟨meaning ρ e, by omega⟩

def converted (ρ : Nat → Nat) (n : Expr) : Fin (meaning ρ (target n) + 1) :=
  elaborate ρ (clientCert n) (client_checked n) (last ρ (source n))

theorem converted_selected (ρ : Nat → Nat) (n : Expr) :
    (converted ρ n).val = 2 * meaning ρ n := by
  change meaning ρ (source n) = 2 * meaning ρ n
  simp [source, meaning]

def explicitlyTransported (ρ : Nat → Nat) (n : Expr) : Fin (meaning ρ (target n) + 1) :=
  Fin.cast (congrArg (· + 1) (converts_meaning (explicit n) ρ)) (last ρ (source n))

theorem routes_agree (ρ : Nat → Nat) (n : Expr) :
    converted ρ n = explicitlyTransported ρ n := by rfl

/-- Two substitutions change both the dependent type and the selected section. -/
def σ : Nat → Expr := fun i => if i = 0 then succ (var 1) else var i
def τ : Nat → Expr := fun i => if i = 1 then succ zero else var i

theorem two_substitutions : subst τ (subst σ (var 0)) = succ (succ zero) := rfl

theorem substituted_conversion : Converts
    (subst τ (subst σ (source (var 0)))) (subst τ (subst σ (target (var 0)))) :=
  converts_subst (converts_subst (explicit (var 0)) σ) τ

example (ρ : Nat → Nat) : (converted ρ (subst τ (subst σ (var 0)))).val = 4 := by
  rw [converted_selected, two_substitutions]
  rfl

example (ρ : Nat → Nat) : (converted ρ (succ (succ zero)) : Fin 5) = ⟨4, by change 4 < 5; decide⟩ := rfl

/-- The outer double step duplicates the open redex; both copies are reduced. -/
theorem mixed_peak (n : Expr) :
    Reduces (add (add zero n) (add zero n)) (target n) ∧
      Reduces (double n) (target n) := by
  constructor
  · exact (Relation.ReflTransGen.single (.left _ (.addZero _))).trans
      (Relation.ReflTransGen.single (.right _ (.addZero _)))
  · exact Relation.ReflTransGen.single (.double _)

theorem commutes_semantically (ρ : Nat → Nat) :
    meaning ρ (add (var 0) (var 1)) = meaning ρ (add (var 1) (var 0)) := Nat.add_comm _ _

/-- Mathematical equality is broader than this setting's generated conversion. -/
example : ¬ Converts (add (var 0) (var 1)) (add (var 1) (var 0)) := by
  intro h
  have := converts_normalize h
  contradiction

/-- An unconstrained old interpretation of add cannot always admit A₀. -/
example : ¬ ∀ y : Nat, (fun _ _ : Nat => 0) 0 y = y := by
  intro h
  have := h 1
  contradiction

-- Kernel-checked positive and failure cases; #eval below also executes the producer/checker.
example : produce (source (succ (succ zero))) (target (succ (succ zero))) =
    some (clientCert (succ (succ zero))) := by decide
example : check (source (var 0)) (target (var 0)) ⟨zero⟩ = false := by decide
example : produce (add (var 0) (var 1)) (add (var 1) (var 0)) = none := by decide
#eval produce (source (succ (succ zero))) (target (succ (succ zero)))
#eval check (source (var 0)) (target (var 0)) (clientCert (var 0))
#eval check (source (var 0)) (target (var 0)) ⟨zero⟩

/-- Separate union control; each rule is finite and type-preserving. -/
inductive Bad where
  | a | b | c | f : Bad → Bad
  deriving DecidableEq, Repr

inductive BadStep : Bad → Bad → Prop where
  | p : BadStep (.f .a) .b
  | q : BadStep (.f .a) .c
  | ctx {x y} : BadStep x y → BadStep (.f x) (.f y)

abbrev BadReduces := Relation.ReflTransGen BadStep

theorem b_terminal {w : Bad} (h : BadReduces .b w) : w = .b := by
  induction h with
  | refl => rfl
  | tail _ h ih => cases ih; cases h

theorem c_terminal {w : Bad} (h : BadReduces .c w) : w = .c := by
  induction h with
  | refl => rfl
  | tail _ h ih => cases ih; cases h

theorem nonconfluent_union :
    BadReduces (.f .a) .b ∧ BadReduces (.f .a) .c ∧
      ¬ ∃ w, BadReduces .b w ∧ BadReduces .c w := by
  refine ⟨Relation.ReflTransGen.single .p, Relation.ReflTransGen.single .q, ?_⟩
  rintro ⟨w, hb, hc⟩
  have := (b_terminal hb).symm.trans (c_terminal hc)
  cases this

/-- Distinct prescribed meanings prevent joint admission. -/
example {M : Type*} (denote : Bad → M) (distinct : denote .b ≠ denote .c) :
    ¬ (denote (.f .a) = denote .b ∧ denote (.f .a) = denote .c) := by
  rintro ⟨hp, hq⟩
  exact distinct (hp.symm.trans hq)

/-- A collapsed interpretation can validate both despite nonconfluence. -/
example : (fun _ : Bad => PUnit.unit) (.f .a) = (fun _ : Bad => PUnit.unit) .b ∧
    (fun _ : Bad => PUnit.unit) (.f .a) = (fun _ : Bad => PUnit.unit) .c := ⟨rfl, rfl⟩

end CertifiedIndexConversion.Examples
