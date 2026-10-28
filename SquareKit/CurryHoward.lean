import SquareKit.STLCSubstitution

/-! A bounded, proof-relevant Curry–Howard interface. Natural deduction and
programs share the compiler's intrinsic tree; admissibility proofs are erased,
but the tree lives in Type. This is not extraction from Internal.Derives.
The single atom is exactly Ty.base; truth is included. -/
namespace SquareKit.CurryHoward
open CategoricalCompiler

inductive Formula where
  | atom | truth
  | and : Formula → Formula → Formula
  | implies : Formula → Formula → Formula
  deriving DecidableEq, Repr

@[reducible] def Formula.type : Formula → Ty
  | .atom => .base
  | .truth => .unit
  | .and a b => .prod a.type b.type
  | .implies a b => .arr a.type b.type

abbrev context (Γ : List Formula) : Ctx := Γ.map Formula.type

inductive Pure : Ty → Prop where
  | atom : Pure .base
  | truth : Pure .unit
  | and : Pure a → Pure b → Pure (.prod a b)
  | implies : Pure a → Pure b → Pure (.arr a b)

theorem Formula.pure (a : Formula) : Pure a.type := by
  induction a with
  | atom => exact .atom
  | truth => exact .truth
  | and _ _ ih ik => exact .and ih ik
  | implies _ _ ih ik => exact .implies ih ik

abbrev NoPrim (_ _ : Ty) := Empty

/-- Only these constructors are proof rules. Intermediate lambda domains are
checked too, so an unused sum hypothesis cannot sneak in via abstraction. -/
inductive Admissible : Term NoPrim Γ a → Prop where
  | hyp (v : Var Γ a) : Admissible (.var v)
  | truth : Admissible .unit
  | andIntro : Admissible t → Admissible u → Admissible (.pair t u)
  | andLeft : Admissible t → Admissible (.fst t)
  | andRight : Admissible t → Admissible (.snd t)
  | impliesIntro : Pure a → Admissible t → Admissible (.lam (a := a) t)
  | impliesElim : Admissible t → Admissible u → Admissible (.app t u)

theorem Admissible.rename {t : Term NoPrim Γ a} (h : Admissible t) (r : Term.Ren Γ Δ) :
    Admissible (Term.rename r t) := by
  induction h generalizing Δ with
  | hyp v => exact .hyp _
  | truth => exact .truth
  | andIntro _ _ ih ik => exact .andIntro (ih r) (ik r)
  | andLeft _ ih => exact .andLeft (ih r)
  | andRight _ ih => exact .andRight (ih r)
  | impliesIntro ha _ ih => exact .impliesIntro ha (ih _)
  | impliesElim _ _ ih ik => exact .impliesElim (ih r) (ik r)

private theorem lift_admissible (s : Term.Sub NoPrim Γ Δ)
    (h : ∀ {a} (v : Var Γ a), Admissible (s v)) :
    ∀ {a} (v : Var (b :: Γ) a), Admissible (Term.liftSub s v)
  | _, .here => .hyp _
  | _, .there v => (h v).rename _

theorem Admissible.subst {t : Term NoPrim Γ a} (h : Admissible t) (s : Term.Sub NoPrim Γ Δ)
    (hs : ∀ {a} (v : Var Γ a), Admissible (s v)) : Admissible (Term.subst s t) := by
  induction h generalizing Δ with
  | hyp v => exact hs v
  | truth => exact .truth
  | andIntro _ _ ih ik => exact .andIntro (ih s hs) (ik s hs)
  | andLeft _ ih => exact .andLeft (ih s hs)
  | andRight _ ih => exact .andRight (ih s hs)
  | impliesIntro ha _ ih => exact .impliesIntro ha (ih _ (lift_admissible s hs))
  | impliesElim _ _ ih ik => exact .impliesElim (ih s hs) (ik s hs)

/-- A proof object is an inspectable term and an erased admissibility certificate.
All external assumptions and the conclusion are formulas in the stated fragment. -/
structure Proof (Γ : List Formula) (a : Formula) where
  term : Term NoPrim (context Γ) a.type
  admissible : Admissible term

namespace Proof

def hyp (v : Var (context Γ) a.type) : Proof Γ a := ⟨.var v, .hyp v⟩
def truth : Proof Γ .truth := ⟨.unit, .truth⟩
def andIntro (p : Proof Γ a) (q : Proof Γ b) : Proof Γ (.and a b) :=
  ⟨.pair p.term q.term, .andIntro p.admissible q.admissible⟩
def andLeft (p : Proof Γ (.and a b)) : Proof Γ a := ⟨.fst p.term, .andLeft p.admissible⟩
def andRight (p : Proof Γ (.and a b)) : Proof Γ b := ⟨.snd p.term, .andRight p.admissible⟩
def impliesIntro (p : Proof (a :: Γ) b) : Proof Γ (.implies a b) :=
  ⟨.lam p.term, .impliesIntro a.pure p.admissible⟩
def impliesElim (p : Proof Γ (.implies a b)) (q : Proof Γ a) : Proof Γ b :=
  ⟨.app p.term q.term, .impliesElim p.admissible q.admissible⟩

/-- Cut substitutes the argument for the newest hypothesis, lifting beneath binders. -/
def cut (p : Proof (a :: Γ) b) (q : Proof Γ a) : Proof Γ b :=
  ⟨Term.subst (Term.single q.term) p.term, p.admissible.subst _ (fun v => by
    cases v with
    | here => exact q.admissible
    | there v => exact .hyp v)⟩

end Proof

/-- A program in this experiment is exactly the same admissible tree. The alias
is deliberate; there is no second syntax or quotient to keep synchronized. -/
abbrev Program := Proof

def toProgram (p : Proof Γ a) : Program Γ a := p
def toProof (p : Program Γ a) : Proof Γ a := p

@[simp] theorem proof_roundtrip (p : Proof Γ a) : toProof (toProgram p) = p := rfl
@[simp] theorem program_roundtrip (p : Program Γ a) : toProgram (toProof p) = p := rfl

/-- Intrinsic indices establish type preservation without a separate typing derivation. -/
def typedCompilation (p : Proof Γ a) : Term NoPrim (context Γ) a.type := (toProgram p).term

@[simp] theorem cut_compiles (p : Proof (a :: Γ) b) (q : Proof Γ a) :
    typedCompilation (p.cut q) = Term.subst (Term.single (typedCompilation q)) (typedCompilation p) := rfl

/-- Natural-deduction detours, with compatible closure through the proof rules.
This relation is specified by intro/elimination rules, independently of Term.Step. -/
inductive Detour : Proof Γ a → Proof Γ a → Prop where
  | implication (p : Proof (a :: Γ) b) (q : Proof Γ a) :
      Detour (p.impliesIntro.impliesElim q) (p.cut q)
  | conjunctionLeft (p : Proof Γ a) (q : Proof Γ b) : Detour (p.andIntro q).andLeft p
  | conjunctionRight (p : Proof Γ a) (q : Proof Γ b) : Detour (p.andIntro q).andRight q
  | andIntroLeft : Detour p p' → Detour (p.andIntro q) (p'.andIntro q)
  | andIntroRight {p : Proof Γ a} {q q' : Proof Γ b} : Detour q q' → Detour (p.andIntro q) (p.andIntro q')
  | andLeft : Detour p p' → Detour p.andLeft p'.andLeft
  | andRight : Detour p p' → Detour p.andRight p'.andRight
  | impliesIntro : Detour p p' → Detour p.impliesIntro p'.impliesIntro
  | impliesElimLeft : Detour p p' → Detour (p.impliesElim q) (p'.impliesElim q)
  | impliesElimRight {p : Proof Γ (.implies a b)} {q q' : Proof Γ a} : Detour q q' → Detour (p.impliesElim q) (p.impliesElim q')

/-- Each proof detour takes one actual compiler-syntax reduction step. -/
theorem detour_simulates {p q : Proof Γ a} (h : Detour p q) : Term.Step (typedCompilation p) (typedCompilation q) := by
  induction h with
  | implication p q => exact .beta p.term q.term
  | conjunctionLeft p q => exact .fstPair p.term q.term
  | conjunctionRight p q => exact .sndPair p.term q.term
  | andIntroLeft _ ih => exact .pairLeft ih
  | andIntroRight _ ih => exact .pairRight ih
  | andLeft _ ih => exact .fst ih
  | andRight _ ih => exact .snd ih
  | impliesIntro _ ih => exact .lam ih
  | impliesElimLeft _ ih => exact .appLeft ih
  | impliesElimRight _ ih => exact .appRight ih

def meaning {B : Type} : {a b : Ty} → NoPrim a b → Val B a → Val B b := fun p => nomatch p

theorem cut_meaning (p : Proof (a :: Γ) b) (q : Proof Γ a) (ρ : Val B (CategoricalCompiler.context (context Γ))) :
    eval meaning (p.cut q).term ρ = eval meaning p.term (ρ, eval meaning q.term ρ) :=
  Term.eval_single meaning p.term q.term ρ

theorem detour_meaning {p q : Proof Γ a} (h : Detour p q) (ρ : Val B (CategoricalCompiler.context (context Γ))) :
    eval meaning (typedCompilation p) ρ = eval meaning (typedCompilation q) ρ :=
  (detour_simulates h).sound meaning ρ

end SquareKit.CurryHoward
