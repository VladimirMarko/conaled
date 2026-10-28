import SquareKit.CurryHoward
import Examples.FullSourceNaturality
import SquareKit.CodeCategory

/-! Checked ordinary Lean and opt-in proof-author clients of the bounded bridge. -/
namespace Examples.CurryHoward
open CategoricalCompiler SquareKit SquareKit.CurryHoward

/-- Ordinary Lean clients remain ordinary functions. -/
def ordinarySwap {A B : Type} (p : A × B) : B × A := (p.2, p.1)
example : ordinarySwap (3, true) = (true, 3) := rfl

/-- The author writes the conjunction proof through introduction/elimination
operations, with just one explicit de Bruijn hypothesis. -/
def swap : Proof [.and .atom .truth] (.and .truth .atom) :=
  let p : Proof [.and .atom .truth] (.and .atom .truth) := Proof.hyp .here
  p.andRight.andIntro p.andLeft

example : eval meaning swap.term ((), ((7 : Nat), ())) = ((), 7) := rfl
example : eval meaning swap.term ((), ((7 : Nat), ())) = ordinarySwap (7, ()) := rfl
example : toProof (toProgram swap) = swap := proof_roundtrip swap
example : Program [] .truth := Proof.truth
example (p : Proof Γ a) (q : Proof Γ b) : Detour (p.andIntro q).andLeft p :=
  .conjunctionLeft p q
example (p : Proof Γ a) (q : Proof Γ b) : Term.Step (p.andIntro q).andRight.term q.term :=
  detour_simulates (.conjunctionRight p q)

/-- Simultaneous substitution may duplicate an argument. -/
def duplicate (Γ : List Formula) : Proof (.atom :: Γ) (.and .atom .atom) :=
  let x : Proof (.atom :: Γ) .atom := Proof.hyp .here
  x.andIntro x
example : (duplicate [.atom]).cut (Proof.hyp (Γ := [.atom]) .here) = duplicate [] := rfl

/-- In context x:A, abstract y:A and return x. Substituting a free z for x must
keep z free when it passes beneath the y binder. -/
def captureBody : Proof [.atom, .atom] (.implies .atom .atom) :=
  Proof.impliesIntro (Proof.hyp (.there .here))
def freeArgument : Proof [.atom] .atom := Proof.hyp .here
def captureRedex : Proof [.atom] (.implies .atom .atom) :=
  captureBody.impliesIntro.impliesElim freeArgument

def captureResult : Proof [.atom] (.implies .atom .atom) :=
  Proof.impliesIntro (Proof.hyp (.there .here))

example : captureBody.cut freeArgument = captureResult := rfl
example : Detour captureRedex captureResult := .implication captureBody freeArgument
example : Term.Step captureRedex.term captureResult.term :=
  detour_simulates (.implication captureBody freeArgument)
example : eval meaning captureResult.term ((), (7 : Nat)) 99 = 7 := rfl

/-- A capture bug would produce the identity, observably different at 99. -/
def capturedIncorrectly : Proof [.atom] (.implies .atom .atom) :=
  Proof.impliesIntro (Proof.hyp .here)
example : eval meaning capturedIncorrectly.term ((), (7 : Nat)) 99 ≠
    eval meaning captureResult.term ((), (7 : Nat)) 99 := by decide
example : captureResult ≠ capturedIncorrectly := by
  intro h
  have e := congrArg (fun p : Proof [.atom] (.implies .atom .atom) =>
    eval meaning p.term ((), (7 : Nat)) 99) h
  exact (by decide : (7 : Nat) ≠ 99) e

/-- Compatible reduction really traverses an abstraction. -/
example : Detour captureRedex.impliesIntro captureResult.impliesIntro :=
  .impliesIntro (.implication captureBody freeArgument)
example : Term.Step captureRedex.impliesIntro.term captureResult.impliesIntro.term :=
  detour_simulates (.impliesIntro (.implication captureBody freeArgument))

/-- Syntax outside the fragment does not acquire a proof rule. -/
example (t : Term NoPrim Γ a) (u : Term NoPrim (a :: Γ) b) :
    ¬ Admissible (.letE t u) := by intro h; cases h
example (t : Term NoPrim Γ a) : ¬ Admissible (.inl (b := b) t) := by intro h; cases h
example : ¬ Pure (.sum .base .base) := by intro h; cases h

/-- The same proof tree has two interpretations: raw categorical code and
functions on Nat. Raw code carries semantic equivalence, not syntactic category laws. -/
abbrev codeModel := STLCNaturality.ofTarget (rawTarget NoPrim)
abbrev functionModel := STLCNaturality.semantics Nat meaning
abbrev interpretation := STLCNaturality.soundMap (rawTarget NoPrim) (rawSound (B := Nat) meaning)

example : CategoryLaws (CodeCategory.ops NoPrim) (CodeCategory.equiv (B := Nat) meaning) :=
  CodeCategory.laws meaning
example : ClosedLaws (CodeCategory.equiv (B := Nat) meaning)
    (CodeCategory.products NoPrim) (CodeCategory.closed NoPrim) :=
  CodeCategory.closedLaws meaning

theorem interpretation_preserves :
    STLCNaturality.Preserves interpretation (equality _) codeModel functionModel :=
  STLCNaturality.sound_preserves _ _

theorem function_congr : STLCNaturality.ModelCongr (equality _) functionModel where
  pair := by intros; subst_vars; rfl
  copair := by intros; subst_vars; rfl
  curry := by intros; subst_vars; rfl

theorem two_models (p : Proof Γ a) :
    interpretation.map (STLCNaturality.compile codeModel p.term) =
      STLCNaturality.compile functionModel p.term :=
  STLCNaturality.naturality (STLCNaturality.soundMap_laws _ _) (equalityCongr _)
    function_congr interpretation_preserves p.term

/-- Compose raw-code interpretation with the existing bundled-function adapter;
this is an instance of naturality_comp, not a second induction over proofs. -/
theorem composed (p : Proof Γ a) :
    FunctionCategory.toTypes.map (interpretation.map (STLCNaturality.compile codeModel p.term)) =
      STLCNaturality.compile (FullSourceNaturality.bundle functionModel) p.term :=
  STLCNaturality.naturality_comp (STLCNaturality.soundMap_laws _ _)
    FunctionCategory.toTypes_laws (equalityCongr _)
    (FullSourceNaturality.bundle_congr functionModel) interpretation_preserves
    (FullSourceNaturality.bundle_preserves functionModel) p.term

example : STLCNaturality.compile functionModel swap.term ((), ((7 : Nat), ())) = ((), 7) := rfl
example : interpretation.map (STLCNaturality.compile codeModel swap.term)
    ((), ((7 : Nat), ())) = ((), 7) := by rw [two_models]; rfl
example : (STLCNaturality.compile (FullSourceNaturality.bundle functionModel) swap.term).hom
    ((), ((7 : Nat), ())) = ((), 7) := rfl

/-- An identity-only category on the compiler objects lacks even the terminal
arrow base → unit required by truth introduction. It is an unsupported target. -/
def identityOnly : CategoryOps Ty where
  Hom a b := PLift (a = b)
  ident := ⟨rfl⟩
  comp g f := ⟨f.down.trans g.down⟩

example : ¬ Nonempty (identityOnly.Hom .base .unit) := by
  rintro ⟨⟨h⟩⟩
  cases h

example : ¬ ∃ (T : TerminalOps identityOnly), T.unit = Ty.unit := by
  rintro ⟨T, h⟩
  have e := (T.terminal (a := Ty.base)).down
  rw [h] at e
  cases e

end Examples.CurryHoward
