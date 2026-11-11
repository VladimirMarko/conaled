import Mathlib.Data.Fin.Basic

/-! Retained contextual proofs for the bounded Curry–Löb experiment (#460). -/
namespace SquareKit.SelfReference

inductive Formula where
  | atom : Nat → Formula
  | bot : Formula
  | imp : Formula → Formula → Formula
  | box : Formula → Formula
  deriving DecidableEq, Repr

scoped infixr:60 " ⟶ " => Formula.imp
scoped prefix:75 "□" => Formula.box

abbrev Context := List Formula
abbrev Theory := Formula → Type

/-- A native proof tree. Necessitation's premise has an empty ordinary context. -/
inductive Derives (T : Theory) : Context → Formula → Type where
  | hyp {Γ} (i : Fin Γ.length) : Derives T Γ (Γ.get i)
  | ax {P} : T P → Derives T [] P
  | intro {Γ P Q} : Derives T (P :: Γ) Q → Derives T Γ (P ⟶ Q)
  | elim {Γ P Q} : Derives T Γ (P ⟶ Q) → Derives T Γ P → Derives T Γ Q
  | closed {Γ P} : Derives T [] P → Derives T Γ P
  | nec {P} : Derives T [] P → Derives T [] (□P)
  | dist (P Q) : Derives T [] (□(P ⟶ Q) ⟶ (□P ⟶ □Q))
  | four (P) : Derives T [] (□P ⟶ □(□P))

abbrev Theorem (T : Theory) (P : Formula) := Derives T [] P

namespace Derives
variable {T : Theory} {Γ : Context} {P Q R : Formula}

def here : Derives T (P :: Γ) P := .hyp ⟨0, by simp⟩

def identity (P : Formula) : Theorem T (P ⟶ P) := .intro here

/-- Closed implication composition, retaining both proof arguments. -/
def chain (f : Theorem T (P ⟶ Q)) (g : Theorem T (Q ⟶ R)) :
    Theorem T (P ⟶ R) := .intro (.elim (.closed g) (.elim (.closed f) here))

/-- Distribution lifts a closed implication, never an open assumption. -/
def boxMap (f : Theorem T (P ⟶ Q)) : Theorem T (□P ⟶ □Q) :=
  .elim (.dist P Q) (.nec f)
end Derives

/-- The sentence and its two actual closed diagonal derivations are supplied.
This interface does not assert that every theory has such a sentence. -/
structure Diagonal (T : Theory) (A : Formula) where
  sentence : Formula
  forward : Theorem T (sentence ⟶ (□sentence ⟶ A))
  backward : Theorem T ((□sentence ⟶ A) ⟶ sentence)

/-- Transparent truth at the selected sentence suffices for Curry's consequence.
The assumptions remain explicit even when the target is bottom. -/
def curry {T : Theory} {A : Formula} (d : Diagonal T A)
    (quote : Theorem T (d.sentence ⟶ □d.sentence))
    (reflect : Theorem T (□d.sentence ⟶ d.sentence)) : Theorem T A := by
  let ca : Theorem T (d.sentence ⟶ A) := .intro
    (.elim (.elim (.closed d.forward) .here) (.elim (.closed quote) .here))
  let ba : Theorem T (□d.sentence ⟶ A) := reflect.chain ca
  exact .elim ca (.elim d.backward ba)

/-- Conditional Löb transformation. Reflection is a theorem, not a hypothesis
in an ordinary nonempty context. -/
def lob {T : Theory} {A : Formula} (d : Diagonal T A)
    (reflect : Theorem T (□A ⟶ A)) : Theorem T A := by
  let step : Theorem T (□d.sentence ⟶ □A) := .intro
    (.elim
      (.elim (.closed (.dist (□d.sentence) A))
        (.elim (.closed d.forward.boxMap) .here))
      (.elim (.closed (.four d.sentence)) .here))
  let ba : Theorem T (□d.sentence ⟶ A) := step.chain reflect
  let l : Theorem T d.sentence := .elim d.backward ba
  exact .elim ba (.nec l)

def Consistent (T : Theory) : Prop := ¬ Nonempty (Theorem T .bot)

theorem no_reflection {T : Theory} (h : Consistent T) (d : Diagonal T .bot) :
    ¬ Nonempty (Theorem T (□Formula.bot ⟶ .bot)) := by
  rintro ⟨r⟩
  exact h ⟨lob d r⟩

/-- The precise missing contextual transparency certificate is also rejected. -/
theorem no_contextual_reflection {T : Theory} (h : Consistent T)
    (d : Diagonal T .bot) : ¬ Nonempty (Derives T [□Formula.bot] .bot) := by
  rintro ⟨r⟩
  exact no_reflection h d ⟨.intro r⟩

/-- Kripke interpretation with ordinary pointwise implication. -/
structure Model where
  World : Type
  access : World → World → Prop
  transitive : ∀ {u v w}, access u v → access v w → access u w
  atom : Nat → World → Prop

def Model.holds (M : Model) : Formula → M.World → Prop
  | .atom n, w => M.atom n w
  | .bot, _ => False
  | .imp P Q, w => M.holds P w → M.holds Q w
  | .box P, w => ∀ v, M.access w v → M.holds P v

def Model.Satisfies (M : Model) (Γ : Context) (w : M.World) : Prop :=
  ∀ i : Fin Γ.length, M.holds (Γ.get i) w

def Model.Valid (M : Model) (P : Formula) : Prop := ∀ w, M.holds P w

/-- Soundness is proved from the actual constructors, including discharge and
closed necessitation; no semantic-validity rule is present in the syntax. -/
theorem Derives.sound {T : Theory} (M : Model) (axioms : ∀ P, T P → M.Valid P)
    {Γ P} (d : Derives T Γ P) : ∀ w, M.Satisfies Γ w → M.holds P w := by
  induction d with
  | hyp i => intro w h; exact h i
  | ax a => intro w _; exact axioms _ a w
  | intro d ih =>
    intro w h p
    apply ih w
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact p
    · exact h j
  | elim f x ihf ihx => intro w h; exact ihf w h (ihx w h)
  | closed d ih => intro w _; exact ih w (fun i => Fin.elim0 i)
  | nec d ih => intro w _ v _; exact ih v (fun i => Fin.elim0 i)
  | dist P Q => intro w _ f p v h; exact f v h (p v h)
  | four P => intro w _ p v hv z hz; exact p z (M.transitive hv hz)

theorem Model.consistent (M : Model) (w : M.World) {T : Theory}
    (axioms : ∀ P, T P → M.Valid P) : Consistent T := by
  rintro ⟨d⟩
  exact d.sound M axioms w (fun i => Fin.elim0 i)

namespace Formula
/-- Propositional substitution. Named diagonal atoms have no special substitution
privilege: the theory must separately certify the resulting axiom instances. -/
def subst (f : Nat → Formula) : Formula → Formula
  | .atom n => f n
  | .bot => .bot
  | .imp P Q => subst f P ⟶ subst f Q
  | .box P => □(subst f P)

@[simp] theorem subst_id (P : Formula) : subst .atom P = P := by
  induction P <;> simp_all [subst]

@[simp] theorem subst_comp (f g : Nat → Formula) (P : Formula) :
    subst g (subst f P) = subst (fun n => subst g (f n)) P := by
  induction P <;> simp_all [subst]
end Formula

end SquareKit.SelfReference
