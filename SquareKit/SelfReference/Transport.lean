import SquareKit.SelfReference.Native
import SquareKit.DependentTheoryMaps

/-! The contextual calculus as a local-certificate rule presentation. -/
namespace SquareKit.SelfReference
namespace Presentation
open DependentTheoryMaps

abbrev Judgment := Context × Formula

inductive Label (T : Theory) where
  | hyp (Γ : Context) (i : Fin Γ.length)
  | ax (P : Formula) (a : T P)
  | intro (Γ : Context) (P Q : Formula)
  | elim (Γ : Context) (P Q : Formula)
  | closed (Γ : Context) (P : Formula)
  | nec (P : Formula)
  | dist (P Q : Formula)
  | four (P : Formula)

abbrev Label.count {T} : Label T → Nat
  | .hyp .. | .ax .. | .dist .. | .four .. => 0
  | .intro .. | .closed .. | .nec .. => 1
  | .elim .. => 2

def Label.premise {T} : (r : Label T) → Fin r.count → Judgment
  | .hyp .., i | .ax .., i | .dist .., i | .four .., i => Fin.elim0 i
  | .intro Γ P Q, _ => (P :: Γ, Q)
  | .elim Γ P Q, i => if i = 0 then (Γ, P ⟶ Q) else (Γ, P)
  | .closed _ P, _ | .nec P, _ => ([], P)

def Label.conclusion {T} : Label T → Judgment
  | .hyp Γ i => (Γ, Γ.get i)
  | .ax P _ => ([], P)
  | .intro Γ P Q => (Γ, P ⟶ Q)
  | .elim Γ _ Q => (Γ, Q)
  | .closed Γ P => (Γ, P)
  | .nec P => ([], □P)
  | .dist P Q => ([], □(P ⟶ Q) ⟶ (□P ⟶ □Q))
  | .four P => ([], □P ⟶ □(□P))

abbrev rules (T : Theory) : Rules Judgment where
  Label := Label T
  count := Label.count
  premise := Label.premise
  conclusion := Label.conclusion

abbrev Tree (T : Theory) (H : Judgment → Type) (j : Judgment) := Derivation (rules T) H j
abbrev ClosedTree (T : Theory) (j : Judgment) := Tree T (fun _ => Empty) j

def node {T : Theory} {H : Judgment → Type} (r : Label T)
    (ds : (i : Fin r.count) → Tree T H (r.premise i)) : Tree T H r.conclusion :=
  Derivation.rule (R := rules T) r ds

def encode {T Γ P} : Derives T Γ P → ClosedTree T (Γ, P)
  | .hyp i => node (.hyp Γ i) (fun i => Fin.elim0 i)
  | .ax a => node (.ax P a) (fun i => Fin.elim0 i)
  | .intro d => node (.intro _ _ _) (fun _ => encode d)
  | .elim f x => node (.elim _ _ _) (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact encode f
      · have : j = 0 := Fin.eq_zero j
        subst j
        exact encode x)
  | .closed d => node (.closed _ _) (fun _ => encode d)
  | .nec d => node (.nec _) (fun _ => encode d)
  | .dist P Q => node (.dist P Q) (fun i => Fin.elim0 i)
  | .four P => node (.four P) (fun i => Fin.elim0 i)

/-- Decoding rules inspects the same ordered premise positions as encoding. -/
def decode {T j} : ClosedTree T j → Derives T j.1 j.2
  | .hyp h => nomatch h
  | .rule (Label.hyp _ i) _ => .hyp i
  | .rule (Label.ax _ a) _ => .ax a
  | .rule (Label.intro _ _ _) ds => .intro (decode (ds 0))
  | .rule (Label.elim _ _ _) ds => .elim (decode (ds 0)) (decode (ds 1))
  | .rule (Label.closed _ _) ds => .closed (decode (ds 0))
  | .rule (Label.nec _) ds => .nec (decode (ds 0))
  | .rule (Label.dist P Q) _ => .dist P Q
  | .rule (Label.four P) _ => .four P

@[simp] theorem decode_encode {T Γ P} (d : Derives T Γ P) : decode (encode d) = d := by
  induction d with
  | hyp => rfl
  | ax => rfl
  | intro d ih => exact congrArg Derives.intro ih
  | elim f x ihf ihx => exact congrArg₂ Derives.elim ihf ihx
  | closed d ih => exact congrArg Derives.closed ih
  | nec d ih => exact congrArg Derives.nec ih
  | dist => rfl
  | four => rfl

def mapJudgment (f : Nat → Formula) (j : Judgment) : Judgment :=
  (j.1.map (Formula.subst f), Formula.subst f j.2)

/-- Only axiom instances require author certificates. The generic transport
recursion supplies all subsequent contextual proof substitution. -/
def substitution {T U : Theory} (f : Nat → Formula)
    (axioms : ∀ P, T P → U (Formula.subst f P)) :
    TheoryMap (rules T) (rules U) (mapJudgment f) where
  certificate r := by
    cases r with
    | hyp Γ i =>
      have h : (Γ.map (Formula.subst f)).get
          ⟨i.val, by simp⟩ = Formula.subst f (Γ.get i) := by simp
      change Tree U _ (Γ.map (Formula.subst f), Formula.subst f (Γ.get i))
      rw [← h]
      exact node (.hyp _ _) (fun i => Fin.elim0 i)
    | ax P a => exact node (.ax _ (axioms P a)) (fun i => Fin.elim0 i)
    | intro Γ P Q =>
      exact node (.intro _ _ _) (fun _ => .hyp ⟨0, rfl⟩)
    | elim Γ P Q =>
      refine node (.elim _ (Formula.subst f P) _) (fun i => ?_)
      refine .hyp ⟨i, ?_⟩
      change mapJudgment f (if i = 0 then (Γ, P ⟶ Q) else (Γ, P)) = _
      split <;> simp_all [Label.premise, Label.conclusion, mapJudgment, Formula.subst]
    | closed Γ P => exact node (.closed _ _) (fun _ => .hyp ⟨0, rfl⟩)
    | nec P => exact node (.nec _) (fun _ => .hyp ⟨0, rfl⟩)
    | dist P Q => exact node (.dist _ _) (fun i => Fin.elim0 i)
    | four P => exact node (.four _) (fun i => Fin.elim0 i)

/-- There is no second native proof-substitution induction. -/
def substitute {T U : Theory} (f : Nat → Formula)
    (axioms : ∀ P, T P → U (Formula.subst f P))
    {Γ P} (d : Derives T Γ P) :
    Derives U (Γ.map (Formula.subst f)) (Formula.subst f P) :=
  decode ((substitution f axioms).transport (fun _ (h : Empty) => h) (encode d))

/-- Grafting discharges meta-premises, each of which is an entire contextual
judgment. This is not substitution for an ordinary open hypothesis. -/
theorem substitution_graft {T U : Theory} (f : Nat → Formula)
    (axioms : ∀ P, T P → U (Formula.subst f P))
    {H A : Judgment → Type} {A' B : Judgment → Type}
    (h : ∀ j, H j → A' (mapJudgment f j))
    (a : ∀ j, A j → B (mapJudgment f j))
    (k : ∀ j, H j → Tree T A j) (l : ∀ j, A' j → Tree U B j)
    (hl : ∀ j p, (substitution f axioms).transport a (k j p) =
      l (mapJudgment f j) (h j p)) {j} (d : Tree T H j) :
    (substitution f axioms).transport a (d.graft k) =
      ((substitution f axioms).transport h d).graft l :=
  TheoryMap.transport_graft _ h a k l hl d

theorem substitution_comp {T U V : Theory} (f g : Nat → Formula)
    (first : ∀ P, T P → U (Formula.subst f P))
    (second : ∀ P, U P → V (Formula.subst g P))
    {j} (d : ClosedTree T j) :
    ((substitution f first).comp (substitution g second)).transport
      (fun _ (h : Empty) => h) d =
    (substitution g second).transport (H' := fun _ => Empty) (fun _ (h : Empty) => h)
      ((substitution f first).transport (fun _ (h : Empty) => h) d) :=
  TheoryMap.comp_transport (substitution f first) (substitution g second)
    (B := fun _ => Empty) (C := fun _ => Empty)
    (fun _ (h : Empty) => h) (fun _ (h : Empty) => h) d

/-- Ordinary formula substitution also transports the retained diagonal witness. -/
def substituteDiagonal {T U : Theory} (f : Nat → Formula)
    (axioms : ∀ P, T P → U (Formula.subst f P)) {A} (d : Diagonal T A) :
    Diagonal U (Formula.subst f A) where
  sentence := Formula.subst f d.sentence
  forward := substitute f axioms d.forward
  backward := substitute f axioms d.backward

/-- A proposed truth-elimination certificate has a meta-premise whose whole
judgment is the contextual hypothesis. Grafting that hypothesis and decoding
would give the forbidden reflection theorem. -/
theorem no_truth_elimination_certificate {T : Theory} (h : Consistent T)
    (d : Diagonal T .bot) : ¬ Nonempty (Tree T
      (fun j => {_i : Fin 1 // ([□Formula.bot], □Formula.bot) = j})
      ([□Formula.bot], Formula.bot)) := by
  rintro ⟨certificate⟩
  let plug : ∀ j, {_i : Fin 1 // ([□Formula.bot], □Formula.bot) = j} → ClosedTree T j :=
    fun _ p => p.property ▸ encode (Derives.here (T := T) (Γ := []) (P := □Formula.bot))
  exact no_contextual_reflection h d ⟨decode (certificate.graft plug)⟩

end Presentation
end SquareKit.SelfReference
