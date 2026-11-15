import Applications.ClassicalControl.SourceSyntax

/-! The function-callback machine. Logical adequacy below uses only its four core
rules. The search theorem constructs its own finite execution. -/
namespace ClassicalControl
namespace Source

def callback (k : Term 0) (L : List Nat) (j : Nat) (O : List Nat) : Value → Term 0
  | .odd h => .walk k L (j+1) (O ++ [h])
  | _ => .stuck

/-- Admission is extensional membership in the specified closure family. -/
def IsCallback (f : Value → Term 0) : Prop :=
  ∃ k L j O, ∀ v, f v = callback k L j O v

def finish (c : Option (Nat × Nat × Nat)) (O : List Nat) : Value :=
  match c with
  | none => .none O
  | some (j,n,h) => .found j n h []

inductive State where
  | run : Term 0 → Stack → State
  | deliver : List Nat → Value → State

inductive Step : State → State → Prop where
  | app : Step (.run (.app t u) π) (.run t (.arg u π))
  | beta : Step (.run (.lam b) (.arg u π)) (.run (b.subst (single u)) π)
  | capture : Step (.run .cc (.arg t π)) (.run t (.arg (.saved π) π))
  | restore : Step (.run (.saved π) (.arg u ρ)) (.run u π)
  | callback (admitted : IsCallback f) : Step (.run (.ret v) (.cb f π)) (.run (f v) π)
  | output : Step (.run (.ret v) (.out L)) (.deliver L v)
  | walk (h : j < L.length) : Step (.run (.walk k L j O) π)
      (.run (.test k L j O) (.cb (Source.callback k L j O) π))
  | exhausted : Step (.run (.walk k L L.length O) π) (.run (.ret (.none O)) π)
  | odd (h : L[j]? = some (2*a+1)) : Step (.run (.test k L j O) π) (.run (.ret (.odd a)) π)
  | even (h : L[j]? = some (2*a)) : Step (.run (.test k L j O) π)
      (.run k (.arg (.ret (.found j (2*a) a O)) π))
  | lastOdd (h : L[j]? = some (2*a+1)) : Step (.run (.last L j c O) π)
      (.run (.last L (j+1) c (O++[a])) π)
  | lastEven (h : L[j]? = some (2*a)) : Step (.run (.last L j c O) π)
      (.run (.last L (j+1) (some (j,2*a,a)) O) π)
  | lastEnd : Step (.run (.last L L.length c O) π) (.run (.ret (finish c O)) π)

abbrev Runs := Relation.ReflTransGen Step


theorem Step.deterministic {s t u : State} (h : Step s t) (h' : Step s u) : t = u := by
  cases h <;> cases h' <;> simp_all
  all_goals omega

theorem terminal_runs {L v s} (h : Runs (.deliver L v) s) : s = .deliver L v := by
  induction h with
  | refl => rfl
  | tail _ step ih => rw [ih] at step; cases step

theorem delivery_unique {s L K v w} (hv : Runs s (.deliver L v))
    (hw : Runs s (.deliver K w)) : L = K ∧ v = w := by
  have total := Relation.ReflTransGen.total_of_right_unique (r := Step)
    (fun {_ _ _} h h' => Step.deterministic h h') hv hw
  rcases total with h | h
  · have he := terminal_runs h
    cases he; exact ⟨rfl, rfl⟩
  · have he := terminal_runs h
    cases he; exact ⟨rfl, rfl⟩

/-- Determinism upgrades the finite delivery path to accessibility of every successor. -/
theorem normalizes_of_delivery {s L v} (h : Runs s (.deliver L v)) :
    Acc (fun t s => Step s t) s := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => constructor; intro t h; cases h
  | head step _ ih =>
    constructor
    intro t ht
    have he := Step.deterministic step ht
    subst t
    exact ih

/-- Predecessor closure is the only logical requirement on a pole. -/
structure Pole where
  holds : State → Prop
  backwards : ∀ {s t}, Step s t → holds t → holds s

theorem Pole.backwards_runs (P : Pole) {s t} (h : Runs s t) : P.holds t → P.holds s := by
  induction h with
  | refl => exact id
  | tail _ step ih => exact fun ht => ih (P.backwards step ht)

/-- A pure core term has no literal runtime instructions or continuations. -/
inductive Pure : Term n → Prop where
  | var : Pure (.var i)
  | lam : Pure b → Pure (.lam b)
  | app : Pure t → Pure u → Pure (.app t u)
  | cc : Pure .cc

/- The output-free invariant permits dynamically captured continuations. -/
mutual
inductive CleanTerm : Term n → Prop where
  | var : CleanTerm (.var i)
  | lam : CleanTerm b → CleanTerm (.lam b)
  | app : CleanTerm t → CleanTerm u → CleanTerm (.app t u)
  | cc : CleanTerm .cc
  | saved : CleanStack π → CleanTerm (.saved π)
inductive CleanStack : Stack → Prop where
  | halt : CleanStack .halt
  | arg : CleanTerm t → CleanStack π → CleanStack (.arg t π)
end

theorem pure_clean {t : Term n} (h : Pure t) : CleanTerm t := by
  induction h with
  | var => exact .var
  | lam _ ih => exact .lam ih
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | cc => exact .cc

theorem clean_rename {t : Term n} (h : CleanTerm t) (f : Fin n → Fin m) :
    CleanTerm (t.rename f) := by
  induction t using Term.induct generalizing m with
  | var => exact .var
  | lam b ih => cases h; exact .lam (ih (by assumption) _)
  | app t u it iu => cases h; exact .app (it (by assumption) _) (iu (by assumption) _)
  | cc => exact .cc
  | saved π => cases h; exact .saved (by assumption)
  | _ => cases h

theorem clean_subst {t : Term n} (h : CleanTerm t) (σ : Fin n → Term m)
    (hs : ∀ i, CleanTerm (σ i)) : CleanTerm (t.subst σ) := by
  induction t using Term.induct generalizing m with
  | var i => exact hs i
  | lam b ih =>
    cases h
    apply CleanTerm.lam
    apply ih (by assumption)
    intro i; refine Fin.cases ?_ (fun i => ?_) i
    · exact .var
    · exact clean_rename (hs i) _
  | app t u it iu => cases h; exact .app (it (by assumption) _ hs) (iu (by assumption) _ hs)
  | cc => exact .cc
  | saved π => cases h; exact .saved (by assumption)
  | _ => cases h

def Clean : State → Prop
  | .run t π => CleanTerm t ∧ CleanStack π
  | .deliver _ _ => False

theorem clean_step {s t} (h : Step s t) (hs : Clean s) : Clean t := by
  cases h with
  | app => rcases hs with ⟨ht, hp⟩; cases ht; exact ⟨by assumption, .arg (by assumption) hp⟩
  | beta =>
    rcases hs with ⟨ht, hp⟩; cases ht; cases hp
    refine ⟨clean_subst (by assumption) _ ?_, by assumption⟩
    intro i; refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    assumption
  | capture => rcases hs with ⟨_, hp⟩; cases hp; exact ⟨by assumption, .arg (.saved (by assumption)) (by assumption)⟩
  | restore => rcases hs with ⟨ht, hp⟩; cases ht; cases hp; exact ⟨by assumption, by assumption⟩
  | _ => rcases hs with ⟨ht, _⟩; cases ht

theorem clean_runs {s t} (h : Runs s t) (hs : Clean s) : Clean t := by
  induction h with
  | refl => exact hs
  | tail _ step ih => exact clean_step step ih

abbrev L₀ : List Nat := [1,2,4]

def Pgood : Pole where
  holds s := ∃ z, Weak L₀ z ∧ Runs s (.deliver L₀ z)
  backwards h hs := by
    obtain ⟨z, hz, path⟩ := hs
    exact ⟨z, hz, (Relation.ReflTransGen.single h).trans path⟩

theorem terminal_pgood (L : List Nat) (z : Value) :
    Pgood.holds (.deliver L z) ↔ L = L₀ ∧ Weak L₀ z := by
  constructor
  · rintro ⟨w, hw, hr⟩
    have he : State.deliver L₀ w = .deliver L z := terminal_runs hr
    cases he
    exact ⟨rfl, hw⟩
  · rintro ⟨rfl, hz⟩; exact ⟨z, hz, .refl⟩

theorem good_nonempty : Pgood.holds (.run (.ret (.found 1 2 1 [0])) (.out L₀)) :=
  ⟨.found 1 2 1 [0], by simp [Weak], Relation.ReflTransGen.single .output⟩

theorem invalid_terminal : ¬ Pgood.holds (.deliver L₀ (.found 0 1 0 [])) := by
  rw [terminal_pgood]; simp [Weak]

theorem restricted_coherence (t : Term 0) (h : Pure t) :
    ¬ Pgood.holds (.run t .halt) := by
  rintro ⟨z, _, path⟩
  exact clean_runs path ⟨pure_clean h, .halt⟩

def universalPole : Pole := ⟨fun _ => True, fun _ _ => trivial⟩

theorem universal_accepts_invalid : universalPole.holds (.deliver L₀ (.found 0 1 0 [])) := trivial

theorem later_even_in_pole : Pgood.holds (.deliver L₀ (.found 2 4 2 [])) :=
  ⟨_, by simp [Weak], .refl⟩

theorem later_even_not_first : ¬ First L₀ (.found 2 4 2 []) := by
  simp [First]

end Source
end ClassicalControl
