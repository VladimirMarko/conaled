import SquareKit.Internal.NominalTelescope

/-! Checked cases for #369. The numbers come from #365: two base changes
retain (7,1), and the maintenance extension retains (7,1,1). The two capture
mutations change the dependent result index; resetting selected data also fails. -/
namespace Examples.NominalTelescope
open SquareKit.Internal.NominalTelescope

/-- Source atoms 0,1 are n,z. Bound atoms initially have spellings 2,3,4. -/
def N : Expr := .var 0
def Z : Expr := .var 1

def σ : Nat → Expr
  | 0 => .add (.var 0) (.lit 1)
  | 1 => .add (.var 2) (.lit 2)
  | a => .var a

def τ : Nat → Expr
  | 0 => .add (.var 0) (.var 0)
  | 2 => .add (.var 3) (.lit 3)
  | a => .var a

def ρ : Nat → Nat
  | 0 => 1
  | _ => 0

def finalN : Expr := (N.subst σ).subst τ
def finalZ : Expr := (Z.subst σ).subst τ

def selectedA : First finalN ρ := ⟨2, by decide⟩
def selectedB : Second selectedA := ⟨1, by decide⟩
def selectedR : Third selectedB := ⟨1, by decide⟩

def initialFrame : Frame (support N Z) := Frame.canonical _

/-- After σ, preserve the second spelling 3, freshen the first to 5.
The permutation also moves the third annotation and binder consistently. -/
def firstPerm : FinitePerm := (FinitePerm.swap 3 4).comp (FinitePerm.swap 3 5)
def firstFrame : Frame (support (N.subst σ) (Z.subst σ)) :=
  Frame.act firstPerm (by
    intro x hx
    have hx' : x < 3 := hx
    simp [firstPerm, FinitePerm.comp, FinitePerm.swap,
      Equiv.swap_apply_of_ne_of_ne (show x ≠ 3 by omega) (show x ≠ 5 by omega),
      Equiv.swap_apply_of_ne_of_ne (show x ≠ 3 by omega) (show x ≠ 4 by omega)])
    (Frame.canonical _)

/-- After τ, keep the first spelling 5 and freshen the second from 3 to 6. -/
def finalPerm : FinitePerm := (FinitePerm.swap 4 5).comp (FinitePerm.swap 5 6)
def finalFrame : Frame (support finalN finalZ) :=
  Frame.act finalPerm (by
    intro x hx
    have hx' : x < 4 := hx
    simp [finalPerm, FinitePerm.comp, FinitePerm.swap,
      Equiv.swap_apply_of_ne_of_ne (show x ≠ 5 by omega) (show x ≠ 6 by omega),
      Equiv.swap_apply_of_ne_of_ne (show x ≠ 4 by omega) (show x ≠ 5 by omega)])
    (Frame.canonical _)

example : firstFrame.name 0 = 5 ∧ firstFrame.name 1 = 3 := by decide
example : finalFrame.name 0 = 5 ∧ finalFrame.name 1 = 6 := by decide

/-- Both routes are the same alpha class, for every program in the fragment. -/
example : substitute τ (substitute σ (program N Z)) =
    substitute (fun x => (σ x).subst τ) (program N Z) := substitute_comp σ τ _

example : substitute .var (program N Z) = program N Z := substitute_id _

/-- The named result is compared with the independently specified contextual
family before evaluating the expected numerical observation. -/
theorem selected_two : nominalObserve finalFrame selectedA selectedB =
    (⟨7, ⟨1, by decide⟩⟩ : Observation) := by
  exact (two_substitutions N Z σ τ ρ finalFrame selectedA selectedB).trans rfl

theorem selected_three : nominalTail finalFrame selectedA selectedB selectedR =
    (⟨7, ⟨1, by decide⟩, ⟨1, by decide⟩⟩ : TailObservation) := by
  exact (tail_two_substitutions N Z σ τ ρ finalFrame selectedA selectedB selectedR).trans rfl

/-- The quotient-level substitution, rather than only a raw-frame evaluation,
retains the complete dependent observation through both stages. -/
example : abstractTail (substitute τ (substitute σ (program N Z))).2.2
    selectedA selectedB selectedR = (⟨7, ⟨1, by decide⟩, ⟨1, by decide⟩⟩ : TailObservation) := by
  exact (tail_substitute_preserves (substitute σ (program N Z)) τ ρ
    selectedA selectedB selectedR).trans
    ((tail_substitute_preserves (program N Z) σ (fun x => (τ x).eval ρ) _ _ _).trans
      ((abstractTail_comparison _ _ _ _).trans rfl))

/-- Alpha abstraction hides bound spelling, but does not collapse free syntax. -/
example : program (.var 0) (.var 1) ≠ program (.var 1) (.var 1) := by
  intro h
  have := congrArg (fun p : Program => p.1) h
  contradiction

/-- Changing the representative cannot change the selected value. -/
example : nominalObserve (Z := finalZ) (Frame.canonical _) selectedA selectedB =
    nominalObserve finalFrame selectedA selectedB :=
  alpha_invariant _ _ (Frame.alpha _ _) _ _

example : nominalTail (Z := finalZ) (Frame.canonical _) selectedA selectedB selectedR =
    nominalTail finalFrame selectedA selectedB selectedR :=
  tail_alpha_invariant _ _ (Frame.alpha _ _) _ _ _

/-- Omitting the first freshening captures free atom 2 in σ(z).
The independent calculation expects index 3, whereas capture gives 4. -/
theorem first_capture :
    (Expr.add (Z.subst σ) (.var (initialFrame.name 0))).eval
      (initialFrame.env (fun x => if x = 0 then 1 else 0) 1 1 0) = 4 ∧
    (nominalObserve firstFrame
      (⟨1, by decide⟩ : First (N.subst σ) (fun x => if x = 0 then 1 else 0))
      ⟨1, by decide⟩).1 = 3 := by decide

/-- Omitting the second freshening captures free atom 3 in τ(a).
The old frame is deliberately used on the new expression without a freshness
proof; it cannot inhabit Frame (support finalN finalZ). -/
theorem second_capture :
    (Expr.add finalZ (.var (firstFrame.name 0))).eval
      (firstFrame.env ρ 2 1 1) = 8 ∧
    (nominalObserve finalFrame selectedA selectedB).1 = 7 := by decide

/-- The retained value, rather than merely an inhabitant of its type, matters. -/
theorem resetting_second_fails :
    nominalObserve finalFrame selectedA (⟨0, by decide⟩ : Second selectedA) ≠
      nominalObserve finalFrame selectedA selectedB := by
  simp only [comparison]
  intro h
  have := congrArg (fun o : Observation => o.2.val) h
  contradiction

theorem resetting_third_fails :
    nominalTail finalFrame selectedA selectedB (⟨0, by decide⟩ : Third selectedB) ≠
      nominalTail finalFrame selectedA selectedB selectedR := by
  simp only [tail_comparison]
  intro h
  have := congrArg (fun o : TailObservation => o.2.2.val) h
  contradiction

example : ¬ ∃ get : Abstraction N Z → Nat, ∀ f, get ⟦f⟧ = f.name 0 :=
  no_bound_name_observer N Z

end Examples.NominalTelescope
