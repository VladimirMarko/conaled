import Applications.Circuits.Syntax
import Applications.Timing.Digital

/-! # Every circuit and every compiled source term has a timing/stability proof -/

namespace Applications.Circuits

open FirstOrderCompiler Applications.Timing
open scoped Matrix

def Gate.digital : Gate a b → Digital a b
  | .constant v => Digital.constant v
  | .not d => Digital.unary d Bool.not
  | .nand d₁ d₂ => Digital.binary d₁ d₂ (fun x => !(x.1 && x.2))
  | .nor d₁ d₂ => Digital.binary d₁ d₂ (fun x => !(x.1 || x.2))
  | .xor d₁ d₂ => Digital.binary d₁ d₂ (fun x => Bool.xor x.1 x.2)

def digitalTarget : Target Gate where
  Hom := Digital
  ident := Digital.identity _
  comp := Digital.compose
  terminal := Digital.terminate _
  fst := Digital.first _ _
  snd := Digital.second _ _
  pair := Digital.pair
  primitive := Gate.digital

namespace Circuit

def digital (c : Circuit a b) : Digital a b := c.interpret digitalTarget

/- Projection equations avoid unfolding proof fields when evaluating circuits. -/
@[simp] theorem analog_compose (g : Circuit b c) (f : Circuit a b) (s : Val Signal a) :
    (Circuit.compose g f).digital.analog s = g.digital.analog (f.digital.analog s) := rfl
@[simp] theorem analog_pair (f : Circuit a b) (g : Circuit a c) (s : Val Signal a) :
    (Circuit.pair f g).digital.analog s = (f.digital.analog s, g.digital.analog s) := rfl
@[simp] theorem analog_first (s : Val Signal (.prod a b)) :
    (Circuit.first : Circuit (.prod a b) a).digital.analog s = s.1 := rfl
@[simp] theorem analog_second (s : Val Signal (.prod a b)) :
    (Circuit.second : Circuit (.prod a b) b).digital.analog s = s.2 := rfl
@[simp] theorem analog_gate (p : Gate a b) (s : Val Signal a) :
    (Circuit.gate p).digital.analog s = p.digital.analog s := rfl

@[simp] theorem timing_compose_apply (g : Circuit b c) (f : Circuit a b) (τ : Times a) :
    (Circuit.compose g f).digital.timing τ = g.digital.timing (f.digital.timing τ) := rfl
@[simp] theorem timing_pair_apply (f : Circuit a b) (g : Circuit a c) (τ : Times a) :
    (Circuit.pair f g).digital.timing τ = Sum.elim (f.digital.timing τ) (g.digital.timing τ) := rfl
@[simp] theorem timing_first_apply (τ : Times (.prod a b)) :
    (Circuit.first : Circuit (.prod a b) a).digital.timing τ = (fun i => τ (.inl i)) := rfl
@[simp] theorem timing_second_apply (τ : Times (.prod a b)) :
    (Circuit.second : Circuit (.prod a b) b).digital.timing τ = (fun i => τ (.inr i)) := rfl
@[simp] theorem timing_gate_apply (p : Gate a b) (τ : Times a) :
    (Circuit.gate p).digital.timing τ = p.digital.timing τ := rfl

@[simp] theorem timing_compose_at (g : Circuit b c) (f : Circuit a b) (τ : Times a) (i : Port c) :
    (Circuit.compose g f).digital.timing τ i = g.digital.timing (f.digital.timing τ) i := rfl
@[simp] theorem timing_pair_at (f : Circuit a b) (g : Circuit a c) (τ : Times a)
    (i : Port (.prod b c)) :
    (Circuit.pair f g).digital.timing τ i = Sum.elim (f.digital.timing τ) (g.digital.timing τ) i := rfl
@[simp] theorem timing_first_at (τ : Times (.prod a b)) (i : Port a) :
    (Circuit.first : Circuit (.prod a b) a).digital.timing τ i = τ (.inl i) := rfl
@[simp] theorem timing_second_at (τ : Times (.prod a b)) (i : Port b) :
    (Circuit.second : Circuit (.prod a b) b).digital.timing τ i = τ (.inr i) := rfl
@[simp] theorem timing_gate_at (p : Gate a b) (τ : Times a) (i : Port b) :
    (Circuit.gate p).digital.timing τ i = p.digital.timing τ i := rfl

theorem gate_value (p : Gate a b) (x : Val Bool a) : p.digital.value x = p.meaning x := by
  cases p <;> rfl

def sound : Sound Bool target Gate.meaning where
  denote c := c.digital.value
  ident _ := rfl
  comp _ _ _ := rfl
  terminal _ := rfl
  fst _ := rfl
  snd _ := rfl
  pair _ _ _ := rfl
  primitive := gate_value

theorem compile_value (t : Term Gate Γ a) (v : Val Bool (context Γ)) :
    (compile target t).digital.value v = eval Gate.meaning t v :=
  compile_sound target sound t v

/--
For arbitrary source syntax, input signals, stability intervals, and values,
the generated analog circuit agrees with source evaluation at every time in
its computed output intervals.  Let-bound sharing is included by the frontend.
-/
theorem compile_stable (t : Term Gate Γ a) {s τ v}
    (h : Stable (context Γ) s τ v) :
    Stable a ((compile target t).digital.analog s)
      ((compile target t).digital.timing τ) (eval Gate.meaning t v) := by
  rw [← compile_value t v]
  exact (compile target t).digital.correct h

theorem compile_matrix_stable (t : Term Gate Γ a) {s τ v}
    (h : Stable (context Γ) s τ v) :
    Stable a ((compile target t).digital.analog s)
      ((compile target t).digital.matrix *ᵥ τ) (eval Gate.meaning t v) := by
  rw [Digital.matrix_correct]
  exact compile_stable t h

def compileSquare (t : Term Gate Γ a) :
    Squares.Square
      (Relational.witness (Digital.object (context Γ)))
      (Relational.witness (Digital.object a)) :=
  (compile target t).digital.square

/-- Circuit syntax has semantic laws; raw ASTs need not be syntactically equal. -/
def Equivalent (f g : Circuit a b) : Prop := f.digital = g.digital

theorem compose_assoc (h : Circuit c d) (g : Circuit b c) (f : Circuit a b) :
    Equivalent (.compose h (.compose g f)) (.compose (.compose h g) f) :=
  Digital.compose_assoc h.digital g.digital f.digital

theorem compose_identity (f : Circuit a b) : Equivalent (.compose f .identity) f :=
  Digital.compose_identity f.digital

theorem first_pair (f : Circuit a b) (g : Circuit a c) :
    Equivalent (.compose .first (.pair f g)) f :=
  Digital.first_pair f.digital g.digital

theorem pair_eta (f : Circuit a (.prod b c)) :
    Equivalent (.pair (.compose .first f) (.compose .second f)) f :=
  Digital.pair_eta f.digital

theorem timing_compose (g : Circuit b c) (f : Circuit a b) :
    (Circuit.compose g f).digital.matrix = g.digital.matrix * f.digital.matrix :=
  Digital.matrix_compose g.digital f.digital

end Circuit
end Applications.Circuits
