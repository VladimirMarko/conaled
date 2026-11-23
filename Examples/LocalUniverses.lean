import SquareKit.LocalUniverses

/-! Checked positive and negative cases for the Type-family specialization.
Native equality in this file is proof irrelevant. Higher identity is an
explicitly separate regression obligation, not a capability of this model. -/

namespace Examples.LocalUniverses

open DependentSquares SquareKit.LocalUniverses

namespace DependentTail

/-- Reuse the existing family whose second fiber depends on the first value. -/
def first : Family Nat := Family.present Example.AS
def second : Family first.Comprehension := Family.present Example.BS

def selected : first.Term := Example.lastIndex
def witness : (second.reindex (extend idSub selected)).Term :=
  app Example.tighten Example.lastIndex

def pair : (first.sigma second).Term := Family.pair selected witness

def shift : Nat → Nat := fun n => n + 1
def double : Nat → Nat := fun n => 2 * n

/-- Both routes preserve `Σ i:Fin(n+1), Fin(i.val+1)`, including its second
component, after the two nonidentity substitutions. -/
theorem routes_agree :
    Family.termReindex (Family.termReindex pair shift) double =
      pairTerm (B := tySub Example.BS (lift (compSub shift double)))
        (tmSub Example.lastIndex (compSub shift double))
        (tmSub (app Example.tighten Example.lastIndex) (compSub shift double)) :=
  Family.pair_twice selected witness shift double

theorem substituted_type :
    (((first.sigma second).reindex shift).reindex double).decode =
      fun n => (i : Fin (2 * n + 2)) × Fin (i.val + 1) := rfl

/-- The expected result is independently calculated: double 2, then add 1. -/
example : ((Family.termReindex (Family.termReindex pair shift) double) 2).1.val = 5 := by
  rw [routes_agree]
  rfl

example : ((Family.termReindex (Family.termReindex pair shift) double) 2).2.val = 5 := by
  rw [routes_agree]
  rfl

example : (first.sigma second).reindex shift =
    (first.reindex shift).sigma (second.reindex (lift shift)) :=
  Family.sigma_reindex first second shift

/-- The constructor parameter object retains arbitrary second-family names,
not just a preselected constant tail. -/
example (n : Nat) (f : Fin (n + 1) → second.Parameters) :
    (first.sigma second).Parameters := ⟨n, f⟩

theorem shift_ne_id : shift ≠ idSub := by
  intro h
  have bad : (1 : Nat) = 0 := congrFun h 0
  cases bad

theorem double_ne_id : double ≠ idSub := by
  intro h
  have bad : (2 : Nat) = 1 := congrFun h 1
  cases bad

/-- The very same parameter object serves the product constructor. -/
example : (first.sigma second).Parameters = (first.pi second).Parameters := rfl

def product : (first.pi second).Term := Family.lam (A := first) (B := second) Example.body

theorem product_native : product = Example.tighten :=
  Family.lam_native (A := first) (B := second) Example.body

theorem product_substituted_type :
    (((first.pi second).reindex shift).reindex double).decode =
      fun n => (i : Fin (2 * n + 2)) → Fin (i.val + 1) := rfl

theorem product_formation_twice :
    ((first.pi second).reindex shift).reindex double =
      (first.reindex (compSub shift double)).pi
        (second.reindex (lift (A := first.decode) (compSub shift double))) := by
  rw [Family.reindex_comp]
  exact Family.pi_reindex first second (compSub shift double)

/-- Equality of the entire dependent function, not only its last value. -/
theorem product_routes_agree :
    Family.termReindex (Family.termReindex product shift) double =
      Family.lam (A := first.reindex (compSub shift double))
        (B := second.reindex (lift (A := first.decode) (compSub shift double)))
        (Family.termReindex Example.body (lift (A := first.decode) (compSub shift double))) :=
  Family.lam_twice (A := first) (B := second) Example.body shift double

theorem application_routes_agree :
    Family.termReindex
      (Family.termReindex (Family.app (B := second) product selected) shift) double =
      Family.app (B := second.reindex (lift (A := first.decode) (compSub shift double)))
        (Family.termReindex product (compSub shift double))
        (Family.termReindex selected (compSub shift double)) :=
  Family.app_twice product selected shift double

theorem application_beta : Family.app (B := second) product selected =
    Family.termReindex Example.body (extend idSub selected) :=
  Family.pi_beta (A := first) (B := second) Example.body selected

theorem product_eta (f : (first.pi second).Term) :
    Family.lam (A := first) (B := second) (etaBody (B := second.decode) f) = f :=
  Family.pi_eta_cwf f

/-- At n=2 the domain is Fin 6; every index i returns the last element of Fin(i+1). -/
theorem product_values (i : Fin 6) :
    ((Family.termReindex (Family.termReindex product shift) double) 2 i).val = i.val := by
  rw [product_routes_agree]
  rfl

theorem application_value :
    ((Family.termReindex
      (Family.termReindex (Family.app (B := second) product selected) shift) double) 2).val = 5 := by
  rw [application_routes_agree]
  rfl

example : (first.pi second).reindex shift =
    (first.reindex shift).pi (second.reindex (lift shift)) :=
  Family.pi_reindex first second shift

example (b : (second.reindex (lift (A := first.decode) shift)).Term) :
    (Family.piSections first second shift).symm (Family.piSections first second shift b) = b :=
  Family.piSections_symm_apply first second shift b

example (f : ((first.pi second).reindex shift).Term) :
    Family.piSections first second shift ((Family.piSections first second shift).symm f) = f :=
  Family.piSections_apply_symm first second shift f

example (b : (second.reindex (lift (A := first.decode) shift)).Term) :
    Family.piSections first second (compSub shift double) (Family.termReindex b (lift double)) =
      Family.termReindex (Family.piSections first second shift b) double :=
  Family.piSections_natural first second shift double b

end DependentTail

namespace InputRepresentation

universe u
variable {P Q W V : Type u} (E : P → Type u)

/-- The second names are arbitrary functions, not just constant or canonical names. -/
example (a : W → P) (b : (w : W) → E (a w) → Q) :
    DependentInput.representation E (DependentInput.name E a b) = ⟨a, b⟩ :=
  DependentInput.representation_name E a b

example (n : W → DependentInput.Parameters (Q := Q) E) :
    DependentInput.name E (DependentInput.representation E n).1
      (DependentInput.representation E n).2 = n := DependentInput.name_representation E n

example (a : W → P) (b : (w : W) → E (a w) → Q) (σ : V → W) :
    DependentInput.name E (a ∘ σ) (fun v => b (σ v)) = DependentInput.name E a b ∘ σ :=
  DependentInput.name_natural E a b σ

end InputRepresentation

namespace EmptyFibers

def emptyInput : Family Unit := Family.present (fun _ => Empty)
def emptyOutput : Family emptyInput.Comprehension := Family.present (fun _ => Empty)

/-- Empty-domain products exist even when every output fiber is empty. -/
def emptyProduct : (emptyInput.pi emptyOutput).Term :=
  Family.lam (A := emptyInput) (B := emptyOutput) (fun z => nomatch z.2)

theorem emptyProduct_unique (f : (emptyInput.pi emptyOutput).Term) : f = emptyProduct := by
  funext x a
  exact Empty.elim a

example : Family.lam (A := emptyInput) (B := emptyOutput)
    (etaBody (B := emptyOutput.decode) emptyProduct) = emptyProduct :=
  Family.pi_eta_cwf emptyProduct

def inhabitedInput : Family Unit := Family.present (fun _ => Unit)
def impossibleOutput : Family inhabitedInput.Comprehension := Family.present (fun _ => Empty)

/-- A nonempty input with an empty output admits no product term. -/
theorem no_product : ¬ Nonempty (inhabitedInput.pi impossibleOutput).Term := by
  rintro ⟨f⟩
  exact (Family.app (B := impossibleOutput) f (fun _ => ()) ()).elim

end EmptyFibers

namespace Transport

universe u
variable {A : Type u} (B : A → Type u)

def move {x y : A} (p : x = y) (b : B x) : B y := p ▸ b

theorem move_comp {x y z : A} (p : x = y) (q : y = z) (b : B x) :
    move B q (move B p b) = move B (p.trans q) b := by
  cases p
  cases q
  rfl

structure Inputs where
  x : A
  y : A
  z : A
  p : x = y
  q : y = z
  value : B x

structure First where
  x : A
  z : A
  loop : x = x
  path : x = z
  value : B x

structure Second where
  x : A
  first : x = x
  second : x = x
  value : B x

def substituteFirst (d : First B) : Inputs B :=
  ⟨d.x, d.x, d.z, d.loop, d.path, d.value⟩

def substituteSecond (d : Second B) : First B :=
  ⟨d.x, d.x, d.first, d.second, d.value⟩

def values : Family (Inputs B) := Family.present (fun d => B d.z)

/-- The identity witness is in native equality, explicitly lifted to Type.
It therefore tests the extensional specialization only. -/
def evidence : Family (values B).Comprehension := Family.present
  (fun d => ULift.{u} (PLift (d.2 = move B (d.1.p.trans d.1.q) d.1.value)))

def result : (values B).Term := fun d => move B d.q (move B d.p d.value)

def proof : ((evidence B).reindex (extend idSub (result B))).Term :=
  fun d => ⟨⟨move_comp B d.p d.q d.value⟩⟩

def argument : ((values B).sigma (evidence B)).Term :=
  Family.pair (result B) (proof B)

/-- The memo's transport argument, including its dependent witness, is
evaluated through both Type-family presentations after both substitutions. -/
theorem routes_agree :
    Family.termReindex (Family.termReindex (argument B) (substituteFirst B))
      (substituteSecond B) =
    pairTerm (B := tySub (evidence B).decode
      (lift (compSub (substituteFirst B) (substituteSecond B))))
      (tmSub (result B) (compSub (substituteFirst B) (substituteSecond B)))
      (tmSub (proof B) (compSub (substituteFirst B) (substituteSecond B))) :=
  Family.pair_twice (result B) (proof B) (substituteFirst B) (substituteSecond B)

example (d : Second B) :
    (Family.termReindex (Family.termReindex (argument B) (substituteFirst B))
      (substituteSecond B) d).1 = move B d.second (move B d.first d.value) := by
  rw [routes_agree]
  rfl

end Transport

namespace PresentationFailure

def original : Family Unit := Family.present (fun _ => Nat)
def delayed : Family Bool := original.reindex (fun _ => ())
def fresh : Family Bool := Family.present (fun _ => Nat)

theorem decoded_equal : delayed.decode = fresh.decode := rfl

/-- Decoded equality does not force equality of the local-universe records.
This defeats a proposed annotation-repair shortcut without changing any logic. -/
theorem presentation_ne : delayed ≠ fresh := by
  intro h
  have e : Unit = Bool := congrArg Family.Parameters h
  have : Subsingleton Bool := e ▸ inferInstance
  exact Bool.false_ne_true (Subsingleton.elim _ _)

end PresentationFailure

end Examples.LocalUniverses
