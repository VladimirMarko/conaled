import SquareKit.DiagonalCoverage
import Examples.RecursiveCompilation

/-! Private pretrial reference validation. Not an author or tool handoff. -/
namespace PrivateReference462
namespace H1
open SquareKit.DiagonalConstruction

def sourceEval (c _ : Bool) : Bool := c
def sourceStep (_ : Bool) : Bool := false
def targetEval (c _ : Option Bool) : Bool := c.getD true
def targetStep (_ : Bool) : Bool := false

def source : Selected sourceEval sourceStep where
  code := false
  represents _ := rfl

def changeCodes : Map sourceEval sourceStep targetEval targetStep where
  code := some
  value := id
  evaluation _ _ := rfl
  step _ := rfl

theorem not_onto : ¬ Function.Surjective changeCodes.code := by
  intro h
  obtain ⟨c, hc⟩ := h none
  cases hc

/-- Rows vary with code, but each individual row is input-constant. -/
theorem rows_differ (input : Option Bool) :
    targetEval (some false) input ≠ targetEval (some true) input := by
  change false ≠ true
  decide

theorem rows_constant (code a b : Option Bool) : targetEval code a = targetEval code b := rfl

theorem extension : changeCodes.Extension source := by
  intro b _
  rfl

def full : Selected targetEval targetStep := changeCodes.selectedExtension source extension

theorem selected_code : full.code = some false := rfl

theorem selected_value : full.witness = false :=
  changeCodes.extension_witness source extension

theorem full_representation (b : Option Bool) :
    targetEval full.code b = diagonal targetEval targetStep b := full.represents b

theorem omitted_input : targetEval full.code none = false := full_representation none

def restricted := changeCodes.selectedImage source

theorem restricted_code : restricted.code.val = full.code := rfl

theorem restricted_value : restricted.witness = full.witness := rfl

theorem restricted_representation (b : {b // ∃ a, changeCodes.code a = b}) :
    targetEval restricted.code.val b.val = diagonal targetEval targetStep b.val :=
  restricted.represents b

theorem restricted_excludes_none : ¬ ∃ b : {b // ∃ a, changeCodes.code a = b}, b.val = none := by
  rintro ⟨⟨b, a, ha⟩, hb⟩
  have h := ha.trans hb
  cases h

/-- A false proposal is refuted at representation, independently of map laws. -/
theorem wrong_source_code : ¬ (∀ a, sourceEval true a = diagonal sourceEval sourceStep a) := by
  intro h
  have bad := h false
  cases bad

theorem no_selected_true : ¬ ∃ s : Selected sourceEval sourceStep, s.code = true := by
  rintro ⟨s, hs⟩
  apply wrong_source_code
  simpa [hs] using s.represents

end H1
namespace H2
open FirstOrderCompiler Examples.RecursiveCompilation

def productCost : Nat →+ Nat × Nat where
  toFun n := (n, 2*n)
  map_zero' := rfl
  map_add' n m := by
    apply Prod.ext
    · rfl
    · exact Nat.mul_add 2 n m

def finalCost : Nat × Nat →+ Nat where
  toFun p := p.1 + 3*p.2
  map_zero' := rfl
  map_add' p q := by
    change (p.1+q.1)+3*(p.2+q.2) = (p.1+3*p.2)+(q.1+3*q.2)
    omega

def compiledSeed : Resources.Measured Int Nat :=
  FirstOrderCompiler.compile counted.scalar seed ()

def transition (x acc : Int) : Resources.Measured Int Nat :=
  let r := FirstOrderCompiler.compile counted.scalar addBody (((),acc),x)
  (r.1,1+r.2)

theorem seed_observed : compiledSeed = (0,1) := rfl

theorem transition_observed (x acc : Int) : transition x acc = (acc+x,2) := rfl

/-- The source execution relation counts actual visited cells. -/
theorem native_execution (xs : List Int) :
    ListFoldCompiler.Executes meaning addBody xs 0
      (ListFoldCompiler.iterate meaning addBody 0 xs) xs.length :=
  ListFoldCompiler.iterate_executes _ _ _ _

theorem native_execution_sum (xs : List Int) :
    ListFoldCompiler.Executes meaning addBody xs 0 xs.sum xs.length := by
  have hs : ListFoldCompiler.iterate meaning addBody 0 xs = xs.sum := total_meaning xs
  rw [← hs]
  exact native_execution xs

theorem native_counted (xs : List Int) :
    ListFoldCompiler.compile counted total xs = (xs.sum, 1+2*xs.length) := total_counted xs

theorem native_ordinary (xs : List Int) :
    ListFoldCompiler.compile ordinary total xs = xs.sum := total_compiled xs

theorem erasure_before_reweight (xs : List Int) :
    (ListFoldCompiler.compile counted total xs).1 = ListFoldCompiler.compile ordinary total xs := by
  rw [native_counted, native_ordinary]

/-- Observation codomain is arbitrary: the product is an actual executor output. -/
theorem transport_execution {C : Type*} [AddMonoid C] (h : Nat →+ C) (xs : List Int) :
    Resources.reweight h (ListFoldCompiler.compile counted total xs) =
      Resources.bind (Resources.reweight h compiledSeed)
        (fun s => Resources.run (fun x acc => Resources.reweight h (transition x acc)) xs s) := by
  change Resources.reweight h (Resources.bind compiledSeed (fun s => Resources.run transition xs s)) = _
  rw [Resources.reweight_bind]
  congr 1
  funext s
  exact Resources.reweight_run h transition xs s

def productExecution (xs : List Int) : Resources.Measured Int (Nat × Nat) :=
  Resources.bind (Resources.reweight productCost compiledSeed)
    (fun s => Resources.run (fun x acc => Resources.reweight productCost (transition x acc)) xs s)

def finalExecution (xs : List Int) : Resources.Measured Int Nat :=
  Resources.bind (Resources.reweight finalCost (Resources.reweight productCost compiledSeed))
    (fun s => Resources.run
      (fun x acc => Resources.reweight finalCost (Resources.reweight productCost (transition x acc))) xs s)

theorem product_transport (xs : List Int) :
    Resources.reweight productCost (ListFoldCompiler.compile counted total xs) = productExecution xs :=
  transport_execution productCost xs

theorem second_transport (xs : List Int) :
    Resources.reweight finalCost (productExecution xs) = finalExecution xs := by
  unfold productExecution finalExecution
  rw [Resources.reweight_bind]
  congr 1
  funext s
  exact Resources.reweight_run finalCost _ xs s

theorem composed_execution (xs : List Int) :
    Resources.reweight (finalCost.comp productCost)
      (ListFoldCompiler.compile counted total xs) = finalExecution xs := by
  change Resources.reweight finalCost
    (Resources.reweight productCost (ListFoldCompiler.compile counted total xs)) = _
  rw [product_transport, second_transport]

theorem product_observation (xs : List Int) :
    productExecution xs = (xs.sum, (1+2*xs.length, 2*(1+2*xs.length))) := by
  rw [← product_transport, native_counted]
  rfl

theorem final_observation (xs : List Int) :
    finalExecution xs = (xs.sum, 7*(1+2*xs.length)) := by
  rw [← second_transport, product_observation]
  apply Prod.ext
  · rfl
  · change (1+2*xs.length)+3*(2*(1+2*xs.length)) = 7*(1+2*xs.length)
    omega

theorem composed_observation (xs : List Int) :
    Resources.reweight (finalCost.comp productCost)
      (ListFoldCompiler.compile counted total xs) = (xs.sum, 7*(1+2*xs.length)) :=
  (composed_execution xs).trans (final_observation xs)

theorem observed_empty : finalExecution [] = (0,7) := final_observation []
theorem observed_two : finalExecution [1,2] = (3,35) := final_observation [1,2]

/-- Shift remains a function, but cannot provide additive-map evidence. -/
def shifted (n : Nat) := n+1

theorem shifted_zero_rejected : shifted 0 ≠ 0 := by decide

theorem no_shifted_additive : ¬ ∃ h : Nat →+ Nat, ∀ n, h n = shifted n := by
  rintro ⟨h, hh⟩
  have hz := hh 0
  rw [map_zero] at hz
  exact shifted_zero_rejected hz.symm

theorem shifted_still_defined : Resources.reweight shifted ((0 : Int),0) = (0,1) := rfl

end H2
end PrivateReference462
