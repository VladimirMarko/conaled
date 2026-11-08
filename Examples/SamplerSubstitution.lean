import Applications.Probability.SamplerClient
import Applications.Probability.SamplerSubstitution

/-! Higher-order sampler replacement against the frozen Boolean joint law. -/
open MeasureTheory
namespace Examples.SamplerSubstitution
open Applications.Probability
open QuasiBorel SamplerClient

abbrev bit := ofMeasurable Bool
abbrev functions := exp bit bit

def xorHom : Hom (prod bit bit) bit where
  toFun p := function p.1 p.2
  preserves h := (measurable_of_countable (fun p : Bool × Bool => function p.1 p.2)).comp
    (h.1.prodMk h.2)

def sampled : Hom bit functions := curry xorHom

def complement : Hom bit bit := measurableHom Bool.not (measurable_of_countable _)
def recoded : Hom bit functions := sampled.comp complement
def recodedTwice : Hom bit functions := recoded.comp complement

def query : Hom (prod functions bit) bit := eval bit bit

def next : Hom (prod (prod functions bit) bit) bit :=
  xorHom.comp
    (pair ((snd functions bit).comp (fst (prod functions bit) bit))
      (snd (prod functions bit) bit))

def readPair : Hom (prod functions bit) (ofMeasurable (Bool × Bool)) where
  toFun p := (p.1 false, p.2)
  preserves h := (h.1 id measurable_id _ measurable_const).prodMk h.2

def readTriple : Hom (prod (prod functions bit) bit) (ofMeasurable (Bool × Bool × Bool)) where
  toFun p := (p.1.1 false, p.1.2, p.2)
  preserves h := (h.1.1 id measurable_id _ measurable_const).prodMk (h.1.2.prodMk h.2)

theorem first_replacement : law fair sampled = law fair recoded := by
  let : MeasurableSpace functions := sigma functions
  change fair.map sampled = fair.map (sampled ∘ Bool.not)
  rw [← Measure.map_map sampled.measurable_source (measurable_of_countable _), fair_not]

theorem second_replacement : law fair recoded = law fair recodedTwice := by
  let : MeasurableSpace functions := sigma functions
  change fair.map recoded = fair.map (recoded ∘ Bool.not)
  rw [← Measure.map_map recoded.measurable_source (measurable_of_countable _), fair_not]

theorem retained_replacement :
    law (fair.prod fair) (seeded sampled (retain query)) =
      law (fair.prod fair) (seeded recoded (retain query)) :=
  retained_law_substitution fair fair fair sampled recoded query first_replacement

theorem twice_replaced :
    law ((fair.prod fair).prod fair) (retainedTwo sampled query next) =
      law ((fair.prod fair).prod fair) (retainedTwo recodedTwice query next) :=
  (two_stage_substitution fair fair fair fair sampled recoded query next first_replacement).trans
    (two_stage_substitution fair fair fair fair recoded recodedTwice query next second_replacement)

theorem observed_pair :
    @Measure.map (prod functions bit) (Bool × Bool) (sigma (prod functions bit)) _ readPair
      (law (fair.prod fair) (seeded sampled (retain query))) = fair.prod fair := by
  rw [law_observe]
  change (fair.prod fair).map (fun p => (function p.1 false, function p.1 p.2)) = _
  simpa only [function_false] using native_pair

theorem kernel_agreement :
    @Measure.map (prod functions bit) (Bool × Bool) (sigma (prod functions bit)) _ readPair
      (law (fair.prod fair) (seeded sampled (retain query))) = fair.compProd transition :=
  observed_pair.trans kernel_pair.symm

/-- Same-seed values differ despite the checked equality of their laws. -/
example : sampled false ≠ recoded false := by
  intro h
  have h0 := congrArg (fun f : functions => f false) h
  contradiction

/-- The explicit seed coupling aligns whole functions, not merely their laws. -/
theorem coupled (b : Bool) : sampled b = recoded (!b) := by
  cases b <;> rfl

theorem coupled_selected (b t u : Bool) :
    retainedTwo sampled query next ((b,t),u) =
      retainedTwo recoded query next ((!b,t),u) := by
  cases b <;> cases t <;> cases u <;> rfl


theorem observed_three :
    @Measure.map (prod (prod functions bit) bit) (Bool × Bool × Bool)
      (sigma (prod (prod functions bit) bit)) _ readTriple
      (law ((fair.prod fair).prod fair) (retainedTwo sampled query next)) = tripleMeaning := by
  rw [law_observe]
  change ((fair.prod fair).prod fair).map
    (fun p => (function p.1.1 false, function p.1.1 p.1.2,
      function (function p.1.1 p.1.2) p.2)) = _
  simpa only [function_false] using native_three

theorem two_kernel_agreement :
    @Measure.map (prod (prod functions bit) bit) (Bool × Bool × Bool)
      (sigma (prod (prod functions bit) bit)) _ readTriple
      (law ((fair.prod fair).prod fair) (retainedTwo recodedTwice query next)) =
    ((fair.compProd transition).compProd secondTransition).map
      (fun p => (p.1.1,p.1.2,p.2)) := by
  rw [← twice_replaced]
  exact observed_three.trans kernel_three.symm

/-- Deterministic function observation does not need a probability object. -/
def atFalse : Hom functions bit where
  toFun f := f false
  preserves h := h id measurable_id _ measurable_const

example : law (fair.prod fair) (seeded sampled
    (atFalse.comp (fst functions bit))) = law fair (atFalse.comp sampled) :=
  seeded_deterministic fair fair sampled atFalse

/-- Realization records retain all three selected seeds as data. -/
def record (a : Hom bit functions) (b t u : Bool) :=
  (((b,t),u), retainedTwo a query next ((b,t),u))

theorem record_seeds (a : Hom bit functions) (b t u : Bool) :
    (record a b t u).1 = ((b,t),u) := rfl

theorem record_coupling (b t u : Bool) :
    (record sampled b t u).2 = (record recoded (!b) t u).2 := coupled_selected b t u

example : (record sampled false true true).1 ≠ (record recoded true true true).1 := by decide

example : copied.map Prod.snd = (fair.prod fair).map Prod.snd :=
  copied_marginals.2.trans fresh_marginals.2.symm
example : copied ≠ fair.prod fair := copied_not_fresh
example : fair.map (fun b => function b b) ≠ fair := reused_seed_wrong


/-- The selected QBS run recovers the independently frozen native record. -/
theorem selected_agreement (b t u : Bool) :
    (b,t,(record sampled b t u).2.1.2,(record sampled b t u).2.2) = selected b t u := rfl

example :
    @Measure.map (prod functions bit) (Bool × Bool) (sigma (prod functions bit)) _ readPair
      (law (fair.prod fair) (seeded sampled (retain query))) = pairMeaning :=
  observed_pair.trans pair_meaning

end Examples.SamplerSubstitution
