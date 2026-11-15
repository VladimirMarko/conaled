import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Quasi-Borel values

Experimental value model for #370, following Heunen–Kammar–Staton–Yang,
arXiv:1701.02547v4, Definitions 7/11 and Propositions 14/18.
Countable measurable selection presents the countable partition axiom.
This module constructs products and exponentials, not the probability monad.
-/

open MeasureTheory

namespace Applications.Probability.QuasiBorel

structure Space where
  Carrier : Type
  random : (ℝ → Carrier) → Prop
  constant : ∀ x, random (fun _ => x)
  reparam : ∀ {a}, random a → ∀ {r : ℝ → ℝ}, Measurable r → random (a ∘ r)
  select : ∀ {a : ℕ → ℝ → Carrier}, (∀ n, random (a n)) →
    ∀ {i : ℝ → ℕ}, Measurable i → random (fun r => a (i r) r)

instance : CoeSort Space Type := ⟨Space.Carrier⟩

structure Hom (X Y : Space) where
  toFun : X → Y
  preserves : ∀ {a}, X.random a → Y.random (toFun ∘ a)

instance {X Y : Space} : CoeFun (Hom X Y) (fun _ => X → Y) := ⟨Hom.toFun⟩

@[ext] theorem Hom.ext {X Y : Space} {f g : Hom X Y} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g
  simp_all only [mk.injEq]
  exact funext h

def Hom.id (X : Space) : Hom X X := ⟨fun x => x, fun h => h⟩
def Hom.comp {X Y Z : Space} (g : Hom Y Z) (f : Hom X Y) : Hom X Z :=
  ⟨g ∘ f, fun h => g.preserves (f.preserves h)⟩

abbrev ofMeasurable (A : Type) [MeasurableSpace A] : Space where
  Carrier := A
  random := Measurable
  constant _ := measurable_const
  reparam {_a} ha {_r} hr := ha.comp hr
  select {a} ha {_i} hi := by
    exact (measurable_from_prod_countable_right (f := fun p : ℕ × ℝ => a p.1 p.2) fun n => ha n).comp
      (hi.prodMk measurable_id)

def measurableHom {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (f : A → B) (hf : Measurable f) : Hom (ofMeasurable A) (ofMeasurable B) :=
  ⟨f, fun ha => hf.comp ha⟩

abbrev prod (X Y : Space) : Space where
  Carrier := X × Y
  random a := X.random (fun r => (a r).1) ∧ Y.random (fun r => (a r).2)
  constant p := ⟨X.constant p.1, Y.constant p.2⟩
  reparam {_a} ha {_r} hr := ⟨X.reparam ha.1 hr, Y.reparam ha.2 hr⟩
  select {_a} ha {_i} hi := ⟨X.select (fun n => (ha n).1) hi, Y.select (fun n => (ha n).2) hi⟩

def fst (X Y : Space) : Hom (prod X Y) X := ⟨Prod.fst, fun h => h.1⟩
def snd (X Y : Space) : Hom (prod X Y) Y := ⟨Prod.snd, fun h => h.2⟩
def pair {W X Y : Space} (f : Hom W X) (g : Hom W Y) : Hom W (prod X Y) :=
  ⟨fun w => (f w, g w), fun h => ⟨f.preserves h, g.preserves h⟩⟩

/-- The exponential condition tests joint randomness, including reparameterizations. -/
abbrev exp (X Y : Space) : Space where
  Carrier := Hom X Y
  random a := ∀ (r : ℝ → ℝ), Measurable r → ∀ b, X.random b →
    Y.random (fun t => a (r t) (b t))
  constant f := fun _ _ _ hb => f.preserves hb
  reparam {_a} ha {_s} hs := fun r hr b hb => ha (_ ∘ r) (hs.comp hr) b hb
  select {_a} ha {_i} hi := fun r hr b hb =>
    Y.select (fun n => ha n r hr b hb) (hi.comp hr)

def eval (X Y : Space) : Hom (prod (exp X Y) X) Y :=
  ⟨fun p => p.1 p.2, fun h => h.1 id measurable_id _ h.2⟩

def curry {W X Y : Space} (f : Hom (prod W X) Y) : Hom W (exp X Y) where
  toFun w := ⟨fun x => f (w, x), fun hb => f.preserves ⟨W.constant w, hb⟩⟩
  preserves ha := fun _r hr _b hb => f.preserves ⟨W.reparam ha hr, hb⟩

def uncurry {W X Y : Space} (f : Hom W (exp X Y)) : Hom (prod W X) Y :=
  (eval X Y).comp (pair (f.comp (fst W X)) (snd W X))

@[simp] theorem curry_apply {W X Y : Space} (f : Hom (prod W X) Y) (w : W) (x : X) :
    curry f w x = f (w, x) := rfl

@[simp] theorem uncurry_curry {W X Y : Space} (f : Hom (prod W X) Y) :
    uncurry (curry f) = f := by ext p; rfl

@[simp] theorem curry_uncurry {W X Y : Space} (f : Hom W (exp X Y)) :
    curry (uncurry f) = f := by ext w x; rfl

/-- The measurable sets tested by all real random elements. This is not asserted
    to preserve products. -/
abbrev sigma (X : Space) : MeasurableSpace X where
  MeasurableSet' s := ∀ a, X.random a → MeasurableSet (a ⁻¹' s)
  measurableSet_empty := by intro a ha; simp
  measurableSet_compl := by intro s hs a ha; exact (hs a ha).compl
  measurableSet_iUnion := by
    intro s hs a ha
    simpa only [Set.preimage_iUnion] using MeasurableSet.iUnion (fun n => hs n a ha)

theorem random_measurable {X : Space} {a : ℝ → X} (ha : X.random a) :
    @Measurable _ _ inferInstance (sigma X) a := fun _ hs => hs a ha

theorem Hom.measurable {X Y : Space} (f : Hom X Y) :
    @Measurable _ _ (sigma X) (sigma Y) f := fun _ hs a ha => hs (f ∘ a) (f.preserves ha)

/-- A standard Borel source recovers ordinary measurability, using a measurable
    real embedding and its measurable retraction. -/
theorem Hom.measurable_source {A : Type} [MeasurableSpace A] [StandardBorelSpace A]
    {Y : Space} (f : Hom (ofMeasurable A) Y) :
    @Measurable _ _ inferInstance (sigma Y) f := by
  cases isEmpty_or_nonempty A with
  | inl h =>
    let : MeasurableSpace Y := sigma Y
    exact measurable_of_finite _
  | inr h =>
    let e := measurableEmbedding_embeddingReal A
    have hm := random_measurable (f.preserves e.measurable_invFun)
    have he := hm.comp e.measurable
    convert he using 1
    funext a
    exact congrArg f (e.leftInverse_invFun a).symm

/-- An admitted observer into a measurable space is measurable for the generated sigma algebra. -/
theorem Hom.measurable_observer {X : Space} {A : Type} [MeasurableSpace A]
    (f : Hom X (ofMeasurable A)) : @Measurable _ _ (sigma X) inferInstance f := by
  intro s hs a ha
  exact (f.preserves ha) hs

end Applications.Probability.QuasiBorel
