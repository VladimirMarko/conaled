import SquareKit.PartialSpine.Append

/-!
# Flattening arbitrary inner observation ideals

The shared semantic fold uses append's right continuity. Inner ideals are fixed
labels under the outer spine order; they may themselves be partial or infinite.
The fold/concat law reuses strict fold fusion, seed continuity and fold/append.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace SquareKit.PartialSpine.Observations

open Order

universe u v
variable {α : Type u} {B : Type v}

/-- Flatten by semantic right fold; neither outer nor inner ideals need be finite. -/
def concat (xss : Observations (Observations α)) : Observations α :=
  foldr append (Ideal.principal .nil) xss

theorem concat_continuous : ScottContinuous (concat (α := α)) :=
  foldr_continuous append (Ideal.principal .nil) (fun xs => (append_right_continuous xs).monotone)

@[simp] theorem concat_bottom : concat (⊥ : Observations (Observations α)) = ⊥ :=
  foldr_bottom append (Ideal.principal .nil) (fun xs => (append_right_continuous xs).monotone)

@[simp] theorem concat_nil :
    concat (Ideal.principal (.nil : PartialSpine (Observations α))) = Ideal.principal .nil :=
  foldr_nil append (Ideal.principal .nil) (fun xs => (append_right_continuous xs).monotone)

theorem concat_cons (xs : Observations α) (xss : Observations (Observations α)) :
    concat (cons xs xss) = append xs (concat xss) :=
  foldr_cons append (Ideal.principal .nil) (fun ys => (append_right_continuous ys).monotone)
    xs (append_right_continuous xs) xss

/-- An infinite first inner value hides the entire arbitrary outer continuation. -/
theorem concat_infinite_first (σ : Stream' α) (xss : Observations (Observations α)) :
    concat (cons (stream σ) xss) = stream σ := by
  rw [concat_cons, append_stream]

theorem concat_ofList (xss : List (List α)) :
    concat (Ideal.principal (ofList (xss.map fun xs => Ideal.principal (ofList xs)))) =
      Ideal.principal (ofList xss.flatten) := by
  induction xss with
  | nil => exact concat_nil
  | cons xs xss ih =>
    change concat (Ideal.principal (.cons (Ideal.principal (ofList xs))
      (ofList (xss.map fun ys => Ideal.principal (ofList ys))))) = _
    rw [← cons_principal, concat_cons, ih, append_ofList]
    rfl

/-- Continuous inner folds become the outer tail steps, with the proved nil seed. -/
theorem foldr_concat [CompletePartialOrder B] (f : α → B → B) (e : B)
    (continuous : ∀ a, ScottContinuous (f a)) (xss : Observations (Observations α)) :
    foldr f e (concat xss) = foldr (fun xs r => foldr f r xs) e xss := by
  have fused := foldr_fusion append (fun xs r => foldr f r xs) (Ideal.principal .nil)
    (fun xs => (append_right_continuous xs).monotone)
    (fun xs => (foldr_seed_continuous f continuous xs).monotone)
    (foldr f e) (foldr_continuous f e (fun a => (continuous a).monotone))
    (foldr_bottom f e (fun a => (continuous a).monotone))
    (fun xs ys => foldr_append f e continuous xs ys) xss
  rw [foldr_nil f e (fun a => (continuous a).monotone)] at fused
  exact fused

end SquareKit.PartialSpine.Observations
