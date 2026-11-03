import SquareKit.Temporal.Relations
import SquareKit.Relations

namespace Temporal
universe u v w

/-- A batch map lifts the scalar relation without changing order or multiplicity. -/
theorem batch_map {R S : Type u} {R' S' : Type v}
    {E : R → S → Prop} {E' : R' → S' → Prop} (f : R → R') (g : S → S')
    (h : ∀ x y, E x y → E' (f x) (g y)) {xs ys}
    (hs : List.Forall₂ E xs ys) : List.Forall₂ E' (xs.map f) (ys.map g) := by
  induction hs with
  | nil => exact .nil
  | cons he _ ih => exact .cons (h _ _ he) ih

/-- Constant terminal batches allow a direct client with no compiler syntax. -/
def mapBatch {A : Nat → Type u} {R S : Type u} (f : R → S)
    (w : Until A (fun _ => List R) n) : Until A (fun _ => List S) n :=
  w.map (fun _ => id) (fun _ => List.map f)

@[simp] theorem mapBatch_horizon {A : Nat → Type u} {R S : Type u} (f : R → S)
    (w : Until A (fun _ => List R) n) : (mapBatch f w).horizon = w.horizon :=
  Until.horizon_map _ _ _

@[simp] theorem mapBatch_id {A : Nat → Type u} {R : Type u}
    (w : Until A (fun _ => List R) n) : mapBatch id w = w := by
  simp [mapBatch]

theorem mapBatch_comp {A : Nat → Type u} {R S T : Type u} (f : R → S) (g : S → T)
    (w : Until A (fun _ => List R) n) :
    mapBatch g (mapBatch f w) = mapBatch (g ∘ f) w := by
  rw [mapBatch, mapBatch, Until.map_comp]
  simp only [mapBatch, Function.comp_id]
  congr 1
  funext n xs
  exact List.map_map

theorem mapBatch_related {A C : Nat → Type u} {R S : Type u}
    {RA : ∀ n, A n → C n → Prop} {E : R → S → Prop}
    (f : R → R) (g : S → S) (h : ∀ x y, E x y → E (f x) (g y))
    {t : Until A (fun _ => List R) n} {s : Until C (fun _ => List S) n}
    (hs : Until.Rel RA (fun _ => List.Forall₂ E) t s) :
    Until.Rel RA (fun _ => List.Forall₂ E) (mapBatch f t) (mapBatch g s) :=
  hs.map _ _ _ _ (fun _ _ _ h => h) (fun _ _ _ hxy => batch_map f g h hxy)

/-- Package the lift as an ordinary relational square when both carriers share a universe. -/
def batchSquare {A C : Nat → Type u} {R S : Type u}
    (RA : ∀ n, A n → C n → Prop) (E : R → S → Prop)
    (f : R → R) (g : S → S) (h : ∀ x y, E x y → E (f x) (g y)) (n : Nat) :
    Relational.RelSquare
      ⟨Until A (fun _ => List R) n, Until C (fun _ => List S) n,
        Until.Rel RA (fun _ => List.Forall₂ E)⟩
      ⟨Until A (fun _ => List R) n, Until C (fun _ => List S) n,
        Until.Rel RA (fun _ => List.Forall₂ E)⟩ where
  impl := mapBatch f
  spec := mapBatch g
  preserves := mapBatch_related f g h

/-- Pasting the two batch squares requires no source-term induction. -/
theorem batchSquare_comp {A C : Nat → Type u} {R S : Type u}
    (RA : ∀ n, A n → C n → Prop) (E : R → S → Prop)
    (f f' : R → R) (g g' : S → S)
    (h : ∀ x y, E x y → E (f x) (g y))
    (h' : ∀ x y, E x y → E (f' x) (g' y)) (n : Nat) :
    Relational.compose (batchSquare RA E f' g' h' n) (batchSquare RA E f g h n) =
      batchSquare RA E (f' ∘ f) (g' ∘ g) (fun x y e => h' _ _ (h x y e)) n := by
  apply Relational.RelSquare.ext
  · intro t
    exact mapBatch_comp f f' t
  · intro s
    exact mapBatch_comp g g' s

end Temporal
