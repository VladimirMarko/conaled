import SquareKit.InteractionContracts

/-!
# Finite event scripts and relational handlers

A bounded interface experiment, not a general effect language. Scripts cannot
branch on replies or express interruption inside a handler. Handler relations
must retain any partial effects they claim to model. Empty relations do not
mean rollback, and safety alone does not establish execution or progress.
-/
namespace Interaction.Events
universe u v w

/-- Events need not be enumerable; mathematical handlers need not be executable. -/
def interpret {E : Type u} {S : Type v} (handle : E → S → S → Prop) :
    List E → S → S → Prop
  | [], s, t => s = t
  | e :: es, s, t => Relation.Comp (handle e) (interpret handle es) s t

theorem interpret_append {E : Type u} {S : Type v} (h : E → S → S → Prop)
    (xs ys : List E) :
    interpret h (xs ++ ys) = Relation.Comp (interpret h xs) (interpret h ys) := by
  funext s t
  apply propext
  induction xs generalizing s with
  | nil => simp [interpret, Relation.Comp]
  | cons e es ih =>
    simp only [List.cons_append, interpret, Relation.Comp]
    constructor
    · rintro ⟨a, hea, rest⟩
      obtain ⟨b, hab, hbt⟩ := (ih a).mp rest
      exact ⟨b, ⟨a, hea, hab⟩, hbt⟩
    · rintro ⟨b, ⟨a, hea, hab⟩, hbt⟩
      exact ⟨a, hea, (ih a).mpr ⟨b, hab, hbt⟩⟩

/-- Prove each event's simulation once; the interpreter supplies sequence
bookkeeping for arbitrary scripts. This is not a premise that the entire
script already refines its specification. -/
theorem interpret_simulation {E : Type u} {C : Type v} {A : Type w}
    (concrete : E → C → C → Prop) (abstract : E → A → A → Prop)
    (related : C → A → Prop)
    (primitive : ∀ e c c' a, related c a → concrete e c c' →
      ∃ a', abstract e a a' ∧ related c' a')
    (script : List E) {c c' a} (initial : related c a)
    (run : interpret concrete script c c') :
    ∃ a', interpret abstract script a a' ∧ related c' a' := by
  induction script generalizing c a with
  | nil =>
    have eq : c = c' := run
    exact ⟨a, rfl, eq ▸ initial⟩
  | cons e es ih =>
    obtain ⟨m, first, rest⟩ := run
    obtain ⟨b, step, rel⟩ := primitive e c m a initial first
    obtain ⟨a', tail, rel'⟩ := ih rel rest
    exact ⟨a', ⟨b, step, tail⟩, rel'⟩

/-- Derived safety transfer used by a caller after proving a source contract. -/
theorem interpret_safe {E : Type u} {S : Type v}
    {concrete abstract : E → S → S → Prop}
    (primitive : ∀ e s t, concrete e s t → abstract e s t)
    {script : List E} {P Q : S → Prop}
    (source : Safe P (interpret abstract script) Q) :
    Safe P (interpret concrete script) Q := by
  intro s t hs run
  obtain ⟨a, ha, eq⟩ := interpret_simulation concrete abstract Eq
    (fun e c c' a h step => by subst a; exact ⟨c', primitive e c c' step, rfl⟩)
    script rfl run
  subst a
  exact source hs ha

/-- A primitive invariant lifts to any finite script without caller induction. -/
theorem interpret_invariant {E : Type u} {S : Type v} {h : E → S → S → Prop}
    {P : S → Prop} (preserves : ∀ e, Stable (h e) P) (script : List E) :
    Safe P (interpret h script) P := by
  intro s t hs run
  induction script generalizing s with
  | nil => exact run ▸ hs
  | cons e es ih =>
    obtain ⟨a, first, rest⟩ := run
    exact ih (preserves e hs first) rest
end Interaction.Events
