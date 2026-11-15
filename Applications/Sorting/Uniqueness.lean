import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Defs

/-! Ordinary sorting functions are determined by pairwise order and occurrences.
The relation needs only antisymmetry once both outputs satisfy the contract.
This adds function-level consequences of the existing list uniqueness theorem,
without introducing another sorting operation or specification carrier.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting

universe u
variable {α : Type u}

/-- Correctness at this input determines the result, even when the relation
does not admit a sorting function on every possible input. -/
theorem sorters_eq_at (r : α → α → Prop) [Std.Antisymm r]
    (f g : List α → List α) (xs : List α)
    (hf : (f xs).Pairwise r ∧ (f xs).Perm xs)
    (hg : (g xs).Pairwise r ∧ (g xs).Perm xs) : f xs = g xs :=
  List.Perm.eq_of_pairwise' (r := r) hf.1 hg.1 (hf.2.trans hg.2.symm)

/-- Any two functions satisfying ordinary sorting correctness at every input
are equal as functions. Stability and execution costs are separate observations. -/
theorem sorters_eq (r : α → α → Prop) [Std.Antisymm r]
    (f g : List α → List α)
    (hf : ∀ xs, (f xs).Pairwise r ∧ (f xs).Perm xs)
    (hg : ∀ xs, (g xs).Pairwise r ∧ (g xs).Perm xs) : f = g :=
  funext fun xs => sorters_eq_at r f g xs (hf xs) (hg xs)

/-- The source's multiset formulation has exactly the same occurrence meaning.
Applying the resulting function equality to an input gives its pointwise form. -/
theorem sorters_eq_of_multiset (r : α → α → Prop) [Std.Antisymm r]
    (f g : List α → List α)
    (hf : ∀ xs, (f xs).Pairwise r ∧ (f xs : Multiset α) = (xs : Multiset α))
    (hg : ∀ xs, (g xs).Pairwise r ∧ (g xs : Multiset α) = (xs : Multiset α)) :
    f = g :=
  sorters_eq r f g
    (fun xs => ⟨(hf xs).1, Multiset.coe_eq_coe.mp (hf xs).2⟩)
    (fun xs => ⟨(hg xs).1, Multiset.coe_eq_coe.mp (hg xs).2⟩)

end Applications.Sorting
