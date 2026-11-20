import Mathlib.Data.List.Chain
import Mathlib.Data.List.Sort
import Mathlib.Data.Quot

/-!
# Related membership and canonical sorted lists

Related membership forgets multiplicity and positions; `List.Forall₂` retains
positions. A compatible strict order connects them on sorted lists. The proof
passes through quotient equality and Mathlib's canonical-list uniqueness law;
neither totality nor decidable equality is an assumption.

The source-facing meanings of InA, equivlistA, eqlistA and Sorted are documented
in `docs/research/vfa-color.md`, with Rocq Stdlib attribution in
`docs/research/rocq-stdlib-notice.md`. The proofs here reuse the Lean interfaces.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.RelatedMembership

universe u v

variable {α : Type u} {β : Type v} {R S : α → α → Prop}

/-- Some actual member of the list is related to the query. -/
def RelatedMem (R : α → α → Prop) (query : α) (xs : List α) : Prop :=
  ∃ value ∈ xs, R query value

/-- Equality of related membership, without a multiplicity or order claim. -/
def SameRelatedMembers (R : α → α → Prop) (xs ys : List α) : Prop :=
  ∀ query, RelatedMem R query xs ↔ RelatedMem R query ys

@[simp] theorem relatedMem_nil (query : α) : RelatedMem R query [] ↔ False := by
  simp [RelatedMem]

@[simp] theorem relatedMem_cons (query head : α) (tail : List α) :
    RelatedMem R query (head :: tail) ↔ R query head ∨ RelatedMem R query tail := by
  simp [RelatedMem, or_and_right, exists_or]

@[simp] theorem relatedMem_eq (query : α) (xs : List α) :
    RelatedMem Eq query xs ↔ query ∈ xs := by
  simp [RelatedMem]

theorem sameRelatedMembers_eq (xs ys : List α) :
    SameRelatedMembers Eq xs ys ↔ ∀ query, query ∈ xs ↔ query ∈ ys := by
  simp only [SameRelatedMembers, relatedMem_eq]

theorem eq_predicate_congr (f : α → Bool) {a b : α} (same : a = b) : f a = f b :=
  congrArg f same

/-- Congruence is needed to state the filter test at the query, not only at its witness. -/
theorem relatedMem_filter (f : α → Bool)
    (compatible : ∀ {a b}, R a b → f a = f b) (query : α) (xs : List α) :
    RelatedMem R query (xs.filter f) ↔ RelatedMem R query xs ∧ f query = true := by
  constructor
  · rintro ⟨value, present, related⟩
    obtain ⟨present, accepted⟩ := List.mem_filter.mp present
    exact ⟨⟨value, present, related⟩, (compatible related).trans accepted⟩
  · rintro ⟨⟨value, present, related⟩, accepted⟩
    exact ⟨value, List.mem_filter.mpr
      ⟨present, (compatible related).symm.trans accepted⟩, related⟩

theorem relatedMem_filter_eq (f : α → Bool) (query : α) (xs : List α) :
    RelatedMem Eq query (xs.filter f) ↔ RelatedMem Eq query xs ∧ f query = true :=
  relatedMem_filter f (eq_predicate_congr f) query xs

/-- Source Sorted is adjacent sortedness; transitivity supplies the all-pairs form. -/
theorem isChain_iff_pairwise_of_trans
    (transitive : ∀ {a b c}, S a b → S b c → S a c) (xs : List α) :
    xs.IsChain S ↔ xs.Pairwise S := by
  let : Trans S S S := ⟨transitive⟩
  exact List.isChain_iff_pairwise

theorem isChain_filter_of_trans
    (transitive : ∀ {a b c}, S a b → S b c → S a c)
    (f : α → Bool) {xs : List α} (sorted : xs.IsChain S) :
    (xs.filter f).IsChain S :=
  (((isChain_iff_pairwise_of_trans (S := S) transitive xs).mp sorted).filter f).isChain

theorem quotient_mk_mem_map (s : Setoid α) (query : α) (xs : List α) :
    Quotient.mk s query ∈ xs.map (Quotient.mk s) ↔ RelatedMem s.r query xs := by
  rw [List.mem_map]
  constructor
  · rintro ⟨value, present, same⟩
    exact ⟨value, present, s.iseqv.symm (Quotient.exact same)⟩
  · rintro ⟨value, present, related⟩
    exact ⟨value, present, Quotient.sound (s.iseqv.symm related)⟩

/-- Sorted lists with the same equivalence classes are pointwise related.
No totality or payload comparison is needed. -/
theorem forall₂_of_isChain_of_sameRelatedMembers
    (equivalence : Equivalence R)
    (irrefl : ∀ a, ¬ S a a)
    (transitive : ∀ {a b c}, S a b → S b c → S a c)
    (compatible : ∀ {a a' b b'}, R a a' → R b b' → (S a b ↔ S a' b'))
    {xs ys : List α} (sortedXs : xs.IsChain S) (sortedYs : ys.IsChain S)
    (sameMembers : SameRelatedMembers R xs ys) : List.Forall₂ R xs ys := by
  let s : Setoid α := ⟨R, equivalence⟩
  let qS : Quotient s → Quotient s → Prop :=
    Quotient.lift₂ S (fun _ _ _ _ left right => propext (compatible left right))
  let : Std.Irrefl qS :=
    ⟨fun value => Quotient.inductionOn value (fun representative => irrefl representative)⟩
  let : Std.Antisymm qS :=
    ⟨fun left right => Quotient.inductionOn₂ left right
      (fun a _ hab hba => (irrefl a (transitive hab hba)).elim)⟩
  have pairwiseXs := (isChain_iff_pairwise_of_trans (S := S) transitive xs).mp sortedXs
  have pairwiseYs := (isChain_iff_pairwise_of_trans (S := S) transitive ys).mp sortedYs
  have quotientXs : (xs.map (Quotient.mk s)).Pairwise qS :=
    pairwiseXs.map _ (fun _ _ h => h)
  have quotientYs : (ys.map (Quotient.mk s)).Pairwise qS :=
    pairwiseYs.map _ (fun _ _ h => h)
  have quotientMembers : ∀ value : Quotient s,
      value ∈ xs.map (Quotient.mk s) ↔ value ∈ ys.map (Quotient.mk s) := by
    intro value
    refine Quotient.inductionOn value ?_
    intro representative
    rw [quotient_mk_mem_map, quotient_mk_mem_map]
    exact sameMembers representative
  have sameLists := quotientXs.eq_of_mem_iff quotientYs quotientMembers
  have relatedQuotients : List.Forall₂ Eq
      (xs.map (Quotient.mk s)) (ys.map (Quotient.mk s)) := by
    simpa only [List.forall₂_eq_eq_eq] using sameLists
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff] at relatedQuotients
  exact relatedQuotients.imp (fun _ _ same => Quotient.exact same)

theorem forall₂_eq_iff (xs ys : List α) : List.Forall₂ Eq xs ys ↔ xs = ys := by
  rw [List.forall₂_eq_eq_eq]

/-- Projection exposes an existential payload witness even when keys repeat. -/
theorem relatedMem_map_fst (query : α) (xs : List (α × β)) :
    RelatedMem Eq query (xs.map Prod.fst) ↔
      ∃ value, RelatedMem Eq (query, value) xs := by
  simp only [relatedMem_eq, List.mem_map]
  constructor
  · rintro ⟨⟨key, value⟩, present, same⟩
    dsimp at same
    subst key
    exact ⟨value, present⟩
  · rintro ⟨value, present⟩
    exact ⟨(query, value), present, rfl⟩

theorem isChain_map_fst (order : α → α → Prop) (xs : List (α × β)) :
    xs.IsChain (fun a b => order a.1 b.1) ↔ (xs.map Prod.fst).IsChain order :=
  (List.isChain_map Prod.fst).symm

end Sequences.RelatedMembership
