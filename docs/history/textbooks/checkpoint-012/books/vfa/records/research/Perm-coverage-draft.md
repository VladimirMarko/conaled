# Perm source correspondence — implementation preparation

**Status: draft mapping only; no chapter acceptance.** The formal build,
exhaustive proof audit, and independent Standards and Spec reviews are pending.
This preparation belongs to the existing implementation loop and is not an
independent final Spec review.

## Reference and inspected code

- VFA version 2.1, `Perm.v`, SHA-256
  `0d3ad2421a6bee80b987423b702e8688e59fe802cafa1efa9b98df71d619fd9f`.
- Primary reference: <https://softwarefoundations.cis.upenn.edu/vfa-current/Perm.html>.
- Source inventory: `source/Perm.inventory.json`.
- `Applications/Sorting/FirstPair.lean`, inspected SHA-256
  `8e253f1468a74c73e89bf8f52f9b98176fe0602e50aa5e64c4676b95128787a0`.
- `Examples/ComparisonPermutations.lean`, inspected SHA-256
  `3f4d1294d84e3840a690c1b9c876ced2d37692b9418dd16e4295425333cab57e`.

In the tables, **S** abbreviates namespace `Applications.Sorting` and **E**
abbreviates `Examples.ComparisonPermutations`. Source IDs are the stable
name-plus-line IDs in the inventory. "Mapped" means that the written Lean
statement and inspected proof appear to cover the source obligation; it does
not mean the compiler or audit has accepted the file.

## All thirty explicit source records

| Source inventory ID | Lean declaration or explicit adaptation | Preparation assessment |
|---|---|---|
| `Perm.geb@72` | `E.geb n m := decide (m ≤ n)` | Mapped. Same reversed non-strict natural-number comparison as the source. |
| `Perm.gtb@76` | `E.gtb n m := decide (m < n)` | Mapped. Same reversed strict comparison; argument orientation is retained. |
| `Perm.lia_example1@86` | `E.lia_example1`; explain the failed source proof through `E.truncated_subtraction` | The source attempt is aborted, then proved at line 124. No extra theorem is needed for the failed proof attempt. Preserve the explanation that natural subtraction saturates at zero. |
| `Perm.truncated_subtraction@112` | `E.truncated_subtraction` | Mapped. Same negated universal claim, with the zero instance exposing the false strict inequality. |
| `Perm.lia_example1@124` | `E.lia_example1` | Mapped. All three variables are natural numbers and both source hypotheses are retained. `omega` replaces the manual arithmetic proof. |
| `Perm.lia_example2@147` | `E.lia_example2` | Mapped through `E.lia_example1`; the source's alternative proof method does not require a second independent mathematical argument. |
| `Perm.lia_example_3@170` | `E.lia_example_3` | Mapped. Arbitrary `f : Nat → Nat → Nat` and the opaque product `a * b` are preserved; no unjustified nonlinear arithmetic principle is assumed. |
| `Perm.maybe_swap@185` | `E.maybeSwap := S.compareSwap E.gtb` | Mapped by definition unfolding. Empty/singleton behavior, swap guard, first-pair exchange, and unchanged suffix agree with the source. |
| `Perm.maybe_swap_123@191` | `E.already_ordered` | Mapped exact source input and output. General correctness is available at that input, although this specific calculation is proved by reduction. |
| `Perm.maybe_swap_321@195` | `E.first_calculation`; connected through `E.first_calculation_spec` and `E.first_calculation_idempotent` | Mapped exact source calculation. The checked connections use the general theorems through definitional reduction, rather than merely reproving the result independently. |
| `Perm.maybe_swap_idempotent@202` | `E.maybe_swap_idempotent`; reflection explanation below | The aborted source attempt is replaced by the successful declaration at line 369. Its pedagogical issue is the conversion from a Boolean comparison to an arithmetic proposition. |
| `Perm.eqb_reflect@249` | `E.eqb_reflect`; Lean `Decidable` and `decide` replace Coq `reflect` | Truth-equivalence is mapped. The existing generic `decidable_of_bool` supplies the data-valued adapter, specialized by `E.reflectedLt` and exercised on both branches. |
| `Perm.ltb_reflect@255` | `E.ltb_reflect`; Lean `decide` reflection | Same strict-order proposition and Boolean truth contract. `E.reflectedLt` converts this law to a proof-carrying decision; `E.reflected_true_branch` and `E.reflected_false_branch` exercise both results. |
| `Perm.leb_reflect@261` | `E.leb_reflect`; also consumed by `E.certified_prefix` | Same non-strict-order proposition. The certificate composition supplies a concrete use of the reflection law. |
| `Perm.gtb_reflect@267` | `E.gtb_reflect`, used by `E.gtb_asymmetric`; `E.false_branch_reflect` | Both comparison directions are explicit for the actual swap comparator. Source `x > y` remains `y < x`. |
| `Perm.geb_reflect@273` | `E.geb_reflect`; Lean `decide` reflection | Same reversed non-strict relation; false branch follows from the standard `decide` equivalence. |
| `Perm.reflect_example1@284` | `E.reflect_example1` | Mapped. The Boolean guard remains in the statement. `by_cases` obtains a proposition or its negation, and `simp` connects it to the guard before `omega`. |
| `Perm.reflect_example1'@312` | `E.reflect_example1'` | Mapped through the preceding result; the alternate source proof has the same proposition. |
| `Perm.bdestruct@345` | Lean `by_cases h : P`, `simp [h]`, `of_decide_eq_true`, `decide_eq_false_iff_not`, and `omega`; demonstrated in the reflection and comparator-law proofs | Explicit proof-technique adaptation. No new tactic DSL or copied Rocq hint database is required. The current module comment mentions this replacement. |
| `Perm.reflect_example2@355` | `E.reflect_example2` | Mapped through `E.reflect_example1`. The associated tactic lesson is covered by the `bdestruct` adaptation. |
| `Perm.maybe_swap_idempotent@369` | `E.maybe_swap_idempotent` via `S.compareSwap_idempotent E.gtb E.gtb_asymmetric` | Mapped. The generic law needs only comparator asymmetry, and its natural-number specialization discharges that condition. |
| `Perm.manual_grade_for_Permutation_properties@454` | No mathematical grading-stub port. See the complete exercise mapping below. | Metadata adaptation. The requested mathematical properties are explicit Lean declarations; the `None` grading placeholder contributes no theorem. |
| `Perm.butterfly@460` | `E.butterfly` | Mapped exact natural-number variables and rearrangement, including the duplicate `t`. The proof composes `List.perm_append_comm` and append congruence. |
| `Perm.permut_example@534` | `E.permut_example` | Mapped exact polymorphic list positions over `Nat`, including the constants 5 and 6 and the harmless trailing empty append. |
| `Perm.not_a_permutation@548` | `E.not_a_permutation` | Mapped exact negative example `[1,1]` versus `[1,2]`; kernel-checked `decide` is intended, subject to the normal audit. |
| `Perm.maybe_swap_perm@560` | `E.maybe_swap_perm` via `S.compareSwap_perm` | Mapped. The source orientation `xs.Perm (maybeSwap xs)` is retained. The generic proof requires no order laws. |
| `Perm.first_le_second@576` | `S.FirstPair (fun a b : Nat => a ≤ b)` | Exact specialization by unfolding: relation on the first two values, `True` for empty and singleton lists. The source does not assert that the remaining suffix is ordered. |
| `Perm.maybe_swap_correct@582` | `E.maybe_swap_correct` via `S.compareSwap_correct` and `E.gtb_order_law` | Mapped exact conjunction of permutation and first-pair ordering. `E.not_whole_list_sorted` guards against a stronger, false whole-list reading. |
| `Perm.inv@603` | Lean `cases`/`rcases` for constructors and equalities, `subst` for substitution, and `noConfusion` for constructor contradictions | Proof-technique adaptation. This should be written explicitly in the accepted coverage note; the current module comment describes `bdestruct`/`lia` but does not mention `inv`. |
| `Perm.Forall_perm@613` | `E.forall_perm_inductive`, via `E.forall_perm` and Mathlib `List.forall_iff_forall_mem`; composed use `E.positive_after_swap` | Direct source-encoding adapter is now present. Membership quantification and List.Forall are connected by the existing proved equivalence, without replacing permutation by set equality. |

## All four exercise markers

| Exercise | Required treatment | Current Lean evidence |
|---|---|---|
| `Permutation_properties`, 2 stars, standard | Account for the four supplied properties, supply three additional properties, and identify the library laws supporting them. | Supplied: `E.permutation_length`, `E.permutation_symmetry`, `E.not_a_permutation`, `E.four_values_permuted`. Additional: `E.permutation_reflexivity`, `E.permutation_transitivity`, `E.permutation_membership`. Their inspected proofs use `List.Perm.length_eq`, `.symm`, `.refl`, `.trans`, and `.mem_iff`; concrete claims use `decide`. `E.permutation_occurrences` additionally records `List.Perm.count_eq`, making multiplicity preservation explicit. This meets the mathematical and library-discovery intent without copying a manual grade stub. |
| `permut_example`, 3 stars, standard | Prove the specified rearrangement for arbitrary natural-number lists. | `E.permut_example`, using append commutation and cons congruence. |
| `not_a_permutation`, 2 stars, standard | Refute the specified permutation. | `E.not_a_permutation`. A different proof technique from the source hints is harmless. |
| `Forall_perm`, 3 stars, standard | Transport an arbitrary element predicate along a permutation, with the source `Forall` encoding accounted for. | `E.forall_perm_inductive`, `E.forall_perm`, and the composed consumer `E.positive_after_swap`. |

The Perm chapter has no optional or advanced exercise markers. All four standard
exercises are in scope.

## All recorded source browsing commands

These commands display or search the source prover's environment and are not
additional mathematical declarations. Their Lean adaptations should be
documented, not implemented as a new proof dependency.

| Source inventory command lines | Source role | Lean adaptation |
|---|---|---|
| 50, 56 (`Locate`) | Locate propositional and Boolean comparison notation | `#check` the elaborated comparison/Boolean expressions; the typed definitions of `E.gtb` and `E.geb` make orientation explicit. |
| 51, 57, 63 (`Check`) | Inspect natural-order types and Boolean truth equivalence | `#check Nat.lt`, typed `decide` expressions, and the signatures of `E.ltb_reflect`/`E.leb_reflect`. |
| 67 (`Print`) | Inspect the source alias for natural less-than | `#print` or Lean's definitional equality for the selected comparison. No duplicate relation definition is needed. |
| 97, 103, 135, 139 (`Search`) | Find arithmetic implication/transitivity helpers | Lean library search or `omega`; `E.lia_example1` and `E.truncated_subtraction` retain the mathematical content. |
| 231 (`Print`), 242 (`Check`) | Inspect `reflect` and its construction from Boolean truth equivalence | Lean `Decidable`, `decide` truth/false laws, and the constructive equivalence discussion below. |
| 402 (`Print`) | Inspect the constructors of occurrence-sensitive permutation | `#print List.Perm`; the generic proof visibly uses `.refl` and `.swap`. |
| 446 (`Search`) | Discover permutation properties for the open-ended exercise | The seven property declarations listed above cite the selected Lean library laws. |
| 526–532 (`Check`) | Inspect permutation/append lemmas before `permut_example` | `List.Perm.cons`, `.trans`, `.refl`, `List.perm_append_comm`, and append equations. The theorem's proof uses these laws directly. |
| 545–546 (`Check`) | Inspect cancellation helpers before the negative example | Kernel decision of the same concrete proposition is an acceptable Lean proof; no cancellation-helper port is required. |

The source's `Infix`, hint registration, warning settings, imports and list
notation setup are ordinary prover integration details. Lean's standard
notations, `decide`, and scoped imports supply their role. They must not create
new global proof assumptions.

## Reflection: precise strength of the current encoding

Coq's `reflect P b` is an indexed data type with evidence for `P` in the true
case and evidence for `¬ P` in the false case. The Lean statements currently
express `b = true ↔ P`. With `b : Bool`, this is logically enough for both
branches: if `b = false`, any proof of `P` would imply `b = true`; conversely,
if `¬ P`, the true Boolean case contradicts the forward implication. For the
five concrete comparisons, Lean already supplies a constructive `Decidable`
instance, and `decide_eq_false_iff_not` provides the false branch directly.

Thus there is **no weakened mathematical claim** in the current Perm proofs.
The file now reuses Lean's generic `decidable_of_bool` adapter in
`E.reflectedLt`, rather than creating a competing reflection hierarchy. The
examples `E.reflected_true_branch` and `E.reflected_false_branch` inspect both
proof-carrying decision constructors. Accepted documentation should say that it
uses Lean's `Decidable`/`decide` mechanism rather than claiming a literal copy
of the Rocq type. A Boolean plus its truth-equivalence constructs `Decidable P`
by branching on that Boolean and proving both cases; no application axiom or
classical choice is needed for this construction.

The present branch usage is substantive: `E.gtb_reflect` discharges comparator
asymmetry, `E.gtb_order_law` treats both outcomes, and `E.leb_reflect` connects the
new operation to the existing ordering checker. Do not turn these proofs into
an opaque trusted Boolean evaluator.

## Forall: explicit source adapter

Coq's inductive `Forall P xs` and Lean's membership statement `∀ x ∈ xs, P x`
assert the same elementwise property. This property does not distinguish
repeated occurrences, but neither does the source `Forall`; the separate
`List.Perm` premise remains occurrence-sensitive.

The pinned Mathlib provides `List.forall_iff_forall_mem`, in
`Mathlib/Data/List/Basic.lean`, identifying `List.Forall P xs` with
`∀ x ∈ xs, P x`. The added `E.forall_perm_inductive` rewrites its input and
output through this equivalence and applies `E.forall_perm`. Its source
correspondence is therefore explicit, with no new `Forall` hierarchy. The
existing `E.positive_after_swap` is a connected consumer of the membership-form
theorem. Compiler verification of the latest additions remains for the parent
implementation loop; this mapper has inspected but not compiled the adapter.

## Statement and example connection inspection

The generic operation, relation, and laws are separated appropriately:

- `S.compareSwap_perm` has no order assumptions. Its statement really preserves
  List.Perm multiplicities for every comparator, including malformed ones.
- `S.compareSwap_idempotent` assumes only that a true comparison becomes false
  when reversed. This is sufficient; it is not claimed to be necessary.
- `S.compareSwap_firstPair` and `S.compareSwap_correct` use the exact two-branch
  relation contract needed for ordered output. They do not assume transitivity
  or silently order the tail.
- `S.compareSwap_drop_two` preserves the suffix exactly. A concrete
  theorem-connected specialization of this new helper would strengthen its
  worked-example evidence; the current first calculation confirms the expected
  tail independently but does not invoke this helper.
- `S.compareSwap_map` requires preservation of the comparator result, without
  injectivity or an order on payloads. `E.record_map` is a direct specialization
  using a potentially noninjective payload map.
- `S.firstPair_iff_chain_take_two` precisely relates the two-element prefix to
  the existing chain specification. It is consumed by
  `S.compareSwap_checkedPrefix`, whose concrete natural-number use is
  `E.certified_prefix`.
- `E.first_calculation_spec` and `E.first_calculation_idempotent` really use the
  general results. Their source-specialization connection is by definitional
  reduction of `maybeSwap`; lack of an explicit `rw` does not make it missing.
- `E.empty_case`, `E.singleton_case`, and `E.repeated_values` cover meaningful
  boundaries while invoking general correctness/permutation results.
- `E.not_whole_list_sorted` supplies a negative boundary example. The source
  result is first-pair ordering, not full sortedness.

The generic `compareSwap_correct` result also composes with the existing
`OrderCertificate.adjacent_correct` consumer. This is conaled integration beyond
a collection of isolated textbook answers, although it does not claim a cost
bound or a broader sorting algorithm.

## Concrete remaining work before source closure

1. Include the `inv` adaptation and the full `Decidable`/two-branch reflection
   explanation in the accepted chapter documentation. `inv` corresponds to
   `cases`/`rcases`, `subst`, and constructor discrimination via `noConfusion`.
   The explicit `E.reflectedLt` and `E.forall_perm_inductive` additions resolve
   the two initial correspondence-evidence gaps identified during preparation.
2. Consider a connected suffix-preservation specialization using
   `S.compareSwap_drop_two`, since that helper is new and the current independent
   calculation does not consume it. Existing examples suffice for most other
   helper claims; no quota of examples per theorem is implied.
3. Confirm the new modules are reachable from the public entrypoint and covered
   by the normal project build and exhaustive proof audit. The originator
   reports a passing focused build before the last reflection/Forall/count
   additions; this draft did not independently run compilation or an audit and
   does not report the latest additions as accepted.
4. Complete the existing independent Standards/Spec review loop and record any
   corrections against the exact source revision before closing the chapter.

No missing source arithmetic, permutation, conditional-swap, reflection,
Forall, or open-ended property obligation was found at the updated inspected
revision. This conclusion is preparation evidence, not final chapter acceptance.
