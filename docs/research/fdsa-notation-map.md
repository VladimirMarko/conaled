# FDSA Appendix C — notation correspondence

This map covers all 90 symbol-table entries, formatting conventions and
syntactic-sugar rows on printed pp.355–359 of the pinned edition.
`Examples.FunctionalNotation`, `Examples.FunctionalBasics` and
`Examples.ListLibrary` retain checked uses of the standard Lean/Mathlib
vocabulary. Editor markup is documented as formatting, not mathematical syntax
requiring a parallel parser. Implementation candidates remain subject to the
local tracker’s full validation and independent review gates.

## Evidence and pins

- Book: *Functional Data Structures and Algorithms: A Proof Assistant Approach*,
  July 27, 2026, <https://fdsa-book.net/functional_data_structures_algorithms.pdf>;
  SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
  PDF pages 361–365 were visually inspected as well as text-extracted. Printed
  p. 360 is blank; the bibliography starts at p. 361. There are no exercises or
  numbered mathematical theorems in this appendix.
- conaled: source interfaces at `1aabd512284fe86254278ac631eda061d311050b`;
  Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`;
  Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`.
- Lean core: `v4.35.0`, commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
  [Int/DivMod/Basic.lean](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Init/Data/Int/DivMod/Basic.lean),
  SHA-256 `3b831c3aee5aea53a8c40eb6332e5bd8de74b3e552df183da1f70412da978e95`.
- Isabelle: shared source pin
  `f86f290225eebcc52c1ae7dba2e098f405f51c21`.
  [Euclidean_Rings.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Euclidean_Rings.thy),
  SHA-256 `e5c9ce17d740ee9f6efb0e38870a5052d4276010b831f7a9d249265f018ae1bc`;
  [Groups_Big.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Groups_Big.thy),
  SHA-256 `719e0d98fe46cfc9ec88ef7e2a8687d07c55ed77cd45d66fbe524c8361e51943`.
  These supporting files resolve integer-division and infinite-set-fold semantics;
  the source pin postdates the book edition. Isabelle uses BSD-3-Clause terms;
  Lean/Mathlib/Batteries files use their Apache-2.0 notices.

Reading copies and page renders stay under `book-source/`, outside deliverables.
This original mapping and provenance are the durable artifact. Relevant inspected
Mathlib sources are `Data/Set/{Defs,Finite/Basic}.lean`,
`Order/Interval/Set/Defs.lean`, `Data/Multiset/{Defs,Filter,MapFold}.lean`,
`Algebra/BigOperators/Group/{List,Multiset,Finset}/Defs.lean`,
`Algebra/Order/Floor/Defs.lean`, `Data/Int/DivMod.lean`, and
`Logic/Function/Basic.lean`.

## Translation rules

The source's editor escapes and ASCII aliases describe Isabelle/jEdit input,
not Lean parser syntax. Preserve their mathematical meaning through the standard
Lean notation below. In particular, Isabelle's meta equality `==` must not become
Lean's Boolean `==` (`BEq`), and its function-type arrow `=>` must not be confused
with the `=>` separating a Lean lambda or match branch.

Isabelle/HOL uses its Boolean type for propositions. Lean statements use `Prop`;
executable predicates may use `Bool` or decidable propositions. State the
`decide`/Boolean-truth bridge when crossing that boundary; do not add decidability
to arbitrary set membership merely to imitate source printing.

Appendix C does **not** supply a precedence/associativity table. Preserve
grouping by typed syntax and parentheses instead of copying Isabelle token
precedence. Application is written `f x`; use `(f ∘ g) x`, explicit nested binders,
and parentheses around combined arithmetic/logic when needed. The table's
variable convention becomes explicit Lean binders: arbitrary typed `x,y`,
`m,n : Nat`, predicates/propositions or Boolean functions as appropriate,
`xs : List α`, `A : Set α`, and `M : Multiset α`. The cited eta contraction is
ordinary function eta reduction; it requires no new mathematical operation.

## C.1: complete symbol map

| ID | Source symbol or role | Lean/Mathlib meaning and boundary |
|---|---|---|
| AC-001 | `λ`, function abstraction | `fun x => t`; lambda binding, not a new combinator. |
| AC-002 | `≡`, meta equality | An asserted correspondence is `Eq` (`=`); a definition uses `def ... := ...`. Use `rfl` only where definitional equality actually holds. |
| AC-003 | `≠` | `Ne`, notation `x ≠ y`; this is a proposition. |
| AC-004 | `⋀`, meta universal binder | Theorem parameters or dependent `∀`; Lean has no separate Isabelle/Pure quantifier layer to reproduce. |
| AC-005 | `∀`, HOL universal binder | `∀ x, P x`, including dependent binders. |
| AC-006 | `∃` | `Exists`, notation `∃ x, P x`. |
| AC-007 | `⟹`, meta implication | A theorem hypothesis or `P → Q`; retain all premises explicitly. |
| AC-008 | `⟶`, HOL implication | `P → Q` for propositions; Boolean realizations need their truth adapter. |
| AC-009 | `⟷` | `Iff`, notation `P ↔ Q`; not equality of arbitrary values. |
| AC-010 | `⇒`, function-type arrow | `α → β`; dependent functions use `(a : α) → β a`. |
| AC-011 | `←`, list-comprehension generator | Standard `List.map`, `filter`, `flatMap`, or typed List `do` notation; preserve generator order and multiplicity. |
| AC-012 | `¬` | `Not`, notation `¬ P`; Boolean negation is a separate operation. |
| AC-013 | `∧` | `And`; Boolean conjunction uses `&&` with a correspondence. |
| AC-014 | `∨` | `Or`; Boolean disjunction uses `\|\|` with a correspondence. |
| AC-015 | `∈` | Typed `Membership.mem`: distinguish Set, List and Multiset carriers. |
| AC-016 | `∉` | Negated membership in the same carrier. |
| AC-017 | `∪` | For source sets, `Set.union`; finite/multiset operations are different instances. |
| AC-018 | `∩` | For source sets, `Set.inter`. |
| AC-019 | big union `⋃` | `Set.sUnion S` / `⋃₀ S` for a set of sets; indexed unions use `iUnion`. |
| AC-020 | big intersection `⋂` | `Set.sInter S` / `⋂₀ S`; indexed intersections use `iInter`. |
| AC-021 | `⊆` | `Set.Subset`; pointwise implication of membership. |
| AC-022 | `⊂` | Proper set inclusion, `A ⊂ B`, distinct from nonstrict inclusion. |
| AC-023 | `≤` | Typed `LE.le`; operations expose only the order capabilities their laws need. |
| AC-024 | `≥` | Reversed `≤`; it introduces no second comparison relation. |
| AC-025 | `∘` | `Function.comp`, with `(f ∘ g) x = f (g x)`. |
| AC-026 | `×` | Product type `Prod α β`; set Cartesian product is `Set.prod A B`, written `A ×ˢ B`. |
| AC-027 | absolute-value bars | `abs x`; do not infer list length or multiset cardinality from the same printed bars. |
| AC-028 | left floor delimiter | Together with AC-029, `Int.floor x` / `⌊x⌋`; target type matters. |
| AC-029 | right floor delimiter | Completes the floor expression, not an independent operator. |
| AC-030 | left ceiling delimiter | Together with AC-031, `Int.ceil x` / `⌈x⌉`; natural versions require an explicit correspondence. |
| AC-031 | right ceiling delimiter | Completes the ceiling expression. |
| AC-032 | `∑` | Standard typed finite/set, multiset or list sum; see AC-078–083. |
| AC-033 | `∏` | The corresponding typed products; see AC-084. |
| AC-034 | Book multiset brace glyphs and Isabelle `{# ... #}` | Use expected type `Multiset α`, its literals/cons/addition. Source brace spelling is typographic, not a new Lean container. |

## C.2: subscripts and superscripts

| ID | Formatting convention | Lean disposition |
|---|---|---|
| AC-035 | Single-symbol `\<^sub>` | A name such as `x₀` is a binder/identifier; it is not list indexing. |
| AC-036 | Single-symbol `\<^sup>` | Preserve whether the context means a decorated name, power, inverse or another operation; write the actual Lean expression explicitly. |
| AC-037 | Long subscript `\<^bsub> ... \<^esub>` | Isabelle rendering markup has no semantic counterpart to port. Use ordinary names, arguments or indexed notation with explicit types. |
| AC-038 | Long superscript `\<^bsup> ... \<^esup>` | Same distinction: formatting does not supply an algebraic operation or an indexing proof. |

## C.3: every syntactic-sugar row

### Arithmetic and lists

| ID | Source form | Exact target or remaining bridge |
|---|---|---|
| AC-039 | Multiplication | `x * y` using the appropriate multiplication instance. |
| AC-040 | Real slash/fraction division | `(x / y : ℝ)`; type annotation distinguishes it from integer/natural quotient. |
| AC-041 | `div` on `nat` or `int` | Natural division maps to `Nat.div` / `/`. Unrestricted Isabelle integer division maps to `Int.fdiv`, **not** default `Int.ediv`; see the boundary register. |
| AC-042 | Numeric absolute value | `abs x` in the corresponding ordered algebraic type. |
| AC-043 | Floor | `Int.floor x`; `Nat.floor` is truncated at zero and is not an unrestricted replacement. |
| AC-044 | Ceiling | `Int.ceil x`; use `Nat.ceil` only with the appropriate nonnegativity/cast bridge. |
| AC-045 | Natural-number exponent | `x ^ n` with `n : Nat`; do not substitute real exponentiation or decorated identifiers. |
| AC-046 | Length bars around a list | `xs.length : Nat`, not cardinality of its support. |
| AC-047 | Empty list | `([] : List α)` / `List.nil`. |
| AC-048 | List cons `x # xs` | `x :: xs` / `List.cons x xs`. |
| AC-049 | Two-element list literal | `[x, y] = x :: y :: []`; retains order and repeated elements. |
| AC-050 | Half-open natural list interval `[m..<n]` | `List.Ico m n`, defined as `List.range' m (n-m)`; increasing, lower-inclusive and upper-exclusive. `List.Ico.mem`, `succ_top`, and `eq_nil_of_le` give the exact standard bridges also recorded in Appendix A. The subtraction is natural truncated subtraction. |
| AC-051 | Zero-based list selection `xs ! n` | `xs[n]` with a proof `n < xs.length`, or `xs[n]? : Option α`. Source invalid-index underspecification is not a global inhabitant assumption. |
| AC-052 | List update `xs[n := y]` | `List.set xs n y`; preserve its out-of-range no-op behavior and length. This is not unrestricted function update. |

### Sets

| ID | Source form | Exact target or remaining bridge |
|---|---|---|
| AC-053 | Empty set | `(∅ : Set α)`. |
| AC-054 | Two-element set | `({x, y} : Set α)` / nested `Set.insert`; duplicates collapse. |
| AC-055 | Set membership | `x ∈ A`, definitionally the set predicate at `x`. |
| AC-056 | Set nonmembership | `x ∉ A`, equivalently `¬ (x ∈ A)`. |
| AC-057 | Set union | `A ∪ B`; membership is disjunction. |
| AC-058 | Set intersection | `A ∩ B`; membership is conjunction. |
| AC-059 | Set inclusion | `A ⊆ B`; all members of A belong to B. |
| AC-060 | Proper set inclusion | `A ⊂ B`; do not erase its strictness. |
| AC-061 | Direct image `f ‘ A` | `f '' A` / `Set.image f A`; injectivity is not required. |
| AC-062 | Predicate comprehension | `Set.setOf P`, displayed `{x ∣ P x}` here to avoid a Markdown table delimiter. No finiteness or decision procedure is required. |
| AC-063 | Restricted comprehension | `Set.setOf (fun x => x ∈ A ∧ P x)`; the source expansion's reversed conjunction is equivalent. |
| AC-064 | Two-variable image comprehension | `Set.setOf (fun z => ∃ x y, z = f x y ∧ P x y)`; retain both existential witnesses. |
| AC-065 | Union indexed by members of A | `⋃ x ∈ A, f x`, or `Set.sUnion (f '' A)`; standard membership equivalence connects the forms. |
| AC-066 | Bounded universal quantifier | `∀ x ∈ A, P x`, expanding to membership implying P. |
| AC-067 | Bounded existential quantifier | `∃ x ∈ A, P x`, expanding to an existential with membership conjunction. |

### Multisets

| ID | Source form | Exact target or remaining bridge |
|---|---|---|
| AC-068 | Multiset cardinality bars | `M.card : Nat`; `Multiset.coe_card` relates a list's multiset cardinality to its length. |
| AC-069 | Empty multiset | `(0 : Multiset α)` / `∅`; multiplicities are all zero. |
| AC-070 | Two-element multiset | `(x ::ₘ y ::ₘ 0)` or a typed multiset literal; repeated values retain multiplicity. |
| AC-071 | `x ∈# M` | `x ∈ M`; this asks for positive membership, not an occurrence index. |
| AC-072 | `x ∉# M` | `x ∉ M`. |
| AC-073 | Filtered multiset comprehension | `M.filter P` with `[DecidablePred P]`; `Multiset.mem_filter` and `filter_coe` supply standard observation bridges. |
| AC-074 | Multiset image comprehension | `M.map f`; `Multiset.mem_map`, `card_map`, `map_coe`. Values may coincide; multiplicities are preserved and accumulated. |
| AC-075 | Universal multiset membership quantifier | `∀ x ∈ M, P x`; predicate truth depends on support, though the carrier still retains counts. |
| AC-076 | Existential multiset membership quantifier | `∃ x ∈ M, P x`. |
| AC-077 | Submultiset `M ⊆# M'` | `M ≤ M'`, the multiplicity-sensitive order. Lean `M ⊆ M'` instead compares supports and is insufficient. |

### Sums and products

| ID | Source form | Exact target or remaining bridge |
|---|---|---|
| AC-078 | Sum of the elements of a set A | For `hA : A.Finite`, `hA.toFinset.sum id`; see the infinite-set convention below. |
| AC-079 | Sum of `f x` over members of A | `hA.toFinset.sum f`, or a supplied finite representation with its membership equality. `Finset.sum` needs an additive commutative monoid. |
| AC-080 | Sum from index i through j | The source is the set fold over `Set.Icc i j`; i and j are not explicitly restricted to Nat. For finite discrete intervals, e.g. Nat, `(Finset.Icc i j).sum f` is the standard target. Both endpoints are included; retain the finite/otherwise-neutral convention for arbitrary ordered intervals. |
| AC-081 | Sum of multiset M | `M.sum`; `Multiset.sum` retains multiplicities and requires `AddCommMonoid`. |
| AC-082 | Sum of `f x` over multiset occurrences | `(M.map f).sum`; do not replace M with its support. |
| AC-083 | Sum of `f x` over a list | `(xs.map f).sum`; order and multiplicity remain. The standard list API has additive-monoid laws without requiring commutativity. |
| AC-084 | Corresponding product forms | `Finset.prod`, `Multiset.prod` and `List.prod`, with the corresponding commutative-monoid versus ordered-list monoid distinction and neutral element 1. |

### Ordered intervals

The standard set-interval declarations use `Preorder α`; the membership witness
retains that capability. No totality or antisymmetry is needed for these six
definitional endpoint predicates.

| ID | Source interval | Exact target and membership |
|---|---|---|
| AC-085 | Lower closed unbounded `{x..}` | `Set.Ici x`; `z` belongs iff `x ≤ z`. |
| AC-086 | Upper closed unbounded `{..y}` | `Set.Iic y`; `z` belongs iff `z ≤ y`. **The printed internal-name cell is wrong.** |
| AC-087 | Closed `{x..y}` | `Set.Icc x y`; `x ≤ z ∧ z ≤ y`. |
| AC-088 | Left closed/right open `{x..<y}` | `Set.Ico x y`; `x ≤ z ∧ z < y`. |
| AC-089 | Left open/right closed `{x<..y}` | `Set.Ioc x y`; `x < z ∧ z ≤ y`. |
| AC-090 | Open `{x<..<y}` | `Set.Ioo x y`; `x < z ∧ z < y`. |

The standard `Set.mem_Ici`, `mem_Iic`, `mem_Icc`, `mem_Ico`, `mem_Ioc` and
`mem_Ioo` lemmas expose exactly these predicates. Set intervals are not lists;
finite natural interval enumeration and `Finset.Icc/Ico` require their own
standard membership bridge when used as executable representations.

## Corrections and semantic boundaries

1. **Printed interval error, p. 359.** The upper interval `{..y}` is expanded as
   `atLeast y`. Its intended expansion is `atMost y`, corresponding to
   `Set.Iic y`. This was checked visually, not inferred only from extraction.
   Over Nat at `y=1`, `0 ≤ 1` while `¬ 1 ≤ 0`; also `1 ≤ 2` while `¬ 2 ≤ 1`.
   These independently evaluated small cases distinguish both directions.
   `FunctionalNotation.upper_interval_correction` retains the checked small
   counterexample and this map records the correction; do not change the meaning of upper intervals to match
   the typo.
2. **Integer division is not a glyph-only substitution.** The pinned Isabelle
   `divide_int` definition rounds the quotient down. Pinned Lean `Int.ediv`,
   which supplies `/`, rounds up for a negative divisor to keep its remainder
   nonnegative. Thus Isabelle `5 div (-2) = -3`, whereas Lean's default integer
   `/` gives `-2`. Lean `Int.fdiv` gives `-3` and has the matching floor-division
   definition, including zero-divisor value 0. The discrepancy was checked by
   evaluating the two source definitions independently in scratch Python;
   `FunctionalNotation.negative_divisor_distinguishes` is the corresponding
   checked Lean case. `Int.fdiv_eq_ediv_of_nonneg` supports using `/`
   when the divisor is known nonnegative. Ordinary natural division is already
   the required standard operation. No new division implementation is needed.
3. **Set folds on infinite sets need their source convention.** Isabelle's
   `Groups_Big` defines ordinary `sum`/`prod` through `comm_monoid_set.F`, whose
   `infinite` lemma returns the neutral element on an infinite indexing set.
   For finite A, `Set.Finite.toFinset` and `Finset.sum/prod` are exact targets.
   If an unrestricted source statement includes infinite A, expose the
   finite/otherwise-neutral adapter; do not silently replace it by a series or
   a finite-support sum. A function supported only at 0 over the infinite set
   of naturals distinguishes the ordinary source sum (0) from a support-based
   sum of that nonzero term. This is a convention bridge, not an algorithmic
   performance theorem.
4. **Multiset inclusion and cardinality retain repetitions.** A multiset with
   two copies of 1 has cardinality 2 and is not below the singleton multiset.
   Its support is nevertheless included in the singleton's support. Pinned
   `Multiset.Defs` explicitly distinguishes `Subset` (`⊆`) from `Le` (`≤`).
   The same distinction separates list/multiset sums from summing a deduplicated
   set. Use the native coercion/card/map/filter bridges rather than a new bag
   implementation.
5. **Natural arithmetic and invalid list inputs remain typed.** Expressions
   such as `n-1` and `n-m` on `Nat` are truncated subtraction; a cast to Int
   before subtracting changes the statement. Source indexing is zero-based.
   Use `Option` or a bounds proof for invalid-index handling, as recorded in
   [the shared reconstruction map](fdsa-reconstruction-map.md). `List.set` leaves an out-of-range index unchanged;
   `Function.update` changes a function at any key and has different semantics.
   Its `update_self`/`update_of_ne` API is available for actual source function
   updates elsewhere, but it must not replace this list-update row.

## Connected clients and statement review

The project already uses the intended distinctions: Sorting's `KeySorted` and
`StableSort` observe lists and filtered equal-key sequences; Selection's
`RankedAt` is a zero-based occurrence predicate while `selectWith` is a public
one-based Option API; RandomAccess's `fetchRA_refinement` and
`updateRA_refinement` connect its representation to `List.getElem?` and
`List.set`; Symmetric sequences expose `headSL_eq_head` through `List.head?`.
Preserve these contracts instead of introducing book-shaped duplicate notation.

The retained cases use public standard operations and the shared list
interfaces; they are not an assertion that source typography is Lean syntax.

| Coverage group | Checked use or standard witness |
| --- | --- |
| AC-001–014, AC-025, AC-035–038 | Typed Lean binders; `composition_and_eta`, `boolean_truth`, `comprehension_order_and_repetition`. Decorated names are identifiers, not lookup or power operations. |
| AC-015–024, AC-053–067 | `set_union_intersection`, `proper_subset`, `direct_image`, `restricted_comprehension`, `two_variable_comprehension`, `indexed_union`, `set_of_sets_observations`, `bounded_quantifiers`. |
| AC-026 | Standard `Prod` and `product_membership`; no conflation of a product type with a set product. |
| AC-027–031, AC-039–045 | `typed_arithmetic`, `floor_division_nonnegative`, `negative_divisor_distinguishes`, `floor_division_zero`, `floor_and_ceiling`; existing `FunctionalBasics.real_cast_add`, `real_cast_sub`, `truncated_subtraction_matters`, `integer_to_nat_boundary`. |
| AC-034, AC-046–052 | Standard list constructors/length and the complete Appendix A map in `fdsa-reconstruction-map.md`; `ListLibrary.range_boundaries`, `range_membership`, `index_valid`, `invalid_index_and_update`, `update_observations` and Empty-payload cases. |
| AC-068–077 | `FunctionalBasics.multiset_observations`, `multiset_map_filter`, `multiset_append`, `multiset_membership`; `FunctionalNotation.submultiset_is_not_support_subset` and the native `Multiset.coe_card`, `card_map`, `map_coe`, `filter_coe` bridges. |
| AC-032–033, AC-078–084 | `repeated_sum_and_product`, `closed_interval_fold`, `ordered_list_folds`, standard Finset/Multiset/List folds, `finiteIndexProduct`/`finiteIndexSum`, their finite/Finset/infinite equations, and `finite_index_values`/`infinite_index_values`. |
| AC-085–090 | `all_interval_memberships`, `upper_interval_correction`; all six interval predicates preserve the actual endpoint inequalities. |

Statement review checks that universes are independent when functions cross
payload types. Set statements require no blanket equality or membership
algorithm. The Prop/Bool correspondence explicitly requires decidability for
its executable `decide` calls; arbitrary propositions and sets remain more
general. Proper subset retains inequality, image retains the witness, and the
two-variable comprehension retains both witnesses. The flattened list
comprehension returns `[2,12,2,12]`, exposing generator order and repeated
occurrences.

The arithmetic examples distinguish truncated natural division from real
division, expose negative-divisor floor division, and give integer floor -2
and ceiling -1 for the negative value -3/2. The nonnegative-divisor bridge
retains its hypothesis, including the zero-divisor convention, instead of
claiming unrestricted equality with Lean's default integer quotient. Existing
natural subtraction/cast checks remain the source witnesses for truncation.

Multiset inclusion compares occurrence counts. Two copies of 1 have support
included in the singleton's support, but do not form a submultiset of that
singleton. The list and multiset `[2,2,3]` sum to 7 and multiply to 12; the
corresponding deduplicated finite set sums to 5 and multiplies to 6. The closed
natural interval from 2 through 4 includes both endpoints, giving sum 9 and
product 24. `ordered_list_folds` retains only a monoid or additive monoid,
without requiring the commutativity that unordered finite folds need.

The only new notation-convention adapter is `finiteIndexProduct`, with its
additive counterpart `finiteIndexSum` generated through `to_additive`. It
selects the standard `Set.Finite.toFinset` fold when the entire index set is
finite, and the neutral element otherwise. The finite-set correspondence
exposes the ordinary `Finset.prod`/`Finset.sum` result; the infinite equation
retains the source's convention regardless of the function's support.
`finite_index_values` gives value 7 on the singleton index set `{0}`;
`infinite_index_values` gives sum 0 and product 1 on all naturals even though
the function differs from the neutral value only at 0. `empty_index_type`
checks both neutral values with the uninhabited index type `Empty`. These results require
only the appropriate commutative monoid on values. Index types have no public
`Fintype`, equality, membership-decision or inhabitant requirements. The local
classical finiteness decision is explicitly noncomputable and supplies no
runtime finiteness algorithm. The standard support-based `finsum`/`finprod`
operations were inspected and are deliberately not used for this adapter.

Appendix C supplies no execution-cost recurrence. Expanding syntactic sugar or
proving equality of values does not transfer Appendix B's observations.
Acceptance records belong to the local tracker and durable checkpoints; this
map is not a substitute for the complete candidate build, proof audit and
both independent review axes.
