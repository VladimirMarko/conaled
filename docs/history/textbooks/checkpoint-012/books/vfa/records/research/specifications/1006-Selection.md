# Local #1006 — VFA Selection: requirements and reuse plan

**Planning only, 2026-11-02. Implementation is blocked until #1005 BagPerm is accepted.**
The predecessor chain remains Perm → Sort → Multiset → BagPerm → Selection → Merge.
No chapter algorithm, proof, example, or acceptance is supplied by this document.
All proposed names and statements below await the ordinary implementation loop.
This preparation changes only this plan and the companion #1007 plan; it does
not change tickets, source inventories, either checkout, or validation state.

## Source and baseline

- VFA 2.1, release header `2026-08-24 10:11`, Coq/Rocq 9.0.0 or later:
  [Selection](https://softwarefoundations.cis.upenn.edu/vfa-2.1/Selection.html).
- Complete inspected source: `reference/vfa/vfa/Selection.v`, 462 lines,
  14,528 bytes, SHA-256 `ff343099ae0fd551648a8fa2bf0adfe32bf5fb158389cee211ff8d1b32c28e11`.
- `../source/Selection.inventory.json`: **33 records; 20 exercises**, comprising
  16 non-optional standard and four optional standard exercises. Records include
  one expected failed definition, five source-proved examples, and one
  transparent well-founded definition. Every record is mapped below.
- The versioned archive and verification/changed-source rules are in
  `../source/SOURCE-RECOVERY.md`; archive SHA-256 is
  `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
  Preserve the MIT notice in `../source/VFA-LICENSE.txt`; ADR 0001 excludes
  research copies of the book from the project deliverable.
- Inspected checkout: `1da24c77d10fe03296dbf117e4249283139f5021`, with Lean 4.35.0
  and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Its full gate was still
  running; this is not an accepted Selection baseline. Capture the actual
  accepted #1005 baseline before implementation.

Read with `1003-Sort.md`, `1004-1005-Multiplicity-plan.md`,
`../source/SORTING-STABILITY-BOUNDARIES.md`, and
`../source/RESOURCE-AND-EXECUTION-OBLIGATIONS.md`. The shared sorting draft
under `../staging/sorting-specs/` is preparation, not accepted chapter coverage;
use the interfaces actually integrated by the predecessors when this chapter starts.

## Reuse and intended small extension

| Existing declaration/interface, inspected in source | Role and limit |
| --- | --- |
| `Applications.Sorting.KeySorted` in `Applications/Sorting/Stable.lean` | Pairwise key order. Bridge the source's adjacent inductive sortedness through the accepted Sort interface; do not silently substitute a stronger predicate without its equivalence. |
| `Stable`, `StableSort`, `StableSort.unique` in the same file | Equal-key record observations and stable-output uniqueness. Generic source selection sort is not stable, so its full result must not inhabit `StableSort`. |
| `insertionOn`, `insertionOn_spec`, `sortOn_correct`, `sortOn_eq_insertionOn` in `Applications/Sorting/Sort.lean` | Existing sorted/permutation clients and comparison algorithms. They do not implement selection or prove its fuel, reconstruction, or cost behavior. |
| `List.Perm.length_eq`, `List.Perm.mem_iff` and accepted Perm Forall transport | Derive the remainder length, selected-element membership, and lower-bound transport from actual permutation results. Definitions/permutation require no payload equality decision. |
| `List.Perm.eq_of_pairwise'`, Mathlib `Data/List/Sort.lean:300–305` | Equality of two pairwise-sorted permuted lists under `Std.Antisymm r`. Use for Nat outputs or mapped key lists; key antisymmetry does not make the pulled-back relation antisymmetric on records. |
| Accepted Multiset/BagPerm contents, count, and permutation bridges | Preserve multiplicity and recover both source specifications. Function bags are all functions `Nat → Nat`; only list contents have finite support. |
| `Resources.Measured`, `bind`, `bind_erases`, `erasureSquare`, `reweight_bind`, `reweight_bound` in `Applications/Resources/Measured.lean` | Instrument the real recurrence and prove erasure separately from an independent count specification. Equal values do not determine costs. |
| `Resources.isBigO_of_nat_bound` in `Applications/Resources/Growth.lean` | Transport an eventual bound `f n ≤ C * g n` on Nat counts to real-cast `Asymptotics.IsBigO`. Supply the actual counted function and size bound first. |

Suggested placement is `Applications/Sorting/SourceSelection.lean`, plus a
small resource module only if it helps the import structure, and an existing
or new `Examples/SelectionSorting.lean` client. Use prefixed names in the
existing `Applications.Sorting` namespace; no new sorter/comparator hierarchy,
cost language, or heap framework is required. A key version can follow
`SourceMerge.lean`'s local pulled-back `LE`/`DecidableLE` pattern.

## Required executable equations and termination accounts

Write `pick`, `F`, `S`, and `W` below for **proposed** source-select, fuelled,
length-fuel, and well-founded adapters. These are shorthand, not existing APIs.

```text
pick x [] = (x, [])
pick x (h :: t) =
  if x ≤ h then let (y, r) = pick x t; (y, h :: r)
           else let (y, r) = pick h t; (y, x :: r)
F xs 0 = []; F [] n = []
F (x :: xs) (n + 1) = let (y, r) = pick x xs; y :: F r n
S xs = F xs xs.length
W [] = []
W (x :: xs) = let (y, r) = pick x xs; y :: W r
```

Both branches' remainder order is material. A minimum chosen with `erase`, a
generic sort with equal Nat outputs, or a swap-based implementation is not an
automatic recurrence bridge. The Boolean Nat test is adapted by an executable
`DecidableLE`; record reflection and both branches, including ties.

`F` structurally decreases fuel. `W` must have a checked length measure:
`pick x xs = (y,r)` implies `r.length = xs.length < (x :: xs).length`.
Retain the two executable definitions and prove their correspondence; making
`W` merely an alias of `S` would miss the source's second termination account.
The source expected failure explains why `r` is not a structural subterm;
Lean need not reproduce Rocq's exact diagnostic or generated helper names.

Pending prose-strengthening obligations are `length (F xs n) = min xs.length n`,
fuel saturation when `xs.length ≤ n`, and `W xs = S xs` through the recurrences.
Together they explain why insufficient fuel loses elements and excess fuel
does not change the answer. Fuel counts outer selections, not comparisons.

Require only executable comparison for definitions, permutation, length,
membership, fuel, and erasure. Minimum/sortedness proofs can use the existing
`Std.IsLinearPreorder` key assumptions (preorder plus totality); they require
neither key antisymmetry nor ordering/equality on payloads. A supplied
`KeySorted key xs` suffices for the source fixed-point proof without adding
global order laws. Nat and exact source statements remain explicit specializations.

## Complete record and exercise obligations

**All rows are pending.** `Adj` means the source adjacent sortedness adapter;
`Bound y xs` means the source `Forall (fun z => y ≤ z) xs`, with an explicit
bridge to membership-wise bounds. `C` denotes the accepted source contents
function; `E` marks a non-optional standard exercise and `O` an optional one.
The inventory ID includes the original source line; source-specific equality
and permutation orientations are retained.

| Source inventory ID | Exact obligation / proposed treatment |
| --- | --- |
| `Selection.select@41` | The `pick` equations above, for every input; generic key realization and Nat specialization. |
| `Selection.selsort@56` | Expected `Fail Fixpoint` attempt, not a missing theorem. Explain the structural-recursion obstruction and check `pick 1 [0,2] = (0,[1,2])`; use the later length proof for actual termination. |
| `Selection.selsort@77` | `F` with both zero-fuel and empty-list clauses and one selection at each positive-fuel nonempty step. |
| `Selection.out_of_fuel@87` | `F [3,1,4,1,5] 3 ≠ [1,1,3,4,5]`; retain the actual partial output `[1,1,3]` and connect the length obstruction. |
| `Selection.extra_fuel@94` | `F [3,1,4,1,5] 10 = [1,1,3,4,5]`; connected use of fuel saturation. |
| `Selection.selection_sort@102` | `S xs = F xs xs.length`, with its source contract. |
| `Selection.sort_pi@105` | Source input `[3,1,4,1,5,9,2,6,5,3,5]` gives `[1,1,2,3,3,4,5,5,5,6,9]`; connect the source correctness theorem to this checked output. |
| `Selection.sorted@119` | Empty, singleton, and adjacent-cons rules (`i ≤ j` plus `Adj (j::xs)`). Reuse the accepted source IsChain presentation and explicitly identify both chapter presentations. |
| `Selection.is_a_sorting_algorithm@126` | For arbitrary `f`, `∀ xs, xs.Perm (f xs) ∧ Adj (f xs)`. Preserve input-to-output orientation; no stability field. |
| `Selection.pairs_example@139` | Pair eta/destruction: `(a,b) = (let (c,d) := pick x l; (c,d)) → (a,b) = pick x l`. Source universally quantified extra `c,d` are unused; explain Lean `cases`/pair eta adaptation. |
| `Selection.select_perm@153` **E** | `pick x l = (y,r) → (x::l).Perm (y::r)`; recurrence proof, independent of order laws. |
| `Selection.select_rest_length@166` **E** | Same equality implies `l.length = r.length`; derive from permutation length and cancel the successor. |
| `Selection.selsort_perm@178` **E** | `∀ n l, l.length = n → l.Perm (F l n)`; do not omit the fuel premise. |
| `Selection.selection_sort_perm@189` **E** | `∀ l, l.Perm (S l)` by the length-fuel specialization. |
| `Selection.select_fst_leq@201` **E** | `pick x al = (y,bl) → y ≤ x`; use comparison branches and transitivity. |
| `Selection.le_all@212` | Source `Forall` lower bound `Bound`; preserve its meaning, not merely a new unexplained predicate. |
| `Selection.le_all__le_one@222` **E** | `Bound y lst → n ∈ lst → y ≤ n`; use the Forall/membership bridge. |
| `Selection.select_smallest@234` **E** | `pick x al = (y,bl) → Bound y bl`; together with the previous minimum bound and membership, identifies an actual minimum, not an arbitrary lower bound. |
| `Selection.select_in@247` **E** | Same select equality implies `y ∈ x::al`; derive from the select permutation. |
| `Selection.cons_of_small_maintains_sort@262` **E** | `n = bl.length → Bound y bl → Adj (F bl n) → Adj (y :: F bl n)`. Retain this orientation of the length equality; transport the bound through fuelled permutation. |
| `Selection.selsort_sorted@278` **E** | `al.length = n → Adj (F al n)`; use minimum bounds, rest length, and the recursive result. |
| `Selection.selection_sort_sorted@289` **E** | `∀ l, Adj (S l)`; source specialization plus KeySorted bridge. |
| `Selection.selection_sort_is_correct@300` **E** | Combine the actual `S` permutation and sortedness theorems into the source contract. |
| `Selection.selsort'@329` | `W`, length-measured recursion and termination proof, transparent executable definition, and public one-level equations. |
| `Selection.selsort'_example@353` | `W [3,1,4,1,5,9,2,6,5] = [1,1,2,3,4,5,5,6,9]`; this is the nine-element example, not the eleven-element `sort_pi`. |
| `Selection.selsort'_perm@375` **E** | `∀ n l, l.length = n → l.Perm (W l)`. An unconditional theorem may supply this exact redundant-`n` wrapper. |
| `Selection.cons_of_small_maintains_sort'@388` **E** | `Bound y bl → Adj (W bl) → Adj (y::W bl)`; no fuel or length hypothesis. |
| `Selection.selsort'_sorted@401` **E** | `∀ n al, al.length = n → Adj (W al)`; retain the source wrapper around any stronger result. |
| `Selection.selsort'_is_correct@411` **E** | Source sorting contract for `W`. Transport through the proved `W = S` bridge is allowed; a checked client must still exercise the well-founded equations. |
| `Selection.select_contents@431` **O** | Select equality implies `union (singleton x) (C al) = union (singleton y) (C bl)`. Prove from the select recurrence and pointwise union laws as a genuine alternate contents argument. |
| `Selection.selection_sort_contents@440` **O** | **`∀ n l, l.length = n → C l = C (S l)`**. The output is `selection_sort l`, not `selsort l n`; derive via the contents recurrence route and retain the redundant `n`. |
| `Selection.sorted_iff_sorted@449` **O** | Local Selection sortedness iff the accepted Sort presentation, in both directions through the explicit adjacent/constructor adapters. |
| `Selection.selection_sort_correct'@456` **O** | Multiset's `∀ l, C l = C (S l) ∧ Sort.sorted (S l)`. Use the contents result and preceding sortedness bridge; multiplicity is required. |

## Source commands and proof-method coverage

| Source command/prose | Lean disposition required at implementation |
| --- | --- |
| `Set Warnings`, imports, constructor hints (`27–30,124`), `Hint Unfold le_all`/`<=*` (`213–214`) | Use pinned imports, explicit namespace/notation, existing constructor and simplification lemmas. Do not disable project warnings or recreate a global tactic database. |
| Failed structural definition (`56–69`) and pair decomposition (`131–144`) | Record the failure's reason and usable remainder witness; retain the successful fuel/measure alternatives and pair case handling. No admitted failed-definition stub. |
| `Recdef` and `Defined` discussion (`323–359`) | Lean `termination_by`/decrease proof, computational definition, and checked equations/case. Explain that Rocq `Qed` versus `Defined` is not a rule about Lean's proof opacity or definitional reduction. |
| `Print selsort'`, `Print selsort'_terminate` (`361–362`), `Check selsort'_equation` (`368`) | Document the Lean well-founded definition/termination argument and expose an equation theorem that an actual proof uses. Generated Rocq helper names need no artificial Lean equivalents; a `#check` alone is not a mathematical bridge. |
| Multiset import and alternate proof route (`423–458`) | Use accepted function-bag operations and genuine direct contents preservation. The source requests a multiset approach; it does not impose an explicit tactic ban. |

Induction and “no induction needed” hints guide the exposition, not additional
axioms or universal bans on library reuse. The optional section remains in
scope. Its direct contents argument should not be replaced throughout by
applying permutation-to-contents to the already completed ordinary proof.
Both final specifications can then use the accepted general equivalence.

## Resource obligations and qualifications

The efficiency prose is at `Selection.v:13–25`. Use an explicit unit charge
for each head comparison, independent of its operands, and distinguish that
model from Rocq unary-Nat comparison, Lean's Nat representation, and runtime.

1. Instrument the actual select recursion. Prove value erasure and exactly
   `xs.length` comparisons for `pick x xs`; each nonempty recursive tail step
   contributes one, regardless of its branch. State an independent size
   recurrence before proving its agreement with instrumented execution.
2. Instrument `F` with no selection charge at zero fuel or empty input. Its
   independent count specification satisfies `T(m,0)=T(0,n)=0` and
   `T(m+1,n+1)=m+T(m,n)`. Prove the measured algorithm has this count using
   select's actual remainder-length theorem; do not define the desired
   triangular answer as the instrumentation.
3. For full sorting, prove `2*T(n,n)=n*(n-1)`, with truncated Nat subtraction
   and explicit empty/singleton cases. The count is independent of input order.
   For `n≥2`, two-sided bounds such as `T(n,n)≤n²≤4*T(n,n)` justify quadratic
   comparison growth. Use `Resources.isBigO_of_nat_bound` for the corresponding
   cast asymptotic bounds; the same counts apply to sufficient extra fuel and
   to an explicitly instrumented `W` only after their count bridges are proved.
4. Compare against #1003's accepted insertion comparison model under the same
   charge convention. Its general upper bound is triangular; ascending and
   all-equal inputs use `n-1` insertion comparisons versus triangular selection
   comparisons (strictly fewer for `n≥3`). Insertion's descending worst case
   attains the triangular count. These facts support a qualified comparison,
   not “selection is always slower” or a measured wall-clock claim.

The comments about expensive imperative swaps, usual small-input preferences,
and the bubble-sort video are contextual advice, not source theorems about
every functional runtime. These algorithms do not execute in-place swaps.
Do not equate logical cons reconstruction with fresh heap allocation, physical
sharing, peak space, or GC. If adding constructor counts, name and instrument
that observation separately. `Resources.run` is available for actual successive
state workloads, but this one-shot recursion does not need a synthetic command
executor or an amortized-potential framework.

## Meaningful case intentions and statement review

- Preserve all four algorithm examples and the pair example in the table;
  combine independent expected calculations with public correctness, length,
  fuel-saturation, or well-founded-equation results. Add empty, singleton,
  exact-fuel, zero-fuel nonempty, and both comparison branches where existing
  cases do not already exercise them. There is no per-lemma case quota.
- Use the same five-element input to connect measured costs: fuel 3 has nine
  comparisons and full/excess fuel ten. Verify these through the measured
  recurrence/count theorem as well as the independent expectation.
- For records `A=(2,"a"), B=(2,"b"), C=(1,"c")`, comparing keys, check
  `S [A,B,C]=[C,B,A]`. The key-2 filtered observation reverses `[A,B]`, while
  permutation, KeySorted, and Nat key output `[1,2,2]` still hold. This refutes
  a generic stable contract; it is a property of the explicit key generalization.
- Separately prove selection fixes supplied key-sorted inputs by showing
  `pick x xs=(x,xs)` under the head lower bound. Combine with all-input
  sortedness to obtain idempotence. Instability does not refute these properties.
- Connect Nat output agreement to existing `insertionOn`/`sortOn` using actual
  source correctness and `List.Perm.eq_of_pairwise'`. For records, equality
  after mapping to keys is a weaker valid observation; do not claim full
  record equality or a cost identity from it. An erasure square can provide
  the existing observation/composition client for instrumentation.

Statement review must inspect source quantifiers, extra `n` parameters, both
length-equality orientations, input-to-output permutation, retained duplicates,
exact remainder reconstruction, adjacent-versus-Pairwise conversion, function
contents semantics, and all assumptions on comparisons. Check that minimum
results assert membership as well as bounds, insufficient fuel is not covered
by an unconditional permutation claim, and proposed complexity refers to the
measured recursion rather than merely to an extensionally equal library sort.

## Completion and preservation gates

Existing proofs leave concrete work: both source algorithms and their exact
bridges; all table wrappers and optional contents arguments; fuel saturation
and output length; source-specific measured execution/bounds; connected Nat,
record, and resource cases; and coverage of the language/prose qualifications.
Neither `insertionOn_spec` nor standard sorting-output uniqueness closes these.

After #1005 acceptance, use the existing implement/example-driven workflow:
record baseline; develop and review statements alongside meaningful clients;
integrate modules, public entrypoints, and exhaustive proof audit; perform the
applicable focused checks and ordinary isolated exact-candidate
`./check.sh --candidate HEAD`; obtain independent Standards and Spec review;
then run `./check.sh --verify-candidate HEAD` immediately before acceptance.
Use the pinned Nix environment and coordinator's current worker setting.
No admissions, new axioms, unsafe proof substitutions, or native proof shortcuts.
Failures and unresolved findings leave #1006 open. Update local coverage,
tickets, and evidence, then capture/upload/expose the durability checkpoint
before beginning #1007. This planning task starts no separate review loop.

## Read-only planning identities

No Lean/compiler/build or cache operation was run for this plan. Source reads
verified the names and hypotheses above; proposed declarations have not been
elaborated. These identities detect drift before implementation:

| Inspected file | SHA-256 |
| --- | --- |
| `../source/Selection.inventory.json` | `bd107b71a11702b61eae54c9a73b351d722bb2659e6d944b1d6f8c0785372371` |
| `1003-Sort.md` | `fcc06acf05245de79637600479006e3d4a98f8bdf85c2537f5e7451cf3042955` |
| `1004-1005-Multiplicity-plan.md` | `39eb5bf01936bc326298de880d83b87912902fe693d5b83fb187a4d05e5e6487` |
| `../source/SORTING-STABILITY-BOUNDARIES.md` | `dba97ea118b343c779d9d11feed6ca4e65c2ebc665454c1642970db4aca83b81` |
| `conaled/Applications/Sorting/Sort.lean` | `5acd7728aaaefdec121df797efafd7dae13476c820d4f85f4ada19868fa71218` |
| `conaled/Applications/Sorting/Stable.lean` | `288552150aa002c60ed06c74e69510112cf9b4e2f0045da3d98ca5c39264d881` |
| `conaled/Applications/Resources/Measured.lean` | `b5f76c8dfdb3cc9dd28a356bebd12787b3a7add61abba1022d474604a6979667` |
| `conaled/Applications/Resources/Growth.lean` | `5e252788c2365d3f9140288a1d51f2ef38270798419af40df8505590a7d20dcc` |
