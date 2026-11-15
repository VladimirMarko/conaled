# Tail boundary correction 3 — full author source readback

This is a source-only correction within the existing XU03 and Chapter 2 review
loop. It is not a compiler result, final Standards/Spec review, acceptance or
new workflow. The fixed original unit base remains
`4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8`, original candidate
`a0597381f02eddd074ee96cabaa974f2062285f8`. The immediate correction base is
`ee2ea2406a014e43c355f93317455f27b90dd680`; fa86 and earlier corrections remain
in its reachable history. Root owns integration and validation after the live
central command actually closes.

## Exact inspected scope and evidence boundary

I read every line of the 247-line predecessor example, every line of the
120-line fixed actual diagnostic extraction (all 16 error headers), and the
complete new 85-line diff. The revised example is 261 lines. This assessment
covers the entire example file and all seven changed proof bodies. I read the
pinned definitions/theorems used below, not every proof in Mathlib or the full
unchanged XU03 core. Prior complete core/unit reviews remain retained by the
outer loop; this readback does not pretend to replace them.

The actual diagnostics belong to immutable central
`5398db774ed5ca9938d0562e379d757323e7a355`, whose example bytes equal the immediate
minimal correction base. They are copied from a fixed prefix of focused7 while
that aggregate command was still live. I did not poll or otherwise use its
execution handle. No later terminal success/failure is inferred here. The
source-only worktree was clean at ee2ea240 before editing.

Source invariants checked directly: all 25 theorem headers are byte-identical;
all seven definition blocks are byte-identical; imports, options and all six
anonymous measurable instances are byte-identical. Only
`Examples/PermutationTailBoundary.lean` changes. No core/main example, public
root, documentation, dependency, pin, linter option or proof-policy file changes.
These byte checks establish the bounded source scope, not proof correctness.

## Corrective derivations

### Actual selected/global first events

The old broad simp call rewrote the optional head of a map before the supplied
full-list equality could match. The actual diagnostic retained existential head
conditions and flagged the global-order simp argument as unused. The correction
first changes the set memberships into exactly their defining head propositions,
then rewrites the already established list observations. Ordinary `decide`
checks the resulting finite option facts. The same sample swap01 still has
inverse global list `[1,0,2,3]` and selected list `[0,2,3]`; selected head0,
global head1 and failure of global head0 are all retained. No new event meaning
or hypothesis is introduced, and no linter is disabled.

### Same finite support, structurally reducible enumeration

The five support decisions stopped at `counterPositions.permutations.toFinset`
or its deduplicated list. The pinned `List.permutations` implementation uses
`permutationsAux.rec`, a well-founded recursion; the pinned alternative
`List.permutations'` has ordinary structural list recursion. The existing
`List.permutations_perm_permutations' counterPositions` proves that the two
complete enumerations are permutations of one another.
`List.toFinset_eq_of_perm` therefore gives equality of the exact support Finsets.
The repair rewrites by that equality after the already existing universal-filter
normalization, then uses ordinary `decide` for the same finite table or membership
proposition. No new random law, independent draw, support assumption, reduction
axiom, native decision tactic or compiler shortcut is used.

The expected table can be checked independently over the six full orders:

| Full order | Selected head0? | Outside order | Joint contribution |
| --- | --- | --- | --- |
| `[0,1,2]` | yes | `[1,2]` | first joint event |
| `[0,2,1]` | yes | `[2,1]` | reversed joint event |
| `[1,0,2]` | no | `[1,2]` | none |
| `[1,2,0]` | no | `[1,2]` | none |
| `[2,0,1]` | yes | `[2,1]` | reversed joint event |
| `[2,1,0]` | no | `[2,1]` | none |

The first joint event is exactly one full-order fiber; the second is the disjoint
union of exactly two. The public whole-order fiber formula still supplies each
mass 1/6, giving joint masses 1/6 and 1/3. Enumeration equality changes neither
that use of the public law nor the conditioning event.

### Finite ENNReal arithmetic with explicit NNReal domain

The file opens scoped ENNReal but not NNReal; its earlier `ℝ≥0` annotations were
parsed as a comparison involving Type. The actual diagnostics report `LE Type`
and `OfNat Type 0`, followed by failed fraction rewrites. The repair spells the
intended coefficient type `NNReal` explicitly, with nonzero 6 or 3 proved by
`norm_num`. The pinned `ENNReal.coe_div` requires that exact nonzero premise.

Each arithmetic block uses `simp only` with the explicit two fraction coercion
identities, reverse `coe_add` or `coe_mul`, and `coe_inj`, then `norm_num` in
NNReal. This applies the intended finite coercion to every matching fraction.
The obligations are unchanged: 1/6+1/6=1/3, 2*(1/6)=1/3, and 2*(1/3)=2/3.
The preceding `cond_apply`, actual first-event mass1/2 and actual joint-event
masses are retained. Positivity/finiteness of these denominators is justified by
fixed nonzero natural numerals; no general ENNReal field law is assumed.

## Complete statement and connection readback

Every theorem below keeps its exact written header. New actual elaborated output
remains required by the outer loop; no statement-equivalence claim is made from
an uncompiled successor. “Unchanged” describes source bytes or proof bodies,
not a newly supplied successful check.

| Declaration | Intended statement, public connection and assessment |
| --- | --- |
| `swap01_global_order` | The inverse list of the actual swap is `[1,0,2,3]`; unchanged finite value computation. |
| `swap01_selected_order` | The actual selected projection is `[0,2,3]`; unchanged finite value computation. |
| `swap01_first_events` | Same swap belongs to selected-head0 and global-head1, but not global-head0; proof now consumes both prior full-list values explicitly. |
| `singleton_conditional_tail_mass` | Actual singleton observation has empty conditional tail of mass1 through `cond_tail_eq`; same singleton membership and complete original positions. |
| `empty_subset_none_mass` | Empty selected projection has optional head none with mass1; unchanged actual projection and original uniform sample. |
| `empty_subset_first_event` | Head0 event for an empty selected set is literally empty through `firstEvent_restrictedOrder_of_not_mem`. |
| `empty_subset_conditional_zero` | Conditioning the actual uniform sample on that empty event gives zero through `cond_firstEvent_restrictedOrder_of_not_mem`; no normalization to a nonempty target. |
| `outsider_first_event` | Label1 is outside the fixed selected set, so its actual head event is empty through the same public outsider law. |
| `outsider_conditional_zero` | The same outsider event gives the zero conditional measure; unchanged exact sample. |
| `empty_indices_none_mass` | Empty index type retains its identity permutation and no distinguished key; optional head is none with mass1. |
| `counterPositions_nodup` (private) | Concrete `[0,1,2]` is Nodup; unchanged finite premise for the public order/tail laws. |
| `counterPositions_complete` (private) | Every Fin3 index belongs to the same original positions; unchanged complete-enumeration premise. |
| `outside_subset_boundaries` | Outside set excludes0 but is not contained in selected erase0; unchanged witness for the consequential missing-containment boundary. |
| `counter_first_mass` | Actual selected-head0 event has original uniform mass1/2 through `uniformOn_firstEvent`. |
| `counter_full_mass` (private) | Each supported complete Fin3 output fiber has mass1/6 through `uniformOn_restrictedOrder_eq`; no resampled source. |
| `joint12_table` (private) | Over the exact supported full lists, head0 plus outside `[1,2]` is equivalent to full list `[0,1,2]`; only finite enumeration proof changes. |
| `joint21_table` (private) | Same support, reversed outside order gives precisely full lists `[0,2,1]` or `[2,0,1]`; only enumeration proof changes. |
| `counter_joint12` (private) | Actual source-event intersection equals the one full-output fiber through both deterministic `filter_restrictedOrder_of_subset` bridges and actual full support; unchanged proof. |
| `counter_joint21` (private) | Actual source-event intersection equals the union of two full-output fibers via the same complete positions/filter/support links; unchanged proof. |
| `full_fibers_disjoint` (private) | Distinct complete outputs cannot hold at one permutation; unchanged proof uses equality contradiction, retaining true disjointness required by measure_union. |
| `counter_joint12_mass` (private) | Exact first joint event has mass1/6; public full-fiber theorem retained, with support membership now rewritten through the equal structural enumeration. |
| `counter_joint21_mass` (private) | Disjoint two-fiber union has mass1/3; exact measure_union, both actual fiber masses and both memberships retained; finite arithmetic type is explicit. |
| `outside_order_12_mass` | Under the original sample conditioned on selected head0, the actual outside `[1,2]` projection has mass1/3; retained cond_apply and actual numerator/denominator, repaired finite arithmetic only. |
| `outside_order_21_mass` | Under that same conditional measure the reversed projection has mass2/3; retained original measure/events and finite arithmetic. |
| `outside_order_not_uniform` | Actual outside `[1,2]` mass differs from1/2; unchanged consequence of the previous public1/3 theorem, so excluding the head alone cannot replace containment. |

The seven definitions are also unchanged: swap01, counterPositions,
conditionSubset, outsideSubset, counterLaw, counterFirst and outsideConditional.
They use the existing permutation, ordinary list/finset, original uniform measure,
optional-head event and ordinary conditioning. All six measurable-space/singleton
instances remain scoped to the same Fin4, Fin3 and Empty permutation sample types.
No payload domain, equality/order hypothesis, universe, event, observation or
source normalization changes. The original 1/3-versus-2/3 mathematical expectation
is retained independently of compilation.

## Pinned primary API reads

All API reads came from the exact local pinned source available to root, without
compiler/cache commands or edits:

- `PermutationTail.lean`33–60: firstEvent is exactly optional-head equality.
- `PermutationOrder.lean`33–60: restrictedOrder maps the inverse permutation
  then filters; orders is the permutation support of the filtered positions.
- `Examples/PermutationOrder.lean`1–80: exact positions, selected set and
  complete-enumeration witnesses used by the example.
- Mathlib `Data/List/Defs.lean`145–254: permutation enumerators and dedup.
- Mathlib `Data/List/Permutation.lean`200–240 and360–389: public recursion facts
  and the exact permutation-equivalence theorem.
- Mathlib `Data/Finset/Dedup.lean`137–157: the exact explicit-argument
  `List.toFinset_eq_of_perm` signature and proof.
- Mathlib `Basic/ENNReal/Inv.lean`20–88: nonzero-denominator coercion laws.
- Mathlib `Basic/ENNReal/Basic.lean`470–530: finite coefficient coercion structure.
- Existing examples `PermutationMinimum.lean`65–100 and
  `ProbabilityCorrelation.lean`1–55: existing project uses of these coercions.

The complete governing REQUEST, CURRENT, STATUS, ticket INDEX, XU03 ticket and
229-line frozen requirements were read, along with AGENTS, implement,
example-driven-development and its worked example, the full review loop,
architectural/domain guidance, GLOSSARY and relevant ADR0001/0010. README124–307
covers the actual native-waived environment, normal/fresh acceptance and audit
rules. Existing full XU03 requirements, scope and findings are retained.

## Validation and handoff limits

No Lean/Lake/compiler/version, cache, checker, audit, candidate verification or
live-session command was run. No files in either live candidate tree were edited
or inspected as mutable build outputs. The pinned dependency source was read
only. `git diff --check` and exact source/header/definition identity checks pass;
these are source-scope checks only. Root must validate the exact integrated
successor, inspect all required actual types, continue both independent axes on
the full scope, complete the guarded audit and immediate candidate verification,
and preserve all required predecessor acceptances. Every compiler finding remains
pending actual confirmation of the proposed source repair.
