# Local10021: logical-history implementation handoff

Author: `/root/trace_reuse_map`, 2026-11-03. This continues root's existing
implementation loop; it does not create a new review loop or change any
chapter acceptance. Local10021 is the bounded persistent history/debit
foundation; the full source/execution correspondence remains10017.

## Inputs, ownership and current validation boundary

Requirements are `requirements/persistent-debit-foundation.md` version1,
SHA256 `2a89d7818d73e0b1b118ebf7d902a75afb2b6e25afaae6b9c7842d229964922f`.
The assignment uses `/workspace/scratch/ca9a61d0bf30/persistent-accounting`,
branch `pfds/persistent-accounting`, baseline
`3dd930c3e3989f3e5530463f3ac937a629551335`. The baseline was observed clean
before this author's edits. Other authors own their distinct new modules.

This author owns only:

- `Applications/Resources/Persistent/History.lean`
- `Examples/PersistentHistory.lean`
- This implementation handoff.

Current source hashes, frozen for focused round2:

| File | SHA256 |
| --- | --- |
| `Applications/Resources/Persistent/History.lean` | `f0f33917f728ef5e1999e58514f816ab7ba2386c5d66e69b315b4bc5079399d9` |
| `Examples/PersistentHistory.lean` | `ce16376024cd71f447ef722119287abb8384af8b59f99c0b1a100b379bd020e1` |

**No compiler/build has been run by this author.** Root-owned focused round1
compiled the unchanged core successfully, then failed the client on one linter
error and two finite-set normalization goals. The corrected client is now
frozen for round2; this module/client pair is not yet focused-green or accepted.
Root owns the validation queues. Requested focused target remains
`Examples.PersistentHistory`, importing the same core. Actual raw round1
evidence is retained in `validation/persistent-history-r1.json` and `.log`.
An eventual focused success cannot replace the exact isolated full build,
exhaustive audit, matching verification record, both independent full-scope
reviews and final verification.

The author read the repository agent, architectural/domain/glossary/ADR/language
guidance, the implementation-assignment rules, shared review procedure, and
example-driven-development skill including its worked example. No Git/ref/index,
entrypoint, repository documentation, compiler-output or other source changes
were made. The agreed API was preserved. Root explicitly approved the small
no-outgoing-edge helper requested by the debit author.

## Intended mathematics and public API

The graph is an ordinary Mathlib quiver. It assigns a type of arrows to each
ordered pair of vertices, preserving multiple uses with identical endpoints.
`Resources.Persistent.history v` is the set of `u` with a possibly empty
finite `Quiver.Path u v`. No finite universe, decidable vertex equality,
acyclicity, thinness, antisymmetry, single-predecessor or single-identity law
is imposed by this definition.

Public results:

- `history_refl`: the empty path puts each vertex in its own history.
- `history_of_path` and `history_of_edge`: retain the given path or one-edge
  witness as history membership.
- `history_trans`: arguments are `u ∈ history v` followed by
  `v ∈ history w`; composing their paths gives `u ∈ history w`.
- `history_eq_of_no_outgoing`: if every arrow out of `u` is impossible,
  `u ∈ history v` implies `u = v`. It follows by ordinary path induction;
  it does not require a finite graph or a reachability decision procedure.
- `HistoryClosed scope`: every history predecessor of a vertex in the
  finite scope is itself in scope. This is separate from raw graph data.
- `HistoryClosed.empty`, `.union`, `.inter`: elementary scope-closure laws.
  Only the finite union/intersection operations require decidable vertex
  equality. Closure is not claimed to be monotone under arbitrary supersets.
- `history_map`: an ordinary `Prefunctor V W` preserves history membership
  using Mathlib's `mapPath`. It does not claim reflection, injectivity, or
  history closure of an image in a larger graph.

The core imports the existing Mathlib path and finite-set interfaces plus
`Mathlib.Tactic.Common`; it does not implement another graph/path datatype.
The new layer makes no source evaluation, chronological-payment or runtime
cost claim. Concrete operation incidence extraction remains outside this
assignment.

## Independently chosen cases and their public connections

### Two-node cycle, loop and parallel uses

`Examples.PersistentHistory.Cycle` has vertices `left` and `right`, two
distinct arrows `forward₀` and `forward₁` from left to right, one backward
arrow and one loop at left. These are separate inductive constructors, so
their identity is retained before projecting to history membership.

Expected facts were fixed from this graph before proof construction:

1. Both forward arrows connect the same ordered pair, but are unequal.
2. Forward then backward is a path of length2; the loop is a path of length1.
3. Both vertices occur in each other's histories despite being unequal.
4. The full two-vertex scope is history-closed. The singleton containing
   only left is not: right is an explicit omitted predecessor.
5. Copying vertices into a wrapper and retaining the same arrow family
   preserves both cycle history memberships.

`parallel_uses` connects each distinct constructor through `history_of_edge`.
`roundTrip_history` uses the public `history_trans`; `roundTrip_length` uses
Mathlib's path-composition/length laws on the explicitly constructed path.
`loop_length_and_history` combines Mathlib's one-edge length theorem with
`history_of_edge`; `empty_path_history` separately exercises `history_refl`.
`history_is_not_antisymmetric` retains the distinct-vertex counterexample.
The open-scope example supplies the actual backward edge to `HistoryClosed`.
`copied_cycle` uses `history_map` with an actual `Prefunctor`.

The existence of a nonempty cycle path is deliberately distinct from the
empty self-path. None of these raw graph facts asserts a terminating source
execution around the cycle.

### Two inputs, two results and distinct identity labels

`Examples.PersistentHistory.Join` has two source vertices, a combining
operation, and two result vertices. Its four use arrows attach each source
to the combining node and that node to each result. An explicit natural
identity label distinguishes the sources/results and the combining node;
the labels impose no edge restriction.

Expected facts:

1. The source vertices are distinct, as are the result vertices.
2. The combining node has both source histories, and both result histories
   include both sources.
3. The second source (label1) occurs in the first result's history (label0).
4. Each source singleton is history-closed because no edge enters that
   source. Their union is the closed two-source scope; their intersection
   is empty.
5. Neither result is in its sibling's history: a shared predecessor is not
   a path from one result to the other.

`both_inputs` uses `history_of_edge`. `both_results_have_both_inputs` and
`history_crosses_identities` use `history_trans` on the actual two-edge
paths. A private client lemma proves source-singleton closure from absence
of incoming edges by examining the path; `input_scope_combinations` then
uses public `HistoryClosed.union` and `.inter`. Finally,
`results_are_incomparable` uses `history_eq_of_no_outgoing` with the concrete
impossibility of any edge leaving a result vertex. The debit author's later
incomparable-payment case can use the same public helper on its own labelled
graph, without importing this presentation example.

## Statement review

History direction was checked against the agreed source definition: an arrow
from `u` to `v` places `u` in `v`'s history, and reflexivity is intentional.
All history/path/map results retain arbitrary vertex and arrow universes.
No decidable equality or finiteness is smuggled into them. Finite scope
membership is the sole scope requirement; source histories themselves may
be infinite, so existence of a finite closed scope is not asserted generally.

The cycle example makes the absence of an antisymmetry/acyclicity restriction
nonvacuous. The full/open scope pair distinguishes representability of a graph
from admissibility of a particular accounted scope. The join case makes
multiple-input/result and cross-identity capacity concrete, and the sibling
counterexample checks that sharing a predecessor does not reverse history
direction. Map transport asserts only the forward implication justified by
mapping a path.

All expected facts remain fixed. Proof drafting used direct constructor,
path and finite-set reasoning; there was no manufactured compiler failure,
admission, extra axiom, native proof shortcut, budget increase or linter
suppression. The first root-owned check compiled the core and exposed only
the client diagnostics retained below; the corrected client remains uncompiled.
Root must preserve actual diagnostics before corrections and keep these source
inputs frozen during compilation.

## Focused validation and correction history

### Round1 — terminal failure, unchanged inputs

Root supplied raw `validation/persistent-history-r1.json` and `.log`, copied
byte-identically from its owned run. It ran2026-11-03T01:04:49.158854+00:00
through01:05:49.348147+00:00, terminal exit1, with inputs unchanged. Targets
were the core and connected client. Core History compiled10s; its module-import
advisories are retained in the raw log. The client failed32s on:

- An unnecessary `simpa` in the omitted-predecessor contradiction; the linter
  correctly reports that `simp at absent` already closes the goal.
- Failure to simplify the public union-closure conclusion's singleton-union
  scope to the independently expected two-element scope.
- Failure to simplify the public intersection-closure conclusion's two
  singleton scopes to the independently expected empty scope.

These are proof/linter diagnostics, not evidence against the expected graph
facts. The round1 client hash was
`b6df60dc755a388c1aeea27fdb76cada1f36b4abcee4cf9777faaa3058d05986`.
The core hash above is unchanged.

### Round2 candidate — corrections frozen, validation pending

The contradiction now uses the linter-requested `simp at absent`. The scope
combination proof separately establishes the two exact finite-set equalities
by ordinary kernel-checked `decide`, rewrites by them, and applies the same
public `HistoryClosed.union` and `.inter` theorems. This preserves both literal
expected scopes and the public API connections. No theorem statement, graph,
case expectation, option, import or core proof changed. No compiler/Git/entrypoint
action was performed by this author. Current source hashes are in the table
above; root must run the corrected focused candidate.

### Round2 result — terminal success, unchanged inputs

The preceding pending/uncompiled descriptions record the state before this
run; this result supersedes them. After completing the requested read-only
Observation author assistance, this author read the root-preserved round2
JSON and log. Root ran the same two focused targets at WIP commit
`dc16a3b457b0393bb94188269fa3749deef39657`, starting
2026-11-03T01:17:00.821372+00:00 and ending
2026-11-03T01:17:32.275972+00:00, with terminal exit0. The record confirms
both queued-input stability and final-input stability. History core was
replayed with the already retained Mathlib module-import advisories;
`Examples.PersistentHistory` built in24s. The build completed successfully
with639 jobs.

The raw retained evidence is:

| File | SHA256 |
| --- | --- |
| `validation/persistent-history-r2.json` | `f6961410604f42d81b998c005222e0ba460af0d2a1cc0b52ca1b92c0f8149e4e` |
| `validation/persistent-history-r2.log` | `8cf9aaaed8254cc8370fd920e5e2d39930ba2bfee2bf8bc1c83f9d0beb3575bc` |

The current core and client hashes were independently read after this run
and still match the record: respectively
`f0f33917f728ef5e1999e58514f816ab7ba2386c5d66e69b315b4bc5079399d9`
and `ce16376024cd71f447ef722119287abb8384af8b59f99c0b1a100b379bd020e1`.
No source correction followed round2. The failed round1 evidence remains
retained. This is focused development evidence only; it is neither a full
candidate check nor an independent acceptance review. Root retains ownership
of the complete check, audit, reviews, final verification and acceptance.
Only this handoff was appended by this author after the read-only assessment;
no compiler, source, entrypoint or Git action was performed.
