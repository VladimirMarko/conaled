# External Lean VFA reuse survey

Status: **advisory, unaccepted research**. Observed 2026-11-02 UTC. No external
formal module was copied, compiled, or selected for integration. This note does
not change the chapter plans, source pin, chapter order, or acceptance gates.

## Result

This bounded search did **not establish a complete, or substantial admission-free,
Lean 4 port of VFA** suitable for bulk reuse. It found a concrete small proof
lead in `samth/waterfall`, an exercise-bearing translation in
`Ghost-Silver/SF-lean4`, and the broader Software Foundations translation
`plclub/sf-in-lean`. This is a limit of the inspected evidence, not a claim that
no other port exists.

## Candidates and provenance

All repository source URLs below use movable `main`. A full commit identity for
the inspected pages could not be retrieved; none is a frozen dependency pin.

| Repository | Revision and toolchain evidence | License evidence | Classification |
| --- | --- | --- | --- |
| [samth/waterfall](https://github.com/samth/waterfall) | README advertises release `v0.2.0`; inspected [lean-toolchain](https://github.com/samth/waterfall/blob/main/lean-toolchain) is `leanprover/lean4:v4.33.1`. [Reservoir](https://reservoir.lean-lang.org/@samth/waterfall) separately lists short revision `12be67f`; this was not established as the commit of the inspected `main` files. | Actual [LICENSE](https://github.com/samth/waterfall/blob/main/LICENSE) says Apache License 2.0. | Proof-search library with concrete VFA examples; broader benchmark coverage is not established chapter coverage. |
| [Ghost-Silver/SF-lean4](https://github.com/Ghost-Silver/SF-lean4) | `main`, full SHA unavailable. [lean-toolchain](https://github.com/Ghost-Silver/SF-lean4/blob/main/lean-toolchain) is `leanprover/lean4:v4.35.0`. | README acknowledges the original tutorial's license, but its project license paragraph supplies no specific license identifier or grant. Reuse permission was not established by this inspection. | README lists all 17 VFA chapter files and explicitly retains exercise `sorry` placeholders. Its advertised translation/audit completion cannot establish proved coverage. |
| [plclub/sf-in-lean](https://github.com/plclub/sf-in-lean) | `main`, full SHA unavailable. [lean-toolchain](https://github.com/plclub/sf-in-lean/blob/main/lean-toolchain) is `leanprover/lean4:v4.34.0`. | Repository page identifies Apache-2.0; the license text was not separately audited here. | Inspected top-level directories include `LF`, `HL`, `TS`, compatibility/meta support, and `old`. No actual VFA proof source was identified in that bounded view. This does not rule out other paths or branches. |

## Concrete proof lead

The actual [Tutorial/Examples.lean](https://github.com/samth/waterfall/blob/main/Tutorial/Examples.lean)
contains the following public declarations:

| Namespace | Declarations | Potential use |
| --- | --- | --- |
| `waterfall.Examples.Sorting` | `insert_sorted`, `sort_sorted`, `insert_perm`, `sort_perm`, `sort_correct` | Nat insertion sort with both adjacent-order and occurrence-permutation guarantees. The insertion-result matching pattern helps instantiate the permutation helper at the recursive sorted tail. |
| `waterfall.Examples.TreeTraversal` | `fast_elements_helper`, `fast_elements_correct` | Generalize over the accumulator, then specialize to the empty accumulator. No BST ordering invariant is required for this value equivalence. |

The definitions use the VFA-shaped insertion branch and recursive sort, and the
same accumulator traversal recurrence. The displayed proofs use `waterfall`;
no `sorry` appears in this inspected file. Its only import is `waterfall`, and
the file expressly excludes benchmark assumptions and earlier case-study
proof imports. **Imported axioms and proof terms were not audited, and none of
these scripts was run on conaled's Lean 4.35.0.** This provides proof ideas, not
validated conaled declarations or a chapter-completion claim.

Local comparison used the pinned VFA 2.1 source, not an assumed equivalence of
the projects' book editions:

| Local source | SHA256 | Compared locations |
| --- | --- | --- |
| `reference/vfa/vfa/Sort.v` | `aeaf646d3b7e4dd88cb5d6dba9d35ae5714e5451c154d90de499bb09a32a7d33` | Lines 30–40: insertion and right-recursive insertion sort. |
| `reference/vfa/vfa/SearchTree.v` | `44b9464a10e8c9e3222530f6f26be45bd44d1c0568deb1710417618706fae61d` | Lines 517–521 and 814–835: flattening, accumulator traversal, and generalized helper. |

The source archive is [VFA 2.1](https://softwarefoundations.cis.upenn.edu/vfa-2.1/vfa.tgz),
SHA256 `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
The external tutorial links `vfa-current` rather than declaring this archive
identity. The checked recurrence correspondence is narrower than whole-source
fidelity. It supplies neither the full sorting-specification exercises nor the
tree representation/lookup obligations, measured resource results, or chapter
integration required by the local plans.

The waterfall [README](https://github.com/samth/waterfall#software-foundations)
reports 509 VFA goals across 15 chapters, with 315 baseline, 402 search, and 357
committed-mode successes. These are reported benchmark results. The benchmark
source, dependency assumptions, goal translations, and axiom closure were not
audited here; the counts are not proved chapter totals. The README also says
`waterfall?` can suggest ordinary Lean proof commands. At the relevant chapter,
that is a possible proof-recipe lead, not a recommendation to add a dependency
or change the current toolchain, and no saving in build time is established.

## Limits and disposition

Four search queries were used, across two search engines:

- `"Verified Functional Algorithms" "Lean" github`
- `"VFA" "Lean4" formalization`
- `"SF-lean4" github VFA`
- `"Verified Functional Algorithms" "Lean" github formalization -awesome`

Promising primary repository/README/source/toolchain/license pages were then
opened. GitHub history/tree, raw-source, and some chapter-page requests were
unavailable through the web reader. One bounded direct API attempt for the three
repositories' `main` refs failed DNS resolution. In particular, the requested
[Ghost-Silver Sort](https://github.com/Ghost-Silver/SF-lean4/blob/main/SFLean4/VFA/Sort.lean)
and [Binom](https://github.com/Ghost-Silver/SF-lean4/blob/main/SFLean4/VFA/Binom.lean)
pages were not readable: no theorem-level admission count or source-fidelity
audit of those files is claimed. The README's explicit exercise-hole policy is
the evidence for its classification. No repositories were cloned, no external
code executed, and no active validation inputs or caches inspected.

The concrete next use, when the chapter order permits, is to consult the two
small waterfall examples while developing the corresponding local proofs.
Any code reuse still needs an immutable external revision, applicable license
and attribution, statement/source comparison, conaled abstraction integration,
and normal compilation and axiom review. Independent proof scripts cannot
replace the pinned book's methods, local exercise inventory, meaningful clients,
resource-model obligations, full guarded build, audit/regression, or independent
chapter reviews. No candidate is approved for wholesale import, and this note
opens no additional implementation or review workflow.
