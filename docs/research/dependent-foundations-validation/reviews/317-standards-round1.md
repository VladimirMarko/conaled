# Issue 317 Standards review, round 1

Outcome: **Passed**. No documented-standard violations or actionable heuristic findings. Findings count: 0; worst severity: none. This is the independent Standards axis only.

Reviewed base `bb77d67171e6cb610e43149394c8a9b9a0deab3f`, candidate `7b8c00ae171c8a0b6de696e42aaf8470ff1e7c96`, and their three-dot diff. The merge base is exactly the supplied base. The scope is all 22 changed files, comprising 3,265 added lines, with no exclusions. Candidate source was read with `git show`; the isolated checkout also resolves to the candidate and has empty short status. The three task commits are `c7ddcfc`, `d144e1a`, and `7b8c00a`.

The requirements reviewed were the saved `specs/317.json`, `specs/orchestration.md`, and `records/317-dispatch.md`. Applicable guidance included root AGENTS.md; README development, build/audit and experimental guidance; review-loop, architectural-quality and domain guidance; GLOSSARY.md; ADRs 0001 and 0010; language-direction and the preservation-contract inventory; code-review and its heuristics; example-driven-development statement review; and no-ai-slop. No applicable nested AGENTS.md, CODING_STANDARDS.md or CONTRIBUTING.md was present. This assigned review continued the existing implementation loop without spawning agents or editing source.

## Architecture and author obligations

The extension reuses the existing guarded contextual source and its semantic model. Inspection of unchanged `Comprehension.lean`, `ContextualOperations.lean` and `PathTransport/Model.lean` confirms that contextual pairing and extension were already present but object Sigma formation was absent.

`Sigma/Capability.lean:10` packages the new family and pack/unpack operations with their over-base and inverse laws. The eliminator is constructed from substitution along unpack. `split_type` at line 34 explicitly uses `pack_unpack`, while beta uses the opposite inverse. This is the documented full comprehension-isomorphism contract. No beta-only interpretation is claimed. Split uniqueness and injectivity are derived results, with arbitrary dependent motives and sections in their stated domains.

`Sigma/Stability.lean:9` adds formation and pack stability. Inverse, branch, pair and split naturality are proved from those laws and inherited comprehension/substitution. `sumMap_comp` at line 78 retains the family comparison between iterated and composite reindexing. `Sigma/Maps.lean:29` requires the primitive family and pack equations; `Map.split` at line 88 constructs the transported motive and branch and derives elimination preservation. Map identities and composition reuse the existing structural-map construction. These interfaces satisfy the architectural requirement to derive reusable preservation from the needed primitive laws.

`Sigma/SourceMaps.lean:15` extends the full existing ModelMap with one shared structural map, preserving the old contextual J boundary. Its partial homomorphism reuses `Contextual.partialHom` and `PartialHom.eval`. The definedness condition at line 144 and typed assumptions at line 219 preserve the existing restriction on raw junk equality. `Tm.interpret_map`, `TypedEquality.map`, `Tm.pair_map`, `Tm.split_map` and `splitDerivation_target` make this contract available through source typing. They do not require the proof author to supply a final preservation equation. The theory-independent semantic term-guard entry point also admits terms interpreted through the reindexing extension.

The source facades expose ordinary typing premises. `ReindexAuthoring.lean:391` reconstructs branch typing; lines 403 and 437 compose arbitrary substitutions while rebuilding dependent data; line 454 relates the successive split to the composite of the lifted arrows. Their proofs consume the generic admitted rules. The report distinguishes these source results from semantic canonical-composite comparison and from raw metavariable substitution. Repeated syntax transport proofs and facade wrappers do not establish an actionable duplication finding here: they preserve the interfaces of distinct admitted theories, and the consequential preservation arguments are shared.

## Formal methodology and checked uses

The implementation handoffs record the initial independently expected case, the missing connection to generic admission, statement review, and retained cases. Review of the declarations and their derivations confirms these connections:

- `Native.lean:15` and line 23 construct inhabited Capability and Stable instances. The varying `Fin(n+1)` family and motive exercise the generic split and beta results.
- `Examples/GuardedSigma.lean:70` obtains the exact selected index by interpreting the fixed source beta derivation. The smallest fiber and pair computation use the same dependent data.
- `Native.lean:141` derives selected-section preservation from the shared comparison theorem. The concrete target observation at line 149 follows from that preservation; inverse recovery at line 155 retains the whole selected section. Both dependent components and the motive change presentation.
- `Examples/GuardedSigmaReindexing.lean:135` and line 142 interpret the source successive/composite derivations with varying families and two order-sensitive substitutions. Intermediate motive and branch typing is reconstructed inside the source author interface.
- `Recovery.lean:19` retains the named dependent-action derivation with its transported source. Line 41 recovers that source's exact evaluation. The unchanged Memo definitions confirm the selected certificate and action being retained.
- `Composition.lean:75` validates the law-only second extension from the existing inverse laws. `Rejection.lean:36` rejects a false type equation with valid type endpoints, while line 60 separately rejects omission of the dependent-family guard.

Statement inspection covered quantifier scope, dependent context indices, the directions of substitutions and comparisons, equality versus object identity, selected-value content, and the separation of primitive assumptions from derived client conclusions. Native instances establish satisfiability for the intended examples. No circular preservation hypothesis or vacuous claimed positive example was found. Universal applications appropriately cover helper results without a per-declaration example quota.

The experiment is marked in Syntax and `Theory.lean:7`, with a resolving link to the dedicated research report. The report records the exact law classification, model-builder/extension-author/proof-author obligations, framework hypothesis assessment and unproved adequacy bridge. It explicitly limits all-model expansion, conservativity and higher adoption. Scoped continuations remain assigned to #289, #318, #321 and #322, within the coordinating programme. The supplied primary-source-check handoff documents the paper inspection; this Standards review assessed its consistency with the report and implemented boundary, without claiming to import those external metatheorems. No global preservation-interface retrofit is introduced.

## Validation

Status: **established for the reviewed candidate in incremental mode**. I inspected the completed evidence rather than rerunning compiler checks:

- `317-candidate-check.log` identifies Lean 4.35.0, passes source-policy/public coverage checks, checks all 1,085 integrated modules and the exhaustive proof audit, and records this exact candidate. The axiom union is only `propext`, `Classical.choice`, and `Quot.sound`.
- The same log hashes 3,252 artifacts before and after the build, with zero invalidated and zero inconsistent modules.
- `317-audit-regressions.log` records all four required fixtures passing.
- `317-verification.json` records the exact candidate, pinned dependencies, incremental mode and completion at `2026-11-05T02:21:39.293372+00:00`.
- `317-verify-candidate.log` reports a matching verification record; `317-final-status.log` and the current short status are empty. The acceptance script and coordinator handoff record execution through the development shell under the shared acceptance lock after writers stopped.

The earlier missing-output observation is documented as occurring during concurrent focused rebuilding. The handoff records subsequent exclusive completion and no observed corrupt/stale declaration; the final guarded acceptance reports no inconsistent outputs. This evidence does not establish a stale-artifact suspicion requiring fresh-mode acceptance. No tooling, toolchain or dependency configuration changes are in the diff. Focused logs are development evidence only. The coordinator must repeat immediate candidate verification before final acceptance, as required by the review procedure.

Base: `bb77d67171e6cb610e43149394c8a9b9a0deab3f`. Candidate: `7b8c00ae171c8a0b6de696e42aaf8470ff1e7c96`. Standards findings: **0**, worst severity **none**, outcome **Passed**.
