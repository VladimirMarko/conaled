# Stage 06: exact all-equal randomized executions

## Immutable candidate and pending root check

- Candidate: `e31773b19073f913b6e0330a37c7426743b5af71`.
- Tree: `f298f6d0d91e1f709879bfe1a0511bf419a04000`.
- Parent: `0b8006f150cdb1aa9c76f5cf80eededca4417e81`.
- Branch: `work/fdsa-ch03-random-selection`; clean.
- Commit: `feat(selection): characterize all-equal random executions (#174)`.
- Actual commit exit: 0; tool `bb9af4`; command-local ChatGPT identity.
- Fixed whole-task review base: `2da5708478a1d943a9214b5b386ec2db16cd9eca`.

Two additive files, 343 lines, provide 19 core and 11 example public theorems and one private helper. There are no new computational definitions or replacement selector. Cumulative scope is 12 files, 239 public names, 17 authored private helpers, and the same 23 computational definitions. The new pair is uncompiled. Root alone runs Lean/Lake, types, checks and audits; this handoff supplies no Chapter 3 acceptance claim.

## Prior evidence and frozen scope

The previous tail pair actually passed at parent `0b8006f`: owned 30827, CLOSED exit 0, terminal `21cdf7`, root complete closure `ab0c36`, full author read `1193e8`. Both core and examples Built. Full log: 10,297 bytes, SHA-256 `361a427be37b3470e5ce9298afaa46e716aca35ca0d8e11ecea8ea9194d79614`; native 10,015 bytes, SHA-256 `d97ab34b4eb4205a7491bf27351fe4bd61dfd47862d33e3f88c777d8563fd6f5`. This is focused evidence only.

Checkpoint 0131's verified upload/exposure and explicit release were read in `1193e8`. All 179 earlier own records, all actual tail-pass records, frozen obligations/plan and release are hash-preserved. Earlier failed and interrupted histories remain intact. All ten earlier sources are byte-identical, preserving all 225 old declaration headers, contexts and proofs.

The full frozen 83-row inventory was reread in `87e1c5`, `f992da`, `55c0b0`; the full proof plan in `55c0b0`, `9e8d07`, `5fef19`. Pinned book p.35 and its whole-PDF SHA-256 were read/verified in `2d0f2e`. The original inaccessible Karp source remains explicitly inaccessible; no invented source recovery or quotations are introduced.

## Mathematical scope and source connection

This stage addresses the general all-equal part of C03-065 and supplies connected C03-060/062/074/075/077 evidence.

`stepRun_all_equal` derives the exact branch from the measured lookup, existing partition specification, and actual `stepRun_eq`. If every input member equals `x`, the chosen pivot is `x`, both strict blocks are empty, and the equal block is the entire input. Its active cost is `3*m+i+6`, with actual length `m` and occurrence index `i`.

`run_all_equal_cons` consumes the actual `run_cons` equation. A valid rank returns immediately. An invalid worker rank executes the existing empty continuation, adding its two calls and returning `none`; its total cost is `3*m+i+8`. Both retain the actual singleton active trace `[(m,i)]`. Valid and invalid replicate laws and exact support characterizations retain each occurrence separately.

The two atom theorems give each complete recorded occurrence outcome mass `1/m`, obtained from the real uniform-index map law and the injectivity of its source/index observation. Equal payload values do not collapse different traces into a uniform distribution over distinct values. The single private helper is a generic injective pushforward identity before the ordered section, with no payload order, measurability, finiteness or inhabited premise. Its injectivity premise is proved at each use.

The scan law is `pure m` for every natural input size and worker rank, including empty and invalid cases. Source marginals retain lookup-cost variation. The lower and real scan expectations equal `m`, derived from the same actual marginal. The general memberwise-equal list theorem does not require a replicate syntax. For every valid rank and supported outcome it gives exactly one active invocation, exact scan `m`, source bounds `3*m+6 <= T <= 4*m+5`, and zero active size and residual work at every later time.

For every `m >= 2`, all supported all-equal outcomes have scan `m < m*(m+1)/2`. This is the required counterbehavior to an incorrectly universal quadratic lower claim. It does not weaken any previously proved universal expectation/tail bound or discharge the existence of distinct-input worst paths.

## Cases computed before proofs

`expected-cases.json` was saved before source creation in `3f0755`. An independent exact finite model counts the actual length, lookup and recursive one-pass partition calls and enumerates the choice tree; it does not invoke Lean or assign the desired costs. It checked sizes 0 through 6 and ranks 0 through `m+2`, with ten fully recorded illustrative cases. These calculations are expected values, not universal proof or compiler credit.

The 11 checked-source example targets retain:

- Empty worker calls: `none`, empty trace, source 2, scan and scan mean 0.
- Singleton: valid rank 0 costs 9; invalid rank 1 costs 11.
- Either valid rank of `[x,x]`: two occurrence traces and source `12+i`.
- Three negative equal integers: valid first/last atoms cost 15 and 17 with mass 1/3 each; the last invalid atom costs 19 with mass 1/3.
- Five copies of 4: pure scan 5 and both scan means 5 at every worker rank; valid middle-rank source law `21+i` on `Fin 5`.
- Arbitrary memberwise-equal input: one active call, exact scan, linear source upper bound, and all later observations zero.
- Every natural size at least 2: the equal family lies strictly below the triangular maximum.
- Public rank zero: unchanged free `none` boundary, distinguished from worker rank zero.

The complete two new sources were read in `4db99c`. `precommit-assessment.json` inventories every new public/private header, its surrounding context, each statement/quantifier group and every example connection. All cases include the original metric and boundary conditions.

## Source and explicit type-program binding

| File | Bytes | SHA-256 | Git blob |
|---|---:|---|---|
| RandomSelectionEqual core | 11242 | `0b66aac89d0f75c36b6543d9e8b37bda0b2d145a5f820938313372c49a6d552c` | `fafe639ca66fffcc7a33af70e058b98e23272efa` |
| RandomSelectionEqual examples | 3944 | `bde72c95157977decc9ab4b2f08264e8cc618a5b38f07e3108eaac2070a5d3dd` | `ef9e627d4e40468ec9da0818af172ef6a0c3dff3` |

The exact two-file patch is `source.diff`, 15,974 bytes, SHA-256 `08d64a60a4012eaeba34b45e22464552246e579a35e3fecb9cd28ab25144b018`. Both no-index capture exits were the expected 1 for differences; they are not failed validation results. The staged patch matches this exact artifact and its whitespace check exited 0.

`Statements239-stage06.lean`: 13,639 bytes, SHA-256 `02ff01193e8571b22f72047661cd7088bab4c19f196800bcc1e21139bbf931d0`. All old 209 explicit `@` names remain in exact order; the 19 core and 11 example names follow. Full-printing options are unchanged. The preparation binds exact candidate/tree, all twelve source blobs and all names. It is prepared input, not actual type output.

Root's focused targets:

```text
Applications.Resources.RandomSelectionEqual
Examples.RandomSelectionEqual
```

## Remaining obligations and hold

C03-064 still requires, for **every distinct input and every valid target rank**, the specified endpoint sequence (minima while target rank is positive, then maxima), exact probability `1/n!`, triangular scan attainment, an unbounded natural-input family, and source-cost worst-case transport. This stage neither narrows that quantifier to endpoint target ranks nor claims it complete. C03-078 through C03-080 remain with root/values.

All twelve source files and own provenance writes are held pending root's actual focused terminal or explicit release.
