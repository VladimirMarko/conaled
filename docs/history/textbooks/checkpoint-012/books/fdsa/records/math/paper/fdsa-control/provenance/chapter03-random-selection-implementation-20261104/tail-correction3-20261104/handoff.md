# C03-RANDOM-TAIL-ELAB-003: pinned conditional theorem names

## Immutable successor

- Candidate: `0b8006f150cdb1aa9c76f5cf80eededca4417e81`.
- Tree: `1f499737b1a9658e8901940d803f5c7ca6d7ad8d`.
- Parent: `831b6df2daeb7278581bdd05f0d1f6aca8a5be39`.
- Branch: `work/fdsa-ch03-random-selection`; clean.
- Commit: `fix(selection): use pinned conditional theorem names (#174)`.
- Actual commit exit: 0, tool `f687ef`, command-local ChatGPT identity.
- Fixed whole-task review base: `2da5708478a1d943a9214b5b386ec2db16cd9eca`.

Root remains the sole compiler. This continues the original implementation and finding records; it creates no new acceptance/review loop. No successor compilation, actual type output, complete candidate check, audit, independent review, or acceptance is claimed.

## Actual failure and exact correction

The entire third tail log, reconciliation, and terminal were read in `c685f5`. Actual candidate was the parent above, owned session 8306, CLOSED exit 1, terminal `ee2b0a`, root complete closure `66796a`. Full log: 12,781 bytes, SHA-256 `3079a173e67cb649a27526029198bf7677e0ee848c1390554a931b085b1e0288`. Native log: 12,499 bytes, SHA-256 `65a27fa591c624ca977b307d8c90f83f1177d8e1bdfc4988f640ca94a957ac54`. Only reported core errors were the deprecated names `if_pos` and `if_neg`. Examples marked Ran do not establish a pair pass from this failed exit. The older verification record is not successor validation.

The pinned Lean 4.35.0 `Init/Core.lean` declarations were read in `3405ac`. They show the deprecated names as aliases of the replacements with the same proposition arguments. Only two names change inside private `nat_map_lintegral`:

```diff
-      · simp only [if_pos h]
-      · simp only [if_neg h]
+      · simp only [ite_eq_left h]
+      · simp only [ite_eq_right h]
```

The complete Git patch is `source.diff`: 732 bytes, SHA-256 `487397bd99397f40cce70aabe3342cc604884a2921a4b9471cc0ac5685f1c70d`. It was read in `a31b65`; the complete changed private proof in `68d811`. Exact byte comparison verifies that the core differs from its fully read parent (`71a951`) only by these two replacements.

## Preservation and full inventory

All 209 public headers, 16 authored private headers and contexts, and 23 computational definitions remain exact. No imports, options, sections, universes, variables, assumptions, constants, event comparisons, proof gates, or executable laws changed. No warning or linter suppression was introduced. Nine other files are byte-identical, including all eight earlier sources and the complete tail examples. The exhaustive 225-declaration inventory and full original statement/case assessment are retained in `precommit-assessment.json`.

The private marginal theorem retains its generic carrier and unchanged proposition; it still proves pointwise equality for the two decidability instances through the same true/false cases. No context assumption was added. The actual chosen-child recurrence, absorbing zero, residual drop observation, natural-excess non-strict tail for positive length, exact `(3/4)^w` bound, source threshold `9*((4+w)*n)+2`, and empty-input countercase remain unchanged. No desired expectation or tail is a premise.

Every statement and proof in the 18 tail examples remains exact: finite trace work and residual values; both actual two-key traces and size/residual expectations; singleton and invalid-rank singleton source means; duplicate occurrence draws and later absorption; generic absorption/integrability; positive-input and valid-answer tails; zero excess; and the empty pure-zero law with probability-one non-strict zero threshold and its excess-one countercase. Every older example is also exact.

All 168 earlier own provenance records and all 42 records from the three failed tail runs are hash-preserved. Root's prior complete binding (`f692f1`) is preserved as `chapter03-focused-continuation-20261104/random-tail-bindings-before-attempt3.json`, fully read in `137c04`. Frozen obligations and proof plan remain unchanged.

## Candidate source and explicit input

Tail core: 24400 bytes, SHA-256 `76ea201bc310b816f844e45422ecaf75d2d060202d1e391681affd558db99725`, Git blob `51ffc050d43ae7642b7b94427d3251b61621c6d7`. All ten source hashes/blobs are bound in `candidate.json` and the statement-input preparation.

`Statements209-tail-correction3.lean` is byte-identical to the original full input and both earlier corrections: 11,862 bytes, SHA-256 `5f3c2af90ccbd65dcdb7e91a555d5cbb2ae2a4579eaf2b9c3fd05f5c44c3c3df`. Its companion preparation binds the candidate, tree, all ten source blobs, all 209 explicit `@` names in exact order, unchanged imports, and unchanged full-printing options. No author execution occurred.

Root's focused targets:

```text
Applications.Resources.RandomSelectionTail
Examples.RandomSelectionTail
```

## Hold and remaining scope

All ten source files and own provenance writes are held for root's actual terminal or explicit release. Endpoint-sequence probability 1/n!, triangular worst-case attainment and an unbounded family, and general all-equal behavior remain pending and were not started here. C03-078 through C03-080 remain with root/values. The original Karp-source access limitation remains disclosed.
