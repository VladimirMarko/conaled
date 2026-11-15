# C03-RANDOM-TAIL-ELAB-002: three-proof correction

## Immutable successor

- Candidate: `831b6df2daeb7278581bdd05f0d1f6aca8a5be39`.
- Tree: `3ea411e7e0ad4060ecbe6832b6cb06eee6419f0e`.
- Parent: `b6df3412d52b0a98f92f625a2289252a93004d20`.
- Branch: `work/fdsa-ch03-random-selection`; clean.
- Commit: `fix(selection): reconcile tail marginal and absorption proofs (#174)`.
- Commit actual exit: 0; tool result `82d5ea`; command-local ChatGPT identity.
- Fixed whole-task review base: `2da5708478a1d943a9214b5b386ec2db16cd9eca`.

This is a correction within the existing original implementation/review loop. Root remains the sole compiler. No successor compilation, type extraction, complete check, audit, independent review, or acceptance is claimed.

## Actual evidence

Tail attempt 2 at the parent is CLOSED exit 1: owned session 66722, terminal `65425e`, root full closure `e81961`. The entire closed log, reconciliation, and terminal were read in `e07b4d`. Full log: 14,049 bytes, SHA-256 `5a4646e66b3b17cbbe7c807a6b8ca75e4d7123d2778361b899d89a59b683555f`. Native log: 13,767 bytes, SHA-256 `ba90e039190a66afc2972976e5b20e82ec6f787d5fbe1564e82eac5f8bca24dc`. All 28 records of the two failed tail attempts and all 157 earlier own records are preserved by hash.

The actual result reported exactly three core proof errors. Examples have no successful build established by this failed run. The old accepted verification record remains evidence for its own candidate, not this one. No historical session is resumed.

## Complete patch and rationale

Only the tail core changes: 8 insertions and 3 deletions across three proof bodies. `source.diff` is the complete patch, 2,021 bytes, SHA-256 `2283bd10a4cb66d30999fa232257b3d1693b0571a7b1441e184cb03bbe918390`.

1. In private `nat_map_lintegral`, the old `rfl` exposed different `Classical.propDecidable` and `instDecidableEqNat` instances in two if-expressions for the same proposition. Multiplication congruence, pointwise `tsum_congr`, and cases on `n = f result` now identify their values using `if_pos` or `if_neg`. This proves extensional equality without changing either probability law or adding a premise.
2. In `sizeExpectation_succ_cons`, the equal branch explicitly simplifies with `activeSize_succ_cons`, `activeSize_nil`, and `Nat.cast_zero`.
3. In `residualExpectation_succ_cons`, the equal branch explicitly simplifies with `residualWork_succ_cons`, `residualWork_nil`, and `Nat.cast_zero`.

The complete changed core was read in `71a951`; the full diff in `964999`. The unchanged examples' full read `e162cb` remains bound by their identical hash.

## Complete mathematical and case preservation

The ten-file scope retains exactly 209 public declarations, 16 authored private helpers, and 23 computational definitions. All 225 declaration headers and surrounding implicit-context directives are identical. All computational definition bodies, imports, options, namespaces, sections, annotations, assumptions, constants, and domains remain exact. Nine other files are byte-identical, including all eight previously passing sources and the complete tail examples. No forbidden proof escape or linter suppression was added. The private marginal helper still has its original generic carrier and remains before the ordered section; no context parameter was added or removed.

The actual recursive run, fresh uniform current-occurrence draw, selected strict child, equal-branch absorption, active size, and drop-based residual work are unchanged. The tail remains the non-strict event `Pr[W >= (4+w)*n] <= (3/4)^w`, with natural `w` and `n > 0`. The same-run source threshold remains `9*((4+w)*n)+2`. No desired expectation/tail is assumed, and no independent-size or larger-side surrogate replaces the actual process.

All 18 tail examples retain their statements and proofs: the finite trace with work 6 and residuals 6, 1, 0; the two actual distinct-key traces; size expectations 2, 1/2, 0 and residual expectations 5/2, 1/2, 0; singleton and invalid-singleton absorption with source means 9 and 11; both equal-occurrence draws and zero later work; generic absorption and integrability; positive-input and valid-answer tails; zero excess; and empty input's pure-zero scan law, event probability 1, and explicit failure at excess 1. Earlier examples are also exact. `precommit-assessment.json` includes every declaration header and the retained original claim and case assessments.

## Source and explicit input binding

| File | Bytes | SHA-256 | Git blob |
|---|---:|---|---|
| Tail core | 24389 | `111f9aabb7cb6b95c686aedb12f6808932b1f661549063e701fe3ef65506c7e7` | `4d94782b68bc2226d1e0d7c0670cced404f23d6b` |
| Tail examples | 8697 | `2678c1f6fd6cab99353562b050d641427c9b04b7648a30e751051d4f0f0d771e` | `682983d2bc4131cb684aad56358a335e9acf59ba` |

`Statements209-tail-correction2.lean` is byte-identical to the complete original input: 11,862 bytes, SHA-256 `5f3c2af90ccbd65dcdb7e91a555d5cbb2ae2a4579eaf2b9c3fd05f5c44c3c3df`. Its preparation record binds this candidate and tree to all ten source blobs, all 209 explicit `@` names in exact order, the same imports, and the same full-printing options. It has not been executed by the author.

Root's focused targets remain:

```text
Applications.Resources.RandomSelectionTail
Examples.RandomSelectionTail
```

## Hold and remaining scope

All ten source files and own provenance writes are held pending root's actual terminal or explicit release. Endpoint-sequence probability 1/n!, triangular worst-case attainment and an unbounded family, and general all-equal behavior remain pending and have not been started here. C03-078 through C03-080 remain with root/values. The inaccessible original Karp-source limitation remains preserved.
