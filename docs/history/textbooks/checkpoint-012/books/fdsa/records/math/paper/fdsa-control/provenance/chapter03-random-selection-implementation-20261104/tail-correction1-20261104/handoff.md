# C03-RANDOM-TAIL-ELAB-001: proof-only successor

## Immutable candidate and gate boundary

- Candidate: `b6df3412d52b0a98f92f625a2289252a93004d20`.
- Tree: `eb6f5aa5b9c7d3724861ee47d949c25cf504c0bb`.
- Parent: `331178cac124394fd5c86da0877fa670463f3280`.
- Branch: `work/fdsa-ch03-random-selection`; clean after command-local ChatGPT commit.
- Commit: `fix(selection): normalize actual tail proof terms (#174)` (actual exit 0, tool `55f97f`).
- Fixed whole-task review base: `2da5708478a1d943a9214b5b386ec2db16cd9eca`.

This continues the existing original randomized-selection implementation and finding records. It is a source correction, with no author compiler, actual successor type output, full candidate validation, independent review, audit, or acceptance claim. Root remains the sole serial compiler.

## Actual failure preserved

The first tail attempt at parent331178 is CLOSED exit1, owned63086, terminalf1e7b1, root complete closure65dc61; complete author readaf26cf. Its full log is16485 bytes, SHA256`bcf17ac312f63f2020aa202a7effdbc2cb9a1f9e51e6a65084fb6b8e05ab1a66`; native16203 bytes, SHA256`842648c2a6d38e957a559754b7d6acb25af87002fc819ad14e453426b81c4240`. All14 run records and all146 earlier own records are hash-preserved. No result is inferred for the failed core's example dependency, and the older accepted verification record does not validate this candidate. Historical sessions are not resumed.

Checkpoint0130 was verified, uploaded, exposed, and explicitly released before editing. Its actual release and durability records were fully read in1d93b6 and are bound in starting-state.json.

## Exact patch

Only `Applications/Resources/RandomSelectionTail.lean` changes:14 insertions and6 deletions. The complete patch is `source.diff` (4414 bytes, SHA256`a5c59823676385fd885ae26e65bc28a49d074986f956c1cab17df07cf47ad85b`).

1. `nat_map_lintegral` adds `rfl` after the actual alpha-equivalent rewritten sum equality.
2. `run_activeSize_zero` adds `rfl` to its two actual projection/reduction goals, preserving both recursive and equal-branch semantics.
3. The two successor expectation recurrences remove only the commands that actually reported no-progress `dsimp only`.
4. The two absorbed expectation proofs use the implicit-argument `zero_le` term.
5. `residualLaw_markov` uses pinned `Set.mem_ofPred_eq`, replacing only its deprecated alias.
6. `scanLaw_tail` replaces the failed final `ac_rfl` with explicit `mul_assoc` followed by `mul_left_comm` in ENNReal.
7. `scanLaw_nil` adds the actual empty observation's definitional closure.

These are ten reported diagnostic sites in nine proof bodies (eight public theorems and one private theorem). The complete changed core was read in53a83a, unchanged examples ine162cb, and exact diff in4c1660. Pinned API sourceb14f87 confirms the association/commutation and Set alias.

## Full scope and case preservation

The cumulative ten-file scope remains209 public declarations and16 authored private helpers. All225 headers and surrounding implicit-context directives are exact; all23 computational definition bodies are exact. Imports, options, namespaces, sections, annotations, assumptions, numerical constants and natural-number domains are unchanged. Nine other files, including the entire tail example file and all eight earlier sources, are byte-identical. No linter suppression or forbidden proof escape was added.

The private `nat_map_lintegral` remains generic in the original carrier and appears before the ordered section. Its header gains no order, measurability, finiteness, or inhabited premise. All earlier private-context disclosures, including the drift helper's previously recorded local omitted order parameter, remain preserved.

The actual-run observations remain `activeSize` of the recorded trace and `residualWork = scanVolume(drop w trace)`. Time induction still uses the actual chosen strict child, with equal branches absorbed. The claim remains the exact non-strict event `Pr[W >= (4+w)*n] <= (3/4)^w` for naturalw and positiven. The source threshold stays `9*((4+w)*n)+2`, obtained from the same outcome's checked source tariff. No desired expectation/tail is a premise, and no unrelated larger-side process substitutes for the actual run.

All18 connected tail cases retain their complete statements and proofs: trace[(5,1),(1,0)] work6 and residuals6,1,0; actual two-key traces and size expectations2,1/2,0; residual expectations5/2,1/2,0; singleton and invalid-singleton absorption with source means9 and11; both duplicate occurrence draws and zero later residual; generic absorption/integrability; positive-input and valid-answer tails; zero excess; and the explicit empty pure0 law whose non-strict zero-threshold event has probability1 and fails the proposed upper3/4 atw1. `precommit-assessment.json` includes the exhaustive header inventory plus original statement and case assessments.

## Exact sources and root input

| File | Bytes | SHA256 | Git blob |
|---|---:|---|---|
| Tail core | 24208 | `f12fd0bef652f95d52154e7936658a4881e3b106045678fdcf749e7a23d99fe1` | `8b30d8cf47221ed6d409d8cfe658d69bf110d78a` |
| Tail examples (unchanged) | 8697 | `2678c1f6fd6cab99353562b050d641427c9b04b7648a30e751051d4f0f0d771e` | `682983d2bc4131cb684aad56358a335e9acf59ba` |

`Statements209-tail-correction1.lean` is byte-identical to the original full209-name input:11862 bytes, SHA256`5f3c2af90ccbd65dcdb7e91a555d5cbb2ae2a4579eaf2b9c3fd05f5c44c3c3df`. Its companion preparation binds the exact candidate/tree, ten source blobs, complete209-name ordering, imports and full-printing options. It has not been executed by the author.

Root focus targets remain:

```text
Applications.Resources.RandomSelectionTail
Examples.RandomSelectionTail
```

## Pending scope and hold

Endpoint-sequence probability1/n!, triangular worst-case attainment and an unbounded family, and general all-equal behavior remain pending. They have not been started in this correction. Pivot-policy obligations C03-078 through C03-080 remain with root/values. The inaccessible original Karp source limitation remains disclosed.

All ten source files and own provenance writes are now held pending root's actual focused terminal or explicit release.
