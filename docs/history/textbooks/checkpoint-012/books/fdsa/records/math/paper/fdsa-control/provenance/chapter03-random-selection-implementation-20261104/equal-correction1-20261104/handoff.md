# All-equal proof correction 1 — immutable handoff

## Candidate and actual boundary

- Finding: `C03-RANDOM-EQUAL-ELAB-001`.
- Candidate: `0fa60badfd353bcd6e22177d852d8d6399a2e0fe`.
- Tree: `fa1ec12150c30df3e12a06b15a24b71be10c504a`.
- Parent: `e31773b19073f913b6e0330a37c7426743b5af71`.
- Branch: `work/fdsa-ch03-random-selection`; clean.
- Commit: `fix(selection): normalize all-equal execution proofs (#174)`; actual exit 0, tool `9dacc7`, command-local ChatGPT identity.
- Fixed whole-task review base: `2da5708478a1d943a9214b5b386ec2db16cd9eca`.

This is a proof-only correction of six bodies in `Applications/Resources/RandomSelectionEqual.lean`: 26 insertions and 10 deletions. It preserves all 31 new declaration headers, 30 public claims, the one private helper and all 11 example statements/proofs. The cumulative scope remains 12 files, 239 public names, 17 authored private helpers and 23 computational definitions. All eleven other source files are byte-identical. No author compiler action, type output, focused successor pass or Chapter 3 acceptance is claimed.

## Actual failure retained

The previous pair at `e31773b` actually CLOSED exit 1: owned session 66212, terminal `9a053b`, root full closure `769729`. The complete outer log was read in `5eedc6`; closed, native, start, result and historical verification records were read in `6036ad`.

- Outer: 15,072 bytes; SHA-256 `ef7c00fd1bafa94247bc1dcb4dfac7d52b96a25728820b90395b509433bc1994`.
- Native: 14,788 bytes; SHA-256 `9355612a39e8bf78582b016ea05098d1b7ebb60cde7cc8cc774cb5276eca3f28`.
- Native body is exactly the outer body at byte offset 127.

Seven diagnostics occurred in six core proofs. The core build failed; examples were not compiled. The inherited verification record is for accepted `c1cefe4`, not this candidate. No historical session was polled. All 14 closed-run files, all 192 earlier own records, frozen specs and root's actual binding are hash-preserved. Root's original binding `3ab034` was completely read in `406117`; its full source and statement/case reads remain `224c2a` and `e3fb25`.

## Exact correction and statement preservation

| Proof | Correction | Preserved claim |
|---|---|---|
| Private `uniformIndex_map_atom` | Use pinned `tsum_ite_eq'` for the actual `if i = a` orientation. | The same generic injective pushforward mass `1/(n+1)`; no order or payload inhabitance assumption. |
| `stepRun_all_equal` | Remove redundant `List.filter_replicate` from the existing simp list. | Same measured occurrence lookup, partition, valid/invalid dispatch and `3*n+i+6` active cost. |
| `run_all_equal_cons` | Reduce `Function.comp_apply` in the existing valid branch. | Same actual `run_cons`, uniform occurrence traces, valid cost `3*n+i+6`, invalid empty continuation and cost `3*n+i+8`. |
| `run_replicate_valid` | Name the replicate tail, prove its member equality and length, substitute the exact length before applying the same cons law. | Every positive size and valid worker rank; identical finite map, result, trace and source cost. No new theorem premise. |
| `run_replicate_invalid` | The corresponding exact length substitution before the invalid cons law. | Every invalid worker rank, unchanged `none`, singleton active trace, occurrence law and empty-call tariff. |
| `run_all_equal_summary` | Expose the two source-cost projections with `change` before `omega`. | Same correct value, one active invocation, exact scan and sharp source inequalities `3*n+6 <= T <= 4*n+5`. |

The generic private helper remains before the Ordered section. No universe, variable, implicit binder, instance, namespace, import, option, linter, computational definition, theorem hypothesis or conclusion changed. The oriented pinned API was read from `Mathlib.Topology.Algebra.InfiniteSum.Basic` in `c509df`; its to-additive theorem covers `if i = a` exactly.

The complete corrected core and exact diff were read in `e295d3`; the unchanged examples were fully read in `ff7343`. `precommit-assessment.json` checks all 256 public/private headers and retained contexts, identifies exactly six changed proof bodies, and retains the full original statement and case assessments. Each of the original 11 empty/singleton/pair/negative-duplicate/invalid/five-copy/generic/linear-family/public-zero cases is byte-identical. The independent expected-case file still has its original preimplementation hash; no expected value or boundary was adjusted.

## Bindings and requested check

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| Corrected core | 11702 | `05abf888d8ef2ab6934a1ad90034ac12e07dd7c79f558828fc719bf3973e1dd2` |
| Unchanged examples | 3944 | `bde72c95157977decc9ab4b2f08264e8cc618a5b38f07e3108eaac2070a5d3dd` |
| Exact committed source diff | 4002 | `34845640ec667dae67f970b7ab3bf365418c37ed34753d77a751298924c57f87` |
| `Statements239-equal-correction1.lean` | 13639 | `02ff01193e8571b22f72047661cd7088bab4c19f196800bcc1e21139bbf931d0` |

Core Git blob: `8f6aee1ec143ea2a8a8f02902ea0625289aa0a9c`. Examples Git blob: `ef9e627d4e40468ec9da0818af172ef6a0c3dff3`. The explicit-@ input is byte-identical to stage06, including all 239 names in the same order and all printing options. Its new preparation binds this exact candidate/tree and all twelve source blobs. It is prepared input, not compiler evidence. The staged patch matched the retained diff exactly; both whitespace checks and the local commit exited 0.

Root alone should run the next newly named focused check:

```text
Applications.Resources.RandomSelectionEqual
Examples.RandomSelectionEqual
```

## Scope still open and hold

The universal C03-064 endpoint sequence remains mandatory for every arbitrary distinct input and every valid rank: minima while the rank is positive, then maxima; exact path probability `1/n!`, actual triangular scan attainment, an unbounded natural-input family, and actual source-cost transport. This correction adds none of that later source. The read-only API/math support received from the finished endpoint-support agent is author assistance, not independent review or proof evidence. C03-078 through C03-080 remain with root/values.

The original inaccessible Karp source remains disclosed as inaccessible. No weakened probability model, substituted majorant execution, desired-bound premise, invented source quotation or new source recovery is introduced.

All twelve source files and own provenance writes are now HELD pending root's actual successor terminal or explicit release.
