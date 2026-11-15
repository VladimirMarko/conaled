# Endpoint proof correction 1 — immutable handoff

## Candidate

- Finding: `C03-RANDOM-ENDPOINTS-ELAB-001`.
- Candidate: `56b46dc955c44057afc366359e4f6f28cfad6330`.
- Tree: `c78ee1ea8b55996744dd864804dde1b007306a2d`.
- Parent: `7950275f345d1077e23730e1975b6dac7460be87`.
- Branch: `work/fdsa-ch03-random-selection`; clean.
- Commit: `fix(selection): normalize singleton endpoint bucket (#174)`; actual exit 0, tool `1683ef`, command-local ChatGPT identity.
- Fixed whole-task review base: `2da5708478a1d943a9214b5b386ec2db16cd9eca`.

Only one proof changes in `Applications/Resources/RandomSelectionEndpoints.lean`: two inserted lines replace one line. The exact addition is `List.replicate_one` in the existing simp-only list; the other change is line wrapping.

## Actual failure and authorized correction

Endpoint attempt1 at parent `7950275` actually CLOSED exit 1: owned session 98749, terminal `5493a7`, root complete closure `e0bf5c`. The complete log, closure, terminal, recorder result and native records were read in `d862bf`.

- Outer log: 13,231 bytes, SHA-256 `4801a24182ed310d25eda308b61d1a1dc24b6a369b472b3882e7d74ae9e478a2`.
- Native log: 12,939 bytes, SHA-256 `6e2de25c927b454ed3382e2176634bd1c2d81c70b01af7674099898689af9048`.
- Native body matches exactly at outer byte offset 135.

The sole diagnostic was that `List.filter_eq`, after substituting count one, produced `List.replicate 1 p`, while the unchanged theorem target was `[p]`. The core failed; examples were not compiled. No old execution session was polled. The inherited verification is for accepted `c1cefe4`, not this candidate.

Checkpoint0133 was verified, uploaded and exposed, with release `8e5889` authorizing only this correction. Its release record was fully read in `9fc78b`. Root's complete previous source/claim/case binding was read in `2bc4a3`. All 228 earlier own provenance files and all 14 failed-run files are hash-preserved. The prior hold's 288 bindings were verified before editing.

## Exact changed claim and preservation

The statement remains:

```lean
theorem partition_equal_singleton_of_nodup (p : α) (xs : List α)
    (hxs : xs.Nodup) (hp : p ∈ xs) : (partition3 p xs).2.1 = [p]
```

It still covers every arbitrary ordered payload, every actual distinct list, and every pivot member. It adds no sortedness, inhabited-carrier or probability assumption. The same actual partition/filter/count argument proves the singleton equal bucket. The pinned normalization theorem is `List.replicate_one : List.replicate 1 a = [a]`, read directly at `Init/Data/List/Lemmas.lean:2199` in `4c48b4`.

All 27 endpoint and all 283 cumulative declaration headers and contexts are exact. All 24 definition bodies, all 17 private helpers, all imports/options/sections/omits, all 12 endpoint example statements and proofs, and the independent expected-case model/results are unchanged. The other 13 source files, including all 12 files preceding the endpoint stage, are byte-identical. No new scope or unrelated proof adjustment was made.

The complete corrected core and patch were read in `4c84ad`; unchanged examples retain their complete `2abd44` read. The exhaustive assessment (`b75a7c`) checks the exact one-string replacement, every retained header, all definitions and all source bindings, and preserves the original complete mathematical/private/case assessments.

## Exact bindings

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| Corrected endpoint core | 8643 | `1621c8f16d8c5a4621268ec115ac2cee6eb18fe1b936116cb50f6b641bd3be8e` |
| Exact committed patch | 904 | `07ff06290ba08729c66826d0c133907ce21c95b9f9dabcf06092ae3918c90a59` |
| `Statements266-endpoints-correction1.lean` | 15,352 | `61aec968e952e701066db6b5802fe87b2356a3c52bba4f533f0a4b865bc7bc33` |

Core Git blob: `e17dbcbdd83a20de00ed5c02dda7a3e7f5fe9e39`. All 266 explicit-@ names, order, printing options and input bytes are identical to stage07. The new preparation binds this exact candidate/tree and all 14 source blobs. This is prepared input, not actual type output. Both whitespace checks and the local commit exited 0; the committed patch matches its saved artifact exactly.

Root's next newly named sole serial focus:

```text
Applications.Resources.RandomSelectionEndpoints
Examples.RandomSelectionEndpoints
```

## Remaining scope and hold

The actual complete endpoint trace, exact `1/n!` mass, triangular scan attainment, unbounded Nat family and measured source-cost worst-case transport remain mandatory and unimplemented. Their universal quantifiers remain every arbitrary Nodup input and every valid worker rank. No probability or complexity premise is substituted for those conclusions. The original Karp access limitation remains unchanged.

No author Lean/Lake, cache/output/environment/dependency/profile action or canonical control edit occurred. The successor is uncompiled; no focused pass, actual type output, full check, audit, independent acceptance review, immediate verification or Chapter 3 acceptance is claimed.

All 14 source files and own provenance writes are now HELD pending root's actual focused terminal or explicit release.
