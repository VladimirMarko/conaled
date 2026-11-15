# Local #1023: staged positive binary key observations

Status: **the complete initial draft passed its sole focused compiler invocation** on 2026-11-02. Independent bounded review is pending with the parent workflow. This is cross-cutting preparation within the existing implementation loop; no chapter, integrated source, ticket, or full candidate is accepted here.

The complete deliverable is `VFAStaging/PositiveKeys.lean`: 43 named theorems and 9 definitions/abbreviations, including its cases and two plain equivalences. All declarations are under `VFAStaging.PositiveKeys` (cases under `.Examples`). Main and candidate were both `de575a81266ac98194c7c5c83e91628098aac92e` when preparation recorded their identities. Only this staging folder was written.

## Intended statements and existing reuse

The first independent boundary is the book's key convention **Nat 0 → positive one → Nat 0**. This requires a shifted observation distinct from a positive value's ordinary numeric interpretation. The general laws were developed around that boundary, then connected to distinct small keys, the source's constructor ten, comparator branches, and an arbitrary observation family. Existing theorems discharged the obligations directly; no artificial failing proof was introduced. The specification authorized one complete-draft compile, so cases and general results were checked together.

| Mathematical obligation | Staged declarations and exact reuse |
| --- | --- |
| xH/one has value 1; xO/bit0 has value `0 + 2*n`; xI/bit1 has value `1 + 2*n`, for arbitrary subtrees | `numeric_one`, `numeric_bit0`, `numeric_bit1`; reuse `PosNum.cast_one'`, `cast_bit0`, `cast_bit1` from `Mathlib/Data/Num/Lemmas.lean:34–46`. No second binary datatype. |
| Every binary value is positive, hence at least 1; numeric equality identifies the binary value | `numeric_pos`, `one_le_numeric`, `numeric_injective`; reuse `PosNum.to_nat_pos` (line 112) and `to_nat_inj` (line 452). |
| PNat retains numeric value with a positivity witness | `toPNat`, `toPNat_value`, `toPNat_injective`; the subtype contains `numeric p` and the proved positivity. |
| Nat encoding denotes `n+1`; decoding takes the natural predecessor | `encode` is an abbreviation of `PosNum.ofNatSucc`; `decode` uses `PNat.natPred` after `toPNat`. `numeric_encode` reuses `PosNum.succ_to_nat` in Nat induction. `decode_eq_numeric_pred` and `numeric_eq_decode_add_one` make the offset explicit. No conversion algorithm is duplicated. |
| Both shifted round trips and both injectivity directions | `toPNat_encode`, `decode_encode`, `encode_decode`, `encode_injective`, `decode_injective`; reuse `Nat.natPred_succPNat`, `PNat.succPNat_natPred`, `PNat.coe_injective`, and the numeric injectivity bridge. |
| PNat and Nat correspondence packages | `ofPNat`, `toPNat_ofPNat`, `ofPNat_toPNat`, `binaryPNatEquiv`, `binaryNatEquiv`. `pnat_equiv_observation` connects the shifted observation to existing `Equiv.pnatEquivNat`. |
| Numeric comparator equality/less/greater branches, including the encoded-Nat specializations | `cmp_eq_iff`, `cmp_lt_iff`, `cmp_gt_iff`, and `cmp_encoded_*_iff`; reuse `PosNum.cmp_eq`, `cmp_to_nat`, `lt_to_nat`, `le_to_nat`, `lt_iff_cmp`, `le_iff_cmp`. The equality branch concludes actual PosNum equality. |
| Recover any Nat-indexed observation through binary keys | `observation_roundtrip {α : Type u} (observe : Nat → α) : (observe ∘ decode) ∘ encode = observe`. It applies `decode_encode` pointwise, using ordinary function composition and function extensionality. |

Relevant PNat infrastructure is in `Mathlib/Data/PNat/Defs.lean:42–71,119` and `Mathlib/Data/PNat/Equiv.lean:19–23`. The numeric comparator infrastructure is in `Mathlib/Data/Num/Lemmas.lean:128–175,582,688–692`. These source declarations were inspected before coding.

## Retained checked cases and their connections

| Independent expected case | Checked connection |
| --- | --- |
| Key 0 encodes as one and returns to 0; key 1 encodes as bit0 one; their representations differ | `encode_zero`, `decode_one`, `encode_one`, `zero_one_distinct`; the decoded boundary uses `decode_encode`, and distinctness uses `encode_injective`. |
| The source constructor `bit0 (bit1 (bit0 one))` has numeric value 10 and shifted key 9 | `ten_numeric` uses each general constructor equation, then closed arithmetic. `ten_key` uses `numeric_eq_decode_add_one`; `encode_nine` uses the reverse law `encode_decode`. |
| PNat's numeric projection of that value is 10 while its natural predecessor is 9 | `ten_pnat_observations`, using the preceding general observations and connected cases. |
| Unshifted `PosNum.ofNat` maps both 0 and 1 to one, so it is not injective over Nat | `ofNat_zero_one_collision`, `ofNat_not_injective`; the non-injectivity proof uses the actual collision. This is not a claim about `ofNatSucc`, whose injectivity is proved separately. |
| The PosNum predecessor clamps one to one; the Num predecessor and shifted natural key are zero | `predecessor_boundary`, connected to `decode_one` and the existing predecessor definitions. |
| Numeric one precedes two; encoded key 9 compares equal to constructor ten; ten follows one | `numeric_one_before_two`, `comparator_recovers_ten`, `numeric_ten_after_one`; each uses a general comparator theorem, with key equality or arithmetic premises established. |
| Absence, a present empty list, and a present nonempty list survive the observation round trip | `observed_absence`, `observed_empty_value`, `observed_nine` use `congrFun (observation_roundtrip sampleObservation)` at keys 0, 1, 9, yielding `none`, `some []`, `some [9,10]`. The sample is an ordinary Nat-indexed observation family, not a new table implementation. |

## Statement review

- Constructor direction matches the source: bit0 doubles the numeric child, bit1 adds one after doubling. The ten calculation tests a nested mixture of both constructors.
- `numeric : PosNum → Nat` is unshifted and never zero. `decode : PosNum → Nat` can be zero and equals `numeric.pred`. `encode : Nat → PosNum` denotes `n+1` for every Nat. Neither positive predecessor clamping nor unshifted `ofNat` is substituted for these functions.
- Positivity is an actual field of `toPNat p`; one and ten are inhabited witnesses, not assumptions. No finite integer range or overflow model is imposed.
- The two inverse laws quantify over all Nat and all PosNum independently. Both injectivity statements identify their respective original inputs. The equivalences package those established laws without new comparator or representation classes.
- Comparator laws concern the existing **numeric** `PosNum.cmp`. They do not identify it with Color's `PositiveOrderedTypeBits` relation, ordered enumeration, or root-first choice. No source carry/comparison recurrence or traversal-cost claim follows from these value laws.
- `observation_roundtrip` quantifies over any `α : Type u` and any observation `Nat → α`; it requires no equality decision, default value, storage structure, or algebraic instance on α. Its result is equality of the observed functions. The option-valued cases retain the distinction between absence and a present empty value.
- Scope is the representation seam. Trie lookup/insertion, maps/sets, Color's algorithms/order/choice, source carry arithmetic, extraction machine-integer contracts, native runtime and cost bounds remain later obligations. Staging these laws does not complete their consuming chapters.

## Exact focused validation

Executed from `/workspace/scratch/0c54f2db1fdf`:

```sh
python3 work-state/staging/positive-keys/prepare.py
python3 work-state/staging/positive-keys/run-check.py
python3 work-state/staging/positive-keys/postcheck.py
```

Only `run-check.py` invokes Lean. It uses the main checkout's pinned Nix environment, `/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, the recorded candidate `LEAN_PATH`, and `LEAN_NUM_THREADS=1`. Its entire Nix/Lean invocation is wrapped by `timeout --signal=TERM --kill-after=5s 180s nix develop --command …`. `STARTED.json` and `result.json` preserve the complete actual argument vector and environment additions; the runner starts its own process session and prevents another launch once `STARTED.json` exists.

This new module has no historical compiler command. The executable, flag convention (`-o`, `-i`, `-c`, `--setup`, `--json`), and candidate `LEAN_PATH` were taken from the completed Finite trace, preserved in `environment-command-source.trace.json`. The new setup preserves the frozen `frp-imports/Spec.setup.json` byte-for-byte except its module name, now `VFAStaging.PositiveKeys`: the same 9,035 artifact mappings, package/options/module mode, **no imports override**. Both direct roots resolve to completed `vfa-validation` dependency artifacts. No main dependency copy, project artifact, broad build, or cache fetch was needed.

| Observation | Result |
| --- | --- |
| Start / finish UTC | 2026-11-02 07:37:08.974794 / 07:38:08.949889 |
| Elapsed / exit | 59.974736 seconds / 0 |
| Timeout / retries | No / none |
| Diagnostics | 0 errors, 0 warnings, 8 information messages |
| Emitted module / direct imports | `VFAStaging.PositiveKeys`; exactly `Mathlib.Data.Num.Lemmas`, `Mathlib.Data.PNat.Equiv` |
| Declaration metadata | 52 named source declarations, preserved in `postcheck-evidence.json` |
| Protected identities changed | None of 27 |
| Generated artifact disposition | `.olean`, `.ilean`, `.c` hashes/metadata captured, then all removed; `out/` is absent |

The information messages are eight selected `#print axioms` reports. `numeric_encode`, both round trips, `cmp_eq_iff`, and `Examples.observed_nine` report only `propext`, `Classical.choice`, `Quot.sound`; the less/greater comparator theorems report only `propext`; `Examples.ofNat_not_injective` reports no axioms. The complete source contains no admission, new axiom, unsafe declaration, or native proof shortcut. This focused check and selected reports do not replace the consuming chapter's full guarded build/exhaustive proof audit or the pending independent draft review.

## Provenance and recovery identities

VFA **2.1**, release stamp **2026-08-24 10:11**, Coq 9.0.0 or later. Source constructor/numeric examples: `Trie.v:131–165`; shifted conversions/round trips/injectivity exercises: `Trie.v:570–608`; Color's distinct order boundary: `Color.v:73–120`. Use the verified official [versioned archive](https://softwarefoundations.cis.upenn.edu/vfa-2.1/vfa.tgz) and require archive SHA-256 `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8` on recovery, following `../../source/SOURCE-RECOVERY.md`. Source references/hashes are retained here rather than a book copy.

Lean **4.35.0**, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`. Full dependency revisions, Nix/toolchain identities, source/direct-artifact identities, and before/after evidence are in `inputs.json` and `postcheck-evidence.json`.

| Source/artifact | SHA-256 |
| --- | --- |
| Staged `VFAStaging/PositiveKeys.lean` | `98c890672ed3e91b16089eb82037af46f15061af572c838f436b5692f5182f79` |
| Pinned `Trie.v` | `a5af2b4db4c2cb639a8deb063e57909e11eb44ee763782ad0af9afbf45a78f3e` |
| Pinned `Color.v` | `67b3410af5fece56c69f4e8301fd6505e89371cfa1279d069ca945b9b2b33370` |
| Mathlib `Data/Num/Basic.lean` | `92971636728e05bc108db821379b71e42c41a49a78eb7ef7674710228cb520f1` |
| Mathlib `Data/Num/Lemmas.lean` | `5cec0cb9b3b20de90fddc44955c23fc5bd94e09aa630214b88e1a95997d7c8c7` |
| Mathlib `Data/PNat/Notation.lean` | `27f551615e05235a068fec3b16124ba5bb6aaa56fef85e968d0b2c98b932d171` |
| Mathlib `Data/PNat/Defs.lean` | `6e01d3031fce32d6de89d510736f3abc6293a45b295f08fb0cc712c41c4f9d6e` |
| Mathlib `Data/PNat/Equiv.lean` | `424a2758860de194f91226631abeacc39b97a7322b4d99ab7fceaa785920c9a9` |
| Staging setup | `d3091ee0ca817526d0f16ab266814d2bb5db99cf4501b402e533cce586276bb0` |
| Generated `.olean` (removed) | `6b056cec59a77f6e92a4dc79fcf31e62b1943e914b7bb24689b2a84c387adccf` |
| Generated `.ilean` (removed) | `462fe20d43acb95479b489ad4c49e05916b24bca5bdf8750339b5f61bd56363f` |
| Generated `.c` (removed) | `c1a040f0160fc154a73a4c01833f3289c9836decf93c1417556358b75662f0ee` |

`SHA256SUMS` covers the retained staging files. Frozen for the parent-coordinated independent bounded review and subsequent recovery checkpoint; integrated chapter order is unchanged.
