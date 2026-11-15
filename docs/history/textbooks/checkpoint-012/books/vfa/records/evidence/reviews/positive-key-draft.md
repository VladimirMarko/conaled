# Independent bounded review: local #1023 positive keys

Reviewer: `reuse_survey`, 2026-11-02. **No findings.** This is a source/spec and
frozen-evidence review of a staging adapter within the existing workflow. It
does not accept a chapter, integrated candidate, or ticket. No compiler was
invoked and no source, candidate, dependency, configuration, or process changed.

The owner confirmed the complete evidence freeze before evidence assessment or
this record was written. The whole specification, reuse note, 43 theorems and
9 definitions/abbreviations, README, and validation harness were inspected.
Pinned Trie/Color passages and the relevant Num/PNat library definitions and
theorems were checked directly in source.

## Mathematical and source correspondence

- **Constructors and positivity:** `numeric_one`, `numeric_bit0`, and
  `numeric_bit1` match `Trie.v:131–151`'s xH/xO/xI observations for arbitrary
  children: 1, `0 + 2*n`, and `1 + 2*n`. `numeric_pos` and `one_le_numeric` have
  no extra assumptions. The nested constructor ten checks both bit constructors
  through the general equations. Reusing PosNum introduces no second datatype.
- **Offsets and inverses:** `numeric` is the unshifted positive value;
  `decode` is its natural predecessor; `encode` is existing `ofNatSucc` and has
  numeric value `n+1`. These match the shifted convention at `Trie.v:575–608`.
  Both round trips quantify over all inputs on their respective sides. Both
  injectivity proofs recover the original inputs by those inverse laws.
- **PNat transport:** `toPNat` contains the numeric value and its actual
  positivity proof. `toPNat_encode`, both PNat inverse laws, and the two Equiv
  packages reuse cast injectivity and PNat predecessor/successor laws.
  `pnat_equiv_observation` explicitly agrees with existing `Equiv.pnatEquivNat`.
  No duplicate conversion recursion or new representation hierarchy is added.
- **Comparator orientation:** the equal branch concludes actual PosNum equality.
  The lt branch observes `numeric p < numeric q`; the gt branch correctly
  reverses the operands. Encoded-key specializations cancel the common successor
  offset. The checked one/two, encoded-nine/ten, and ten/one cases connect to
  these general laws. They concern numeric order, as stated.
- **Boundaries and clients:** the collision `ofNat 0 = ofNat 1 = one` proves
  failure of unshifted injectivity; it does not undermine `ofNatSucc`. The
  predecessor case distinguishes PosNum's clamp at one from Num/Nat zero.
  `observation_roundtrip` is ordinary function equality for every `α : Type u`
  and `observe : Nat → α`, with no storage, decidability, or default assumption.
  Its connected clients retain `none`, `some []`, and `some [9,10]` separately.
- **Scope:** the draft and README do not claim to implement the source's partial
  comparison exercise, carry arithmetic, Trie/Color algorithms, extraction
  contracts, or any resource/runtime bound. Color's distinct bit ordering
  (`Color.v:73–120`) and root-first choice are explicitly excluded. The examples
  support the representation laws without claiming later chapter coverage.

## Independent evidence checks

The frozen manifest's **12 listed files** all matched their hashes and accounted
for every retained file except the manifest itself. Source, specification, reuse
note, and all **27 protected inputs** were independently rehashed; the recorded
before/after identities match, and those inputs still matched at review time.

The 9,035-mapping setup is byte-identical to its recorded frozen template except
the single module-name substitution to `VFAStaging.PositiveKeys`; every other
field/mapping is preserved, with no imports override. The source has exactly
`Mathlib.Data.Num.Lemmas` and `Mathlib.Data.PNat.Equiv` as direct imports. Recorded
emitted `.ilean` metadata names that module and those roots, with all import flags
false; the C initializer record agrees. The metadata contains 52 source names,
consistent with the independently counted declarations.

The preserved Finite trace supplies the executable, original candidate
`LEAN_PATH`, and flag convention for this new module, with provenance accurately
qualified in README. The recorded invocation retains `-o/-i/-c/--setup/--json`,
uses staging-only output paths, the pinned Nix shell, `LEAN_NUM_THREADS=1`, and
the 180-second timeout plus five-second grace. The runner permits one launch.
Result and start records agree: exit 0 in **59.974736 seconds**, no timeout.

The raw diagnostics independently parse as exactly eight information messages,
zero errors/warnings, with no extra non-JSON output. Axiom reports match README:
the reported union is only `propext`, `Classical.choice`, and `Quot.sound`;
the lt/gt claims use only `propext`, and the ofNat collision proof uses none.
The full source contains no admission, added axiom, unsafe declaration, or
`native_decide`. Selected reports are not represented as an exhaustive audit.

The postcheck records generated artifact hashes before deletion. The `out/`
directory and all generated `.olean`, `.ilean`, and `.c` files are absent.
No reviewer compiler rerun or recovery of deleted binaries was performed.

## Exact reviewed identities

All hashes below are SHA256; paths are relative to `work-state/`.

| File | Hash |
| --- | --- |
| `specs/1023-Positive-keys.md` | `ce48f68b69f4c155ab96f7714d930c62806ab1362ee517256f2e39f95f854c5d` |
| `source/POSITIVE-KEY-REUSE.md` | `ea930357c4547aebff68ae1a8464adb60af1dd336cb6e9669771dcf3db51df02` |
| `staging/positive-keys/VFAStaging/PositiveKeys.lean` | `98c890672ed3e91b16089eb82037af46f15061af572c838f436b5692f5182f79` |
| `staging/positive-keys/README.md` | `e6d9e8a3eeb56204d1e9ac72c51a0a0457956e726750af18795c74e418d0c956` |
| `staging/positive-keys/SHA256SUMS` | `feb485c6a82167aa8b03758125b2b18eb050674f4c90a9b974d30215f8c17468` |
| `staging/positive-keys/PositiveKeys.setup.json` | `d3091ee0ca817526d0f16ab266814d2bb5db99cf4501b402e533cce586276bb0` |
| `staging/positive-keys/result.json` | `5d21c2e0fbcb4be5997ae8e1fc393ab520c8a210fe67d605835a8720eb25859e` |
| `staging/positive-keys/postcheck-evidence.json` | `7ef166c19fc3a0710aa6956eec928647eccf6debb751cd7f3e1a0a6fe65eb194` |

Source pins verified through protected-input records: VFA 2.1 Trie
`a5af2b4db4c2cb639a8deb063e57909e11eb44ee763782ad0af9afbf45a78f3e`,
Color `67b3410af5fece56c69f4e8301fd6505e89371cfa1279d069ca945b9b2b33370`;
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Lean 4.35.0.

**Disposition:** no corrective action for this bounded draft. Integration into
its consuming chapters, the complete guarded build/exhaustive audit, and the
mandatory independent Standards/Spec gates remain later obligations for root.
