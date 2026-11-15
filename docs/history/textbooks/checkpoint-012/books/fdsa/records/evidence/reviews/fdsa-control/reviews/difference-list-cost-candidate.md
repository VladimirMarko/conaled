# Shared difference-list closure candidate handoff

Recorded 2026-11-02. Committed uncompiled draft; no unit or chapter acceptance.

- Unit starting base: `a14977b9e316cc484ffad8a470d26b15615956c0`.
- Original source draft: `ffeaf8aed84184f49a13acb5c84e1fd608c9b7e8`.
- Current documentation-corrected candidate: `62809ced86c561c7a6cce8b71e727177a3f17fb8`.
- Branch/worktree: `work/fdsa-builder-costs` / `conaled-builder-costs`.
- Commit: `feat(resources): separate builder creation and application costs (#174)`.
- Frozen exact requirements: `difference-list-cost-requirements.md`, SHA-256
  `cb215a33cce3dd258cca37b9d703522d19caf2da76767c01e573d268b3e92c4e`.
- Design/source preflight: `../research/difference-list-cost-preflight.md`,
  SHA-256 `a0bd75c09ea1208c880dc87d5e8abe88be207c1e411b118519e7cf6237984232`.

The base is the still-uncompiled Chapter 1 repair. This branch does not contain
the separate insertion/list/potential/affine drafts. Reconcile those branches
only with the appropriate accepted Chapter 1 base and preserve their outstanding
validation and source obligations. The main repository and old frozen validation
checkout remain on `1aabd512284fe86254278ac631eda061d311050b`.

## Implemented source and statement assessment

The core uses an ordinary function `List α -> Measured (List α) Nat` with
separate arbitrary-suffix `Rep` and `AppCost` predicates. Charged identity,
singleton and composition expose their value and dependent application-cost
equations. Composition executes g before f while concatenating their represented
prefixes in f-then-g order. The uniform cost contract covers the actual intermediate
suffix passed to f, not only materialization at the empty suffix.

Creation operations capture supplied values at a fixed unit observation without
invoking them. `pushRun` performs two creation operations through existing bind;
`buildFrom` uses existing run. The seed-general laws separately derive prefix,
construction cost `2*n` and application cost `k+2*n`. Initial identity creation
then gives `2*n+1` for construction and for each later application.

`toDList` reuses Batteries.DList with an erased value function and its proved
invariant. The application/toList/equality/append/push bridges preserve values.
They do not infer costs for the pinned fused Batteries push, install a false
measured Monoid identity, or claim compiler/runtime behavior. No payload
equality, order or inhabitance is required.

Root inspected all core proofs, including the generic seed induction,
arbitrary-suffix contracts and ordinary DList laws. The connected cases consume
these public results and keep independent expected calculations:

| Case | Expected and retained result |
| --- | --- |
| Ordered singleton composition | Prefixes [1] and [2] applied to [9] give [1,2,9], application count 3 |
| Expensive supplied callbacks | Capture costs 1; application counts p+q+1, including zero p/q |
| Identity-seeded builder | Construction and one application each cost 2*n+1 |
| Construct then apply once/twice | Actual measured binds give 4*n+2 and 6*n+3, retaining both lists |
| Duplicate input [3,1,3] | Counts 14 and 21 for the combined programs, with nonempty suffixes preserved |
| Empty payload type | Empty one-/two-application programs cost 2/3 without a payload inhabitant |
| Supplied singleton seed | Extending n items then applying costs 4*n+1, excluding earlier seed creation |
| Charged identity | Same value; composition adds two application entries |
| Empty-prefix padding | Same decoded value for every n; application count 2*n+1 exceeds any proposed affine output-length expression |
| Shared self-composition | Creation n+1, application plus one 2^(n+1); the successor equality justifies natural subtraction |
| Four self-composition extensions | Five creations, application 31, combined construction/application 36 |

The self-composition induction applies its hypothesis at the original suffix
and at the actual intermediate callback value. It does not substitute repeated
description sharing for memoization. The generic application bounds count
unfolded invocation occurrences, not distinct shared allocation events.

The source's actual asc seed is singleton-prefix, with final suffix [last].
Its recurrence/size correspondence, the conditional 2*r-3 application count,
full scanner/control/descending/emitted-run/dispatch work, and ordinary repeated
append versus prepend/reverse comparison remain Chapter 2 obligations.

## Author-side preflight and wording corrections

The source-inventory contributor independently inspected the root-written
examples and notes against the frozen requirements and actual pinned source.
It found no mathematical/count/source-scope mismatch. This was an author-side
preflight, not either final independent review axis; it did not inspect a
changing core or run Lean.

The inspected example and documentation hashes were respectively
`e7f8e4f34bdb40bce772377588d4be975255fe7555c7fedabb837ca214db2d16` and
`47fb173fcba5ae41ebbf93f15b4584a5aefaac2fd0b7a0e8addd83b0873228cd`.
Two nonblocking text corrections were applied before committing: the count 21
now explicitly includes construction plus two applications, and the validation
note excludes only an additional compiler run for this draft, acknowledging the
old gate's existing compiler. The formal declarations were unchanged by those
text corrections.

## Original source-draft identities and validation boundary

| New file | SHA-256 |
| --- | --- |
| `Applications/Resources/DifferenceListCosts.lean` | `567683626b9a46d07c465ceb44faaafc941e2dc1c83491b093599ca7f8c698a5` |
| `Examples/DifferenceListCosts.lean` | `09165e6a1ccb0b0e45b7ddc6083883aa5bf67bc931c59ff44707d1726ffbe102` |
| `docs/research/fdsa-difference-list-costs.md` | `635f53c8823e2d6f0d54939b5966a90661e54c5861094bf70aa09bec9b7f43a1` |

The five-file commit includes the public application import and source-map
section. The checkout was clean after commit; `git diff --cached --check`
passed. No Lean/compiler/build or axiom-audit command ran for this draft.
Elaboration of its induction, simplification and DList bridge remains pending.

The old frozen Chapter 1 gate continues unchanged. Later validation must cover
the final immutable integrated candidate, with source/public coverage, full
build, exhaustive audit, both retained independent axes and immediate final
candidate verification. No source preflight or checkpoint closes those gates.

## Provenance correction successor

`62809ced86c561c7a6cce8b71e727177a3f17fb8` corrects only the AFP/Isabelle attribution in
`docs/research/fdsa-difference-list-costs.md`. Its new SHA-256 is
`fd01432541c9b27ad83def6192e4a3b75d6b77ae7490ec11a2bf665324f1246e`
(10,679 bytes). Both Lean files, examples, imports and reconstruction map are
unchanged. The prior source draft and original file hashes above remain
historical evidence; the unit base and requirements are unchanged.

Finding `XD01-DOC-001` and the original preflight attribution are retained in
`difference-list-provenance-correction.md`; read it with the historical
design preflight. Root verified the exact saved AFP archive member and its
import header, then `git diff --check` and `git diff --cached --check` passed.
The one-file commit left the checkout clean. No compiler ran, and independent
final review of the correction and entire unit remains pending.

## Recovered compiler continuation — 4 November 2026

The first six-target development attempt at 4ac0e7eed2fa41a8844fff8d213b6298e9ad5cf9 closed with actual exit 1, clean unchanged source. Complete recorder/native logs are preserved in provenance/chapter02-variants-xd01-focused-20261104-attempt1/. XD01 core reported the reserved `prefix` binder and its parser cascades, plus one genuine successor arithmetic normalization in `buildFrom_appCost`; its downstream example job is not a pass. Independent Standards and Spec source assessments of exact628 are complete with zero mathematical source findings, overall Blocked pending validation.

Root implemented XD01-ELAB-001/002 in the source-only tree: bare code binders/references `prefix` become `pref` while comments/strings stay unchanged; an explicit natural-number equality aligns the same application-cost induction result. Public names, definitions modulo bound-variable spelling, premises, expected cases, source note and mappings are preserved. Successor 66e480cf6db359ebf97d761b804ebe5d6d946eca is uncompiled. Exact diff, source hashes, actual whitespace/commit results are in provenance/chapter02-xd01-correction1-20261104/. Continue both independent axes on these changes and the entire five-path scope; no acceptance is claimed.

## Compiler continuation: XD01-ELAB-003, 4 November 2026

The first corrected focused attempt at e2db542 closed with actual exit 1. Its complete log and native terminal record are retained. The only remaining core diagnostic was `compose_rep`: the simplifier did not specialize the definition-valued Rep witnesses. Candidate 52722e3ee481167e99b8f6c0b2417df7fb7615d8 applies each witness at the actual callback suffix and rewrites append associativity. This is a proof-only change from 66e480cf6db359ebf97d761b804ebe5d6d946eca; public statements, algorithms and examples are unchanged. The exact diff, hashes and source assessment are in provenance/chapter02-xd01-correction2-20261104/. Compilation, explicit type assessment, both full-scope review continuations and all acceptance gates remain pending.

## Complete corrected-source statement readback, 4 November 2026

All 72 public declarations (42 core, 30 connected examples) passed explicit elaboration and root completed every corresponding source/type assessment with zero concrete findings. Exact checked central candidate dfaf68114d1dda4e15628c94c3d988c3f5457c49 contains the two source files byte-identical to minimal52722e3ee481167e99b8f6c0b2417df7fb7615d8. The corrected four-target check exited0; all134 combined types exited0, with complete closed/native logs retained. Full per-declaration assessment: provenance/chapter02-xd01-random-types-20261104/xd01-root-readback.md. Both independent source reviews of original62809ced remain retained and overall Blocked; successor/full-integration review and all acceptance gates remain pending.
