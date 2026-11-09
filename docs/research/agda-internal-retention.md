# What completed Agda declarations retain

Research for [#115](https://github.com/VladimirMarko/conaled/issues/115),
2026-11-09. The inspected base is
`0b9a72f58d8fd7476eff6676f88b2690491b5051`. This follows the
[frontend assessment](agda-core-and-slean-frontends.md) and the
[monodromy consumer-path assessment](monodromy-consumer-path.md).

**Completed internal declarations remain the useful candidate input.** The
saved interfaces contain the dependent types, checked bodies and conversion
chain needed to investigate the retained consumer. Runtime output cannot
replace them. This experiment does not establish a complete export or a
translation to Lean: some environment fields remain decoded only as raw nodes,
and the cubical rules still require a justified interpretation.

## What was actually checked and inspected

The [reproduction kit](../../experiments/agda-internal-retention/README.md)
checks fresh sources using the official Agda 2.8.0.2 Linux binary and Cubical
commit `b150186d2544e7efeddd31e5d14a8b9ecbb100f7`, the exact library retained
with Monodromy/FrozenMemo. Its [receipt](../../experiments/agda-internal-retention/evidence/receipt.json)
records executable/archive hashes, commands and the 154-module Monodromy import
closure. This is the compiler's module closure, **not** a certificate of the
smallest assumptions of the selected argument. Licensing and source provenance
are recorded in the kit. The matching compiler previously used for checkpoint
096-10 was reused; that checkpoint's library closure was not substituted.

Two modes were kept separate:

- `IdentityPattern.agda` uses `--safe --without-K`. Its probes cover level
  polymorphism, dependent identity elimination, ordinary constructor matching,
  an irrelevant argument and an abstract definition.
- Monodromy and FrozenMemo retain `--safe --cubical --guardedness`. The Cubical
  library's own options remain intact. Neither `--erased-cubical` nor a change
  to judgmental equality was used to make the consumer compile.

Both checks succeeded with unsolved metas and incomplete matches disallowed.
The experiment inspected the resulting `.agdai` signatures, not just the scoped
syntax or a surface pretty-printer. A bounded Python decoder reads the actual
serialized tables for interface format `202507030`. It produces selected
summaries and keeps complete raw tables privately for reproducing individual
node references. The decoder is an untrusted research instrument; its output
has not been verified against an independent proof checker.

The official release binary did not produce a declaration dump at
`-v tc.signature:60`. Its help says verbosity requires a build with the
`debug` flag; the observed behavior is consistent with a non-debug build. The
[ordinary diagnostic](../../experiments/agda-internal-retention/evidence/ordinary.log)
contains checking progress, not a hidden successful core dump. Reflection was
considered, but its `getType`/`getDefinition` view is not the whole compiler
interface or checking environment. A debug-capable build of the pinned Agda
source, or a small backend linked against that version's compiler library,
remains a route to an independent typed dump. Neither was built here.
[Reflection API](https://agda.readthedocs.io/en/v2.8.0.2/language/reflection.html)

## The selected consumer survives elaboration, with additional obligations

The actual saved clause references confirm this chain:

```text
Monodromy instantiates FrozenMemo.Memo with S¹ and Cover
Cover                 → S¹-rec ℤ (pathToEq sucPathℤ)
S¹-rec                → Cubical.HITs.S1.Properties.rec, eqToPath
sucPathℤ              → ua, successor/predecessor, inverse-law data
circle-loop           → Cubical.Data.Equality.S1.loop
step's checked body   → Agda.Builtin.Equality._≡_.refl
```

The declaration excerpts for
[the circle](../../experiments/agda-internal-retention/evidence/Cubical.Data.Equality.S1.json),
[conversion](../../experiments/agda-internal-retention/evidence/Cubical.Data.Equality.Conversion.json),
[successor univalence](../../experiments/agda-internal-retention/evidence/Cubical.Data.Int.Properties.json)
and [Monodromy](../../experiments/agda-internal-retention/evidence/Monodromy.json)
record actual qualified names and term references. They are selected excerpts,
not a proof that no other declaration is required.

`step` still has a dependent equality type and a reflexivity body. That body
alone does not explain why it checks: conversion unfolds the covering,
path/equality conversions and cubical computation. An importer accepting
`refl` while omitting those rules would miss the main obligation. Likewise,
`input` and `erased-input` remain different checked terms. The whole selected
pair and its transported witness are retained in
`value-and-witness-twice` and `transported-witness-twice`; observing only the
final integers would discard part of this consumer.

There is also information absent from the source equations. In the saved
[FrozenMemo signature](../../experiments/agda-internal-retention/evidence/FrozenMemo.json),
`Memo.η` has nine clauses, including cubical composition/transport references;
the source gives one equation. `eqToPath` has five saved clauses. These are
compiler-generated clauses for the indexed equality datatype in cubical mode.
They are evidence against exporting only visible source patterns. `j-beta`,
`w-twice` and `apd-twice` each retain a reflexivity clause, but their types still
carry the dependencies that make those proofs useful.

This study supplies no new theorem about the source/model correspondence.
The conversion judgments and generated cubical clauses still need examination
in the monodromy construction work; a list of resolved names does not discharge
those obligations.

## Retention, declaration by declaration

The internal column describes observed saved declarations. No actual treeless
`TTerm` dump was obtained. The final column distinguishes observed backend
output from expectations supported by the pinned treeless implementation.

| Declaration | Surface requirement | Completed internal evidence | Runtime/treeless boundary |
|---|---|---|---|
| `identity` | Arbitrary level and type | Dependent `Pi` spine, sort annotations, level terms and variable body | Generated Haskell worker accepts only the value; JS retains positional wrappers but returns the value. Neither retains its dependent typing judgment. |
| `J` | Motive indexed by endpoint and equality witness | Dependent type and checked reflexivity pattern/body; compiled case metadata present | Generated Haskell worker is identity on the base case. JS returns its base-case argument. The motive's judgment is absent. |
| `predecessor` | Zero/successor constructor cases | Two saved clauses and compiled case tree | Both backends retain an integer branch/subtraction computation. This does not recover the original inductive declaration by itself. |
| `forget` | Irrelevant natural argument | Domain argument metadata retains irrelevance | Haskell worker is constant zero; JS ignores its argument. Runtime behavior does not state the legal source uses of that argument. |
| `opaqueIdentity` | Abstract body outside its block | Body and `FunAbstract` flag both retained | Generated worker computes as identity. Availability of code is not permission to unfold the source declaration during checking. |
| `FrozenMemo.j-beta` | Indexed identity computation | Typed reflexivity clause | No cubical runtime artifact was produced. Its source judgment cannot be reconstructed from a hypothetical erased proof value. |
| `FrozenMemo.Memo.η` | Compatibility of dependent transport composition | Nine clauses, dependent type and cubical primitive references | No cubical runtime artifact; generated clauses require the source's cubical interpretation. |
| `FrozenMemo.Memo.w-twice` | Selected dependent pair under two substitutions | Typed reflexivity clause, dependent pair references in type | No cubical runtime artifact; preserving just existence or the first component is inadequate. |
| `FrozenMemo.Memo.apd-twice` | Transported higher witness under substitution | Typed reflexivity clause and higher identity dependencies | No cubical runtime artifact; no proof-irrelevance replacement was justified. |
| `Cover`, `S¹-rec`, `loop` | Circle family and chosen loop | Saved references to cubical recursor and path/equality conversion | Full cubical compilation rejects; no runtime projection of this family was established. |
| `pathToEq`, `eqToPath` | Conversion between cubical paths and indexed equality | Checked types/bodies; the latter has generated cubical clauses | They cannot be replaced by Lean equality without a compatibility result. |
| `sucPathℤ` | Universe path from successor equivalence | `ua`, equivalence construction and inverse-law references | No computational univalence bridge to our current Lean fragment is supplied. |
| `circle-loop`, `step` | Abstract selected loop and transport computation | Bodies, dependent types and abstract flags retained; `step` is `refl` | Full cubical backend rejection; abstract conversion context still matters. |
| `input`, `erased-input` | Different selected first paths | Different checked constructor applications | No backend artifact. They must remain distinguishable by the required observation. |
| `transport-three`, `transport-two` | Concrete consequences of selected paths | Distinct checked applications and types | The two integer conclusions alone would not preserve the argument. |
| `value-and-witness-twice`, `transported-witness-twice` | Reuse of generic dependent laws | Actual references to `w-twice`/`apd-twice` and `input` | No runtime artifact; selected witness preservation remains part of the spec. |

The ordinary [Haskell](../../experiments/agda-internal-retention/evidence/IdentityPattern.hs.txt)
and [JS](../../experiments/agda-internal-retention/evidence/IdentityPattern.js.txt)
files are actual generated output. Haskell generation used
`--ghc-dont-call-ghc`; no executable was linked or run. Attempting JS compilation
of unchanged Monodromy produced
[`CubicalCompilationNotSupported`, exit 42](../../experiments/agda-internal-retention/evidence/cubical-runtime.log).
JS's retained argument positions illustrate why “erasure” should not be
reported as a uniform removal of every syntactic argument across backends.
[Agda backend documentation](https://agda.readthedocs.io/en/v2.8.0.2/tools/compilers.html)

The pinned treeless datatype has erased terms and runtime sorts rather than
internal dependent types. Its conversion pipeline performs erasure and
simplification. This source-level fact supports the boundary above; it is not
a claim to have dumped those intermediate nodes for this corpus.
[Treeless syntax](https://github.com/agda/agda/blob/cccf42fa88eae25ccbe2623f489021d2075f6f73/src/full/Agda/Syntax/Treeless.hs),
[conversion pipeline](https://github.com/agda/agda/blob/cccf42fa88eae25ccbe2623f489021d2075f6f73/src/full/Agda/Compiler/ToTreeless.hs)

## Environment, completion and information already lost

The inspected interface envelopes retain imported-module references, a
signature, meta bindings, builtins, source pragmas, checking options, partial
definitions and opacity metadata. The signature includes separate rewrite-rule
and instance tables. Each selected interface had empty saved meta-binding,
partial-definition and rewrite-rule tables. This does not prove that an
arbitrary interface is complete or that the whole imported closure has no
additional primitive assumptions.

Completion here is supported by fresh checking with explicit rejection of
unsolved metas and incomplete matches, successful exit statuses and completed
declarations. A scope-only result is not accepted. The partial term traversal
found no `MetaV`/`Dummy` in the inspected positions; sorts, levels and metadata
were not traversed for this test. Do not turn that bounded result into a
universal “no metavariables anywhere” claim.

Types use `El sort term`; dependent domains retain `ArgInfo`, names, partial-type
status and optional tactics. `ArgInfo` retains hiding, modality, origin,
free-variable information and annotations. Modality includes relevance,
quantity, cohesion and polarity. For example, the ordinary `forget` domain's
saved relevance is `Irrelevant`, while its ordinary language tag is
`WithoutK`. This corpus does not test crisp/cohesive restrictions: finding the
metadata slot is not a model or a tested exporter for them. Sort/level nodes,
pattern metadata, builtin maps and options are preserved as raw references in
the diagnostic, rather than silently discarded.

Abstractness and newer opaque blocks are separate mechanisms. The selected
abstract declarations retain flag bit 5 (`FunAbstract`) and bodies; their
empty opaque-block tables do not mean the bodies are freely unfoldable. The
serialization source also reveals losses: definition types have ranges
removed, blocker information is ossified, opaque-block data are abbreviated,
and the transient scope map is reconstructed rather than serialized whole.
The function's compiled case tree is saved, but its treeless cache is omitted
and restored as `Nothing` when reading. A saved interface is therefore not a
lossless transcript of elaboration or author intent.
[Internal serialization](https://github.com/agda/agda/blob/cccf42fa88eae25ccbe2623f489021d2075f6f73/src/full/Agda/TypeChecking/Serialise/Instances/Internal.hs),
[checking state](https://github.com/agda/agda/blob/cccf42fa88eae25ccbe2623f489021d2075f6f73/src/full/Agda/TypeChecking/Monad/Base.hs),
[argument serialization](https://github.com/agda/agda/blob/cccf42fa88eae25ccbe2623f489021d2075f6f73/src/full/Agda/TypeChecking/Serialise/Instances/Common.hs)

## Minimum candidate export and correspondence checks

A later bounded exporter should carry the following together. This is a
candidate schema, not an implemented interchange contract.

| Export component | Required check |
|---|---|
| Compiler revision, source/library hashes, modes and checker result | Match a fresh completed check; reject scope-only or incomplete results. |
| Qualified declarations with types, sorts, levels, bodies, telescopes and patterns | Preserve binders, de Bruijn indices, dependencies and generated clauses; validate against a typed compiler dump. |
| Argument restrictions and equality/conversion regime | Interpret relevance, quantity and any used modal restrictions; do not identify indexed equality with cubical paths or Lean equality by naming convention. |
| Inductive/record/constructor declarations and primitives used | Include formation, elimination and computation obligations, not only names of called functions. |
| Builtin bindings, rewrite rules, options and opacity policy | Reproduce the conversion responsible for `step = refl`; retain what can unfold at the source boundary. |
| Assumptions and reachable declaration closure | Classify axioms, primitives, parameters and generated dependencies explicitly; module imports are an upper bound, not minimal capabilities. |
| Source correspondence | Link exported declarations to exact source hashes and selected source names; preserve author structure separately where serialization drops it. |
| Target validation | Check a justified interpretation or independently checkable certificate. Compiler success alone is not a Lean theorem. |

A typed compiler-side dump cross-checked against these saved tables would
resolve uncertainty about the bounded decoder. It would not resolve the
mathematical interpretation of cubical primitives. A direct `TTerm` dump could
make the erasure comparison more precise, but could not restore the missing
dependent judgments. Those are different follow-ups and need not block the
current source/model work.

## Consequences

Proceed with internal syntax **plus its environment** as the candidate input
for a selected fragment, while keeping direct/native interfaces available.
Do not invest in a broad importer on the strength of these excerpts. The next
source-admission work should account explicitly for the generated cubical
clauses and `step`'s conversion chain, and compare a compiler-side typed dump
before trusting an exporter. Existing monodromy construction/correspondence
tickets remain responsible for their mathematical obligations.

The current transfer fragment does not supply the circle, universe/Glue
computation and compatible indexed-identity interpretation required here.
This inspection neither generalizes away those requirements nor constructs
models for them. Preserving a source proof also does not recover its weakest
assumptions automatically. Author-selected parameters, abstraction boundaries
and explanatory structure should remain available alongside the checked terms.
No #108 theorem was selected or prepared, no production importer was added,
and no Lean formal claims or axiom-audit roots changed.
