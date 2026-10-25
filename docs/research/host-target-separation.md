# Host Lean and modeled target contracts

Issue [#136](https://github.com/VladimirMarko/conaled/issues/136), inspected
2026-10-25. Keep the latest compatible Lean as the development host. The current
host is Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Mathlib remains at `56a005855ea17e0b0958f73ec801ae140b0a1679`. This investigation
changes neither pin nor dependency manifest.

The smallest useful separation is to identify the target contract independently
of the host, keep its judgments and interpretation explicit, and place installed
Lean conversions at the edge. The graph implementation already does much of
this. Its remaining use of host data types does not require immediately copying
Lean's entire expression or environment infrastructure. A target revision label
alone would not specify its rules, interpretation, or executable compatibility.

## Existing boundaries

| Component | Explicit target content | Host coupling and consequence |
| --- | --- | --- |
| `GraphTarget` | Three-sort terms, formulas, inspectable proof code, substitution and native interpretation | Types/functions, `Prop`, equality and universes are host mathematics. This is a bounded native model, not a model of every target kernel rule. |
| `CoreSyntax` | Six raw constructors, de Bruijn substitution/renaming | `Lean.Name` and `Lean.Level` are reused as data. `toLean`/`ofLean` directly match host `Lean.Expr`; changes there can require adapter changes even when the fragment is unchanged. |
| `CoreTyping` | Explicit context lookup, binder/application rules and graph primitive schemas | Sorts use host `Level.succ`/`imax`, and constants use host names. There is no general conversion judgment, declaration-admissibility judgment, or full Lean type checker here. |
| `GraphEmissionPure`, `GraphEmissionTyping` | Pure producer and bounded typing preservation | Final expression and theorem-declaration payloads use host `Expr`/`Declaration` constructors. The roundtrip proof concerns representation, not kernel acceptance. |
| `GraphEmissionProof`, `GraphEmissionContract` | Primitive proof semantics, `ClosedDenotes`, independently stated artifact relation | Native Set/Prop semantics. Soundness does not identify arbitrary installed constants or establish ConLeche's set model. |
| `GraphPrimitiveEnvironment` | Exact accepted primitive records and structural comparison | Complete host `ConstantInfo`, names, levels, bodies, inductive and recursor metadata, safety fields and dependency closure. Body or private-name drift can invalidate the contract without changing primitive mathematics. |
| `GraphEmission`, `GraphTranslationValidator` | Producer/validator correspondence, bounded replay and rejection checks | Host environment inspection and synchronous kernel installation. The proved validator relation is separate from compiled execution, serialization and host kernel trust. |
| Isolated relative graph experiment | Explicit environment translation, primitive laws, conditional model comparison | Imports pinned ConLeche expression/judgment/checker APIs. `AcceptedGraph` still takes an acceptance equality; execution checks do not provide it. No result from unfinished #135 is used here. |

These are source inventories of [the graph core](graph-target-implementation.md),
[emission](graph-emission-implementation.md),
[validation](graph-translation-validator.md), and the
[relative model route](relative-graph-model.md). The pinned
[Lean expression](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Expr.lean)
and [declaration types](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Declaration.lean)
are the host representations being used. Representation compatibility, meaning
preservation, and actual checker acceptance need separate evidence.

## Two pinned contracts under one host

The [checked experiment](../../experiments/host-target/Contracts.lean) describes
a six-constructor sublanguage with two binder shapes. It follows a real change
between these ConLeche revisions, both described and checked using our single
Lean 4.35.0 host:

| Contract identifier | Source revision and bounded content |
| --- | --- |
| `conaled.host-target.never-core.v1` | ConLeche `67f04630d88718e81aa4d07ab64501f68f105398`; variables, sorts, constants, application, lambda and forall, with every binder metadata field restricted to `pw = .never`. Local representation: `HostTarget.Annotated`. |
| `conaled.host-target.bare-core.v1` | ConLeche `8e166ca53cd1f864b63c13cc1d326d38316d00ea`; the same six constructors with metadata-free binders. Local representation: existing `CoreSyntax.Expr`. |

The identifiers name local partial contracts tied to upstream evidence, not
full exports of either upstream datatype. Names and levels retain the host
encoding; local `Never` is the singleton subdomain representing upstream
`BinderMeta` with `pw = .never`. Literals, projections, arbitrary declarations,
other annotations and upstream environment well-formedness are outside scope.

The old [expression definition](https://github.com/leanprover/con-leche/blob/67f04630d88718e81aa4d07ab64501f68f105398/ConLeche/Kernel/Expr.lean#L328-L338)
has a third metadata argument on lambda and forall. The new
[definition](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Kernel/Expr.lean#L315-L325)
removes it. Old [BinderMeta](https://github.com/leanprover/con-leche/blob/67f04630d88718e81aa4d07ab64501f68f105398/ConLeche/Kernel/Expr.lean#L92-L104)
contains proposition-status data, not display `BinderInfo`. Its default is
`.never`; [PropWhen](https://github.com/leanprover/con-leche/blob/67f04630d88718e81aa4d07ab64501f68f105398/ConLeche/Kernel/PropWhen.lean#L398-L409)
has a separate opaque representation and public operations.

This is also a rule change. Old
[betaGate and beta](https://github.com/leanprover/con-leche/blob/67f04630d88718e81aa4d07ab64501f68f105398/ConLeche/Rules/Rel.lean#L117-L128)
permit contraction with `.never`, or with an argument inference/domain conversion
certificate. New [beta](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Rules/Rel.lean#L122-L130)
has no annotation gate. The experiment's `beta_reduct` checks the unchanged
substitution result for the old `.never` branch. It does not implement the other
old beta rule, either upstream conversion relation, or a checker.

Global annotation erasure would be an unjustified semantic claim. Old
[binder congruence](https://github.com/leanprover/con-leche/blob/67f04630d88718e81aa4d07ab64501f68f105398/ConLeche/Rules/Rel.lean#L370-L384)
requires matching annotations; new
[congruence](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Rules/Rel.lean#L395-L407)
uses different lambda conditions. Old
[denotation](https://github.com/leanprover/con-leche/blob/67f04630d88718e81aa4d07ab64501f68f105398/ConLeche/Denotes.lean#L154-L169)
uses `regime φ m.pw` with `lamR`/`piR`; new
[denotation](https://github.com/leanprover/con-leche/blob/8e166ca53cd1f864b63c13cc1d326d38316d00ea/ConLeche/Denotes.lean#L143-L156)
uses `lamV`/`piV`. The old
[inference rules](https://github.com/leanprover/con-leche/blob/67f04630d88718e81aa4d07ab64501f68f105398/ConLeche/Rules/Rel.lean#L508-L540)
also check the annotation against the codomain sort. In particular, adding
`.never` to every binder of a graph proof does not establish old upstream
annotation validity or typing.

### What is proved and reused

`erase_annotate` and `annotate_erase` prove inverse representation maps on the
selected sublanguage. `erasureSquare` uses the existing `Squares.Square`, and
`throughErasure` uses its composition. The downstream conversion example uses
the existing `CoreSyntax.Expr.ofLean_toLean` theorem. Its observation is decoded
syntax, not semantic truth; the fallback in `leanRep.decode` is unreachable on
this square's image and supplies no contract for arbitrary host expressions.

For semantic reuse, `graph_contract` transports the existing `emitCore_typed`
and `emitCore_denotes` to the annotated encoding. Its interpretation is explicitly
the repository's native graph interpretation after erasure. Its meaningful
instance is the existing forward graph declaration. It is not old ConLeche
`Denotes`, nor a claim that all annotations on that encoded declaration are
valid upstream. Both representations retain the same graph proof and meaning
without duplicating its argument. Different clients can provide different
observations to the square; no universal IR or mandatory frontend is introduced.

The binder-sensitive beta example substitutes an open variable beneath a
lambda and expects it at index one. This checks capture avoidance instead of
merely applying identity at the root. A distinct-universe example guards the
scope of representation equality. No test fabricates an upstream syntax change.

## Options and adoption cost

| Option | Benefit | Cost and limit |
| --- | --- | --- |
| Explicit version-indexed target specifications | Several target contracts can coexist in one host; changes to rules remain visible. | Every materially different judgment/interpretation needs definitions and comparison proofs. A single version parameter with identical rules would conceal the difference found above. Do not generalize the whole kernel from this fragment. |
| Pinned adapter packages | Isolates imports, serializers, environment metadata and executable APIs; clients can share stable bounded contracts. | Each host/target pair supported operationally needs a built adapter and compatibility tests. Separate package/toolchain machinery is unnecessary while only the current installed host is supported. |
| Separate experiments | Can investigate old APIs and alternative models without making them normal dependencies. | Evidence must retain exact pins, complete import-closure audit and commands. Experiments can diverge, so record which contracts have checked bridges. They do not create automatic production support. |

Adopt explicit identifiers and contract records at artifact boundaries first;
retain the current host adapter and isolated experiments. The delivered cost is
one bounded Lean experiment, a small reproduction entrypoint reusing the
existing compiler/audit, and this inventory. No library client changes are
required. A production old-version adapter would additionally need upstream
syntax conversion, annotation validation, environment translation and checker
refinement; those are unimplemented obligations, not hidden costs covered by
the roundtrip theorem.

ConRon's [alignment blocker](../../experiments/relative-graph/pin-alignment.md)
is concrete evidence of adapter cost: the pinned arena/refinement still expects
`BinderMeta`. Its port needs compatible Aeneas artifacts and proof/audit work.
A second installed Lean, general version registry, serialized interchange
format, or wholesale replacement of `Lean.Level`/`Name` needs a scoped follow-up
implementation issue with a consumer and acceptance tests. None is selected by
this research. Ordinary Lean clients and multiple frontend routes remain intact.

## Artifact identity and compatibility obligations

For a persisted artifact, record this tuple, and reject a mismatch before
installation:

```text
(target repository + commit, local contract ID,
 syntax schema ID, judgment ID, interpretation ID + model parameters,
 primitive environment/dependency closure ID,
 producer/adapter source revision + artifact content digest,
 host Lean commit + library manifest, checker implementation revision/options)
```

For this experiment the syntax IDs are the two contract identifiers above;
the judgment is `CoreTyping.HasType` at the recorded conaled source revision,
the semantic contract is `GraphEmissionPure.ClosedDenotes` with native graph
interpretation at universe zero, and the operational fragment is the selected
beta reduct. The model is not the full old or new ConLeche judgment. The
reproduction evidence identifies the exact source digests. Host primitives are
not installed by this experiment, so its artifacts claim no primitive environment
fingerprint or checker acceptance. Production graph artifacts additionally need
the complete `GraphPrimitiveEnvironment` records and declaration dependency
closure, not merely a short hash or Lean version string.

An adapter needs four separate obligations:

1. **Representation:** scope, binder/level preservation, supported constructors,
   and a decoding roundtrip or explicit relation. Missing constructors reject.
2. **Judgments:** represented typing/conversion/declaration validity maps to the
   selected target judgment, with environment and annotation hypotheses visible.
   The two inverse syntax maps here prove none of this for upstream rules.
3. **Meaning:** the interpretation map preserves the chosen denotation or
   observation. Relative set models retain `SetTheory`, universe and primitive
   premises. Reflection or return to source requires its own theorem.
4. **Execution:** successful checker execution implies the represented judgment,
   and the supplied artifact/environment matches the checked input. Kernel
   acceptance, runtime execution and source correspondence are different claims.

Compose these only when the intermediate artifact, environment, model and
revision agree. Equality of names or AST constructor counts cannot discharge
those premises. The existing squares and relations support separate target
branches without erasing their different semantic assumptions.

## Upgrade and rerun policy

| Change | Required evidence before renewing compatibility |
| --- | --- |
| Host Lean or Mathlib | Fresh normal repository build/audit; rebuild and audit affected isolated closures; recheck host expression roundtrips, exact primitive records, installation and validator rejection fixtures. Rebuild any imported external checker/model proofs under that host. Old target IDs stay fixed if their specified rules have not changed. |
| Modeled target syntax, rules or denotation | New target contract ID; inspect primary-source delta, reprove affected representation/judgment/meaning bridges and their composition; retain binder, universe and unsupported-constructor cases. Re-run the corresponding target checker tests only where execution support is claimed. |
| Primitive metadata or environment | Reconstruct and compare complete records, closure and safety fields; rerun affected typing/meaning connections, installation and corrupted-record rejection. Do not silently accept new private helpers. |
| Adapter, serializer or checker implementation | Reprove affected refinement and rerun exact-input, roundtrip, rejection and execution tests. Pin compiler/runtime and options in execution evidence; a model-level theorem alone does not validate a changed binary. |
| Documentation only | Check citations and contract scope; no semantic compatibility renewal follows from editing a version label. |

Latest compatible Lean remains the default; a host upgrade can preserve a
modeled historical target. No full self-reflection or host consistency theorem
is required or claimed. The #107/#108 repair and independent-retest ownership
is unchanged, and no fresh theorem for either issue was chosen.

## Reproduction and statement review

Run from the repository development shell:

```sh
direnv exec . python3 experiments/host-target/check.py --jobs 2
```

The checker recompiles the complete local import closure into a temporary tree,
replaces `LEAN_PATH`, and appends the existing exhaustive current-module audit
to each copied source. It reuses `scripts/check.py` for compilation and source
guards. Only Lean's own installed libraries are external dependencies. See
[the checked evidence](../../experiments/host-target/evidence.txt). No main
library source or public import changed, so this affected-closure check covers
all new formal claims without rebuilding unrelated applications. Temporary
outputs are deleted; shared package checkouts are untouched.

Statement review: the inverse laws quantify over exactly the six constructors
and the singleton annotation domain. The beta theorem asserts equality of
capture-avoiding reducts, with no typing or upstream acceptance conclusion.
The square's observation parameter stays arbitrary, so syntax decoding is not
misrepresented as denotation. The graph theorem quantifies over every existing
graph declaration, reuses its proved typing and native meaning, and has no
upstream-acceptance premise. Its concrete forward instance establishes usable
inhabitants; the binder and universe cases exercise data that an incorrect
adapter could lose. No mathematical assumption is supplied by execution or a
native-evaluation axiom shortcut.
