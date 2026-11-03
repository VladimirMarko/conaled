# Bounded graph translation validation

Issue [#133](https://github.com/VladimirMarko/conaled/issues/133) adds a replay
validator sharing the [producer's contract](graph-emission-implementation.md).
It covers the graph source fragment, all `GraphTarget.Code` constructors, and
an explicit finite environment. It does not check arbitrary Lean programs.

## Certificate and checked relation

`GraphTranslationValidator.Certificate s` contains a format version and typed
`Code` instructions from the translated source premise to its translated
conclusion. These are executable derivation data. There is no acceptance proof,
`ArtifactDenotes` field, arbitrary semantic premise, or axiom constructor.
Substitution instructions use the existing finite typed variable assignments.
The format is an in-memory Lean datatype; no external byte parser is claimed.

`check` receives the source program, requested declaration name, primitive
environment records, actual `ConstantInfo`, certificate and node limit. It
checks the format, exact environment, theorem kind, name, universe parameters,
mutual-declaration names, decoded source type, decoded certificate body and
node limit, in that order. The accepted syntax uses only the bounded producer
fragment. The node limit counts reconstructed core nodes, not identifier bytes
or universe sizes, and is checked after reconstruction. It is not a bound on
checker runtime or protection against resource exhaustion.

`Validated` retains the exact source-translated type and declaration metadata,
as well as `ArtifactTyped` and `ArtifactDenotes`. `check_sound` derives this
relation from successful validation. `Validated.source` then obtains source
preservation through the existing formula comparison. Explicit type equality
prevents a different true proposition from being accepted as the intended one.
The certificate's code need not equal the source program's chosen code.

`GraphArtifactEquality` supplies proved structural comparisons. It compares
all fields of the supported primitive declaration kinds, including helper
bodies, universe names, mutual names, constructor metadata and recursor rules.
It rejects metadata expression nodes and unsupported declaration kinds. The
pinned environment is proved to compare successfully. These operations use
kernel-computable comparisons, not Lean's optimized expression hashes or
`BEq` as an unproved equality oracle.

The environment is the ordered projection of the host environment onto the
pinned primitive/helper declarations. The host may contain unrelated ordinary
Lean declarations. The validator rejects an extra, missing, reordered or changed
record in its supplied projection. It does not formalize host environment lookup.

## Distinct construction and composition

`GraphArtifactTransform.transform` consumes an actual theorem record. It
decodes its type and body, descends matching telescope binders, and inserts two
`Eq.symm` applications at an equality leaf. It does not consume `Code` or call
its traversal. The forward graph example proves by reduction that the output
matches an alternate replay certificate and that its body differs from the
original producer's body. The checker accepts that transformed artifact.
This supplies one checked transformed family; a general theorem for every
possible input to the raw transformer has not been claimed.

Binder labels have no de Bruijn binding significance. The general
`renameBinders_decodes` and `check_rename` theorems transport acceptance across
label changes without changing indices, binder info or the environment.
Neither admissibility rule allows unchecked binder permutations.

`validatedArtifactSquare` connects checked declarations to the same relational
representation as `producerSquare`. `checkedTargetSquare` composes the existing
source comparison with the validated source relation. `compose_preserves`
composes separately validated implications at a common source formula. The
round-trip example also checks a composed artifact whose certificate combines
the double-symmetry route with the backward producer route.

## Actual artifacts and retained boundaries

`Examples/GraphTranslationValidation.lean` installs the direct and transformed
forward declarations and a backward declaration through the existing kernel
installation path. It captures the installed forward records and the actual
primitive environment as literal Lean definitions. Kernel-checked equations
identify those records with the specified payloads and exact pinned environment;
`installedDirect_checked` and `installedTransformed_checked` prove successful
validation of the captured records. No acceptance equation is assumed, and
no `native_decide` or `#eval` supplies proof evidence.

The retained examples exercise heterogeneous carriers, concrete arithmetic,
a higher-universe caller, alpha renaming and composition. Kernel-checked negative
cases reject a well-typed opposite implication and a well-typed exchange of
same-sort binder roles at the type gate. Other cases reject changed helper
bodies, changed recursor metadata, an empty environment, a wrong name, a bad
certificate version, a mismatched certificate body and an insufficient limit.

The syntax decoder, bounded typing/denotation judgments, certificate replay,
comparison reflection and source preservation are proved in Lean. Installation,
reading the live environment, record reification, and compiled execution of the
checker remain host-driver boundaries. The generated definitions and their
acceptance equations are checked again by Lean's kernel. This is not a model
of `addDeclCore`, Lean's native runtime, or compiled checker execution. Relative
upstream-kernel acceptance remains a separate obligation under #128; this work
does not discharge the ConLeche/ConRon connection by assuming checker success.
