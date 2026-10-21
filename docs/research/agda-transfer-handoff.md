# Frozen identity-fragment author handoff

This handoff accompanies the #105 first proof. Use the reviewed #105 repository
snapshot identified by the review/tracker record, not a moving working tree.
Read [the implemented interface](agda-transfer-interface.md) and
[source attribution](agda-transfer-source-notice.md). The first port is
`tr-concat`; this document does not select or prepare a second theorem.

## Imports and checked starting points

```lean
import SquareKit.GroupoidTransport
open SquareKit.GroupoidTransport.Authoring
```

The named source operations are `transport hΓ p b`, `concat hΓ p q` and
`trConcat hΓ p q b`. The arguments are generated source data, with named
endpoints inferred from their types. The ordinary theorem is
`SquareKit.GroupoidTransport.transport_concat C B p q b`.

Read these compiling modules for the corresponding use:

- `Examples/AgdaTransferCaller.lean`: complete source call, typed renaming,
  simultaneous substitution, and generalized reflexive computation.
- `Examples/AgdaTransferModels.lean`: the same source proof in faithful C₄
  translation and trivial `Fin 2`, with retained arrow labels.
- `Examples/AgdaTransferDiagnostics.lean`: rejected unsupported source
  formation, host-function injection and equality reflection.
- `SquareKit/Internal/PathTransport/Transfer.lean`: the translated proof,
  using the generalized `TransferFrame.command` and named application.
- `SquareKit/Internal/PathTransport/Authoring.lean`: generic motive and
  contextual `PathCommand` interface. New proofs may need this lower layer.

`SquareKit/Internal/PathTransport/Typed.lean` defines the exact supported
source judgments. Native Lean functions may construct source syntax uniformly;
they cannot serve as source terms without generated typing evidence. Source
identity, judgmental conversion, native equality of raw syntax, and semantic
annotation equality are different operations. Do not replace a missing source
conversion by a target equality.

## Commands

Use the pinned Nix shell as described in `README.md`. From the repository root:

```sh
direnv exec . lake build SquareKit.GroupoidTransport Examples.AgdaTransferCaller Examples.AgdaTransferModels Examples.AgdaTransferDiagnostics
direnv exec . lake env lean YourCaller.lean
direnv exec . ./check.sh
```

The first command prepares imports and checks the retained examples. The
second checks a new caller. The last rebuilds fresh sources and audits all
local proof roots through the normal public entrypoint. No Agda build or
external checker is part of these commands. Only the existing approved
`propext`, `Classical.choice`, and `Quot.sound` kernel axioms are permitted.

## Independent baseline protocol

The #106 author must be independent of framework implementation, first-port
work and reviews. Start a fresh session with only this frozen public snapshot
and handoff. Do not pass private implementation conversations, unpublished
helpers, a selected solution, or coaching into that session. The author may
inspect the public source and documentation.

Before starting the proof, the independent author selects a theorem and records
its exact declaration, upstream revision, license, dependency closure, intended
conclusion and applications, plus a prospective effort budget and stopping
rule. Obtain an independent scope check without a solution, then freeze the
candidate and protocol. During the baseline, keep the frozen API read-only and
record the attempted caller, errors and results.
Separate proof translation from any proposed framework additions, dependency
investigation and debugging. Do not infer costs from line counts or elapsed
machine time. Preserve unsuccessful attempts and the exact unsupported
operation if the fragment does not suffice. Archive the baseline before any
API repair or assisted correction; label subsequent assisted work separately.

If implementation context or a solution contaminates an attempt, replace the
author with an unexposed author, and choose a new scoped theorem if its solution
leaked. An assisted retry is not an independent baseline. The independent author selects the
second theorem under the #106 scope protocol; the first-port implementers do
not select it or coach the proof. No second-proof skeleton or theorem-specific
helper is included here.

## Known boundary

There is no Agda parser, general proof tactic, internal Π, universe,
univalence, modality, crisp rule, K/UIP or equality reflection. The supported
model is ordinary groupoids with a set-valued primitive family. The source J
rule admits finite dependent tails, but a new named motive may still expose
typed-context bookkeeping. General context-presentation conversion and a
standalone arbitrary concat-code reindex theorem are not public operations.

Report a missing interface rather than inserting a host proof or silently
changing the selected theorem. The existing first-port design record documents
framework work performed to make its own named caller compile; independent
usability has not already been established by that work.
