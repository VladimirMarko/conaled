# Rotation certificates: contracts and remaining mathematics

CTB-24/FDSA-5-93 asks for an explicitly encoded rotation-distance decision
problem with polynomial-size witnesses and polynomial verification. The supplied
source now connects raw word/binary verification to finite controllers, native
tape simulations and a conventional verifier criterion. Receiving acceptance
evidence is tracked under #713 separately from the historical checks.
FDSA-5-93 stays open.

Use the [integration and next-work map](textbook-machine-integration.md) for
source families, unfinished drafts and acceptance. The
[exact final preparation](../history/textbooks/handover-2026-11-25/received/current/source/docs/research/fdsa-rotation-certificate-preparation.md)
preserves the complete derivations, literal expectations and embedded historical
records. The [cumulative requirements](../history/textbooks/handover-2026-11-25/received/current/control/requirements.md)
and [fixed expectations](../history/textbooks/handover-2026-11-25/received/current/research/fixed-expectations/certificate-research-EXPECTATIONS.md)
remain source requirements. This maintained paper selects their mathematical
contracts rather than repeating the operational record.

## Source correspondence and semantic boundary

The canonical [FDSA Chapter 5 ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md)
owns FDSA-5-93. The original preparation used printed pages 67 and 76 of the
27 July 2026 PDF, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The original rendering attempt did not establish fresh visual inspection.
Later source-reading attributions remain in the preserved paper; this curation
claims no new primary-source reading or present research-status conclusion.

[Mixed rotations](../../Applications/Trees/Rotations/Mixed.lean) supplies actual
partial moves at state-dependent positions and their sequential execution.
[Distance](../../Applications/Trees/Rotations/Distance.lean) supplies an attained
minimum on `Shape n`, the threshold/existence equivalence and the empty-safe
natural bound `2*n-2`. The [distance paper](fdsa-rotation-distance.md) preserves
empty, repeated-label, disconnected-label and stale-position distinctions.
FDSA-5-92's [eventual exact diameter `2n−6`](fdsa-rotation-diameter-preparation.md)
is a separate mandatory obligation. FDSA-5-94 belongs to the
[three-key mean paper](fdsa-three-key-search-mean.md).

## Source-event observation

The measured source programs charge one for recursive primitive/parser entry,
one for a newly constructed list cons or tree node, and one for a returned
Option or Boolean literal. Nil, finite tags, projections, control packaging,
aliases and reuse of an existing return value are free; measurement arithmetic
is bookkeeping. Each component's exact wrapper charges remain in its source.

These are declared source events. Machine time, allocation, physical sharing,
bit work and visited space require their own contracts. The executed programs
traverse actual data and bind actual returned results; mathematical lengths,
node counts, decoded fuel and distance belong to proofs, not free runtime
oracles.

## Raw parsing and binary fuel

[FixedWidth](../../Applications/Resources/BinaryCounter/FixedWidth.lean) retains
little-endian fuel width, including empty and redundant high-zero words.
Decrement fails exactly at numeric zero; success preserves width and reduces
value by one. Its raw work bound is `3*b+2`. It does not normalize the bits or
expand the threshold into unary data.

[Execution](../../Applications/Resources/RotationCertificate/Execution.lean)
implements partial root/positioned rotations and left-first structural equality.
Successful rotation at depth `d` costs `3*d+5`, with `d+2≤n`; raw execution costs
at most `3*n+3`. Equality costs at most `3*sourceNodes+2`, retaining skipped-right
short circuits and actual callback results.

| Parser | Exact successful work | Every raw input |
|---|---|---|
| Bits of width `b` or path of depth `d` | `3*b+2` or `3*d+2` | `3*length+2` |
| Move at depth `d` | `3*d+4` | `4*length+2` |
| Tree of `n` nodes | `7*n+3` | `5*length+2` |
| Whole input with sizes `ns,nt` and bit width `b` | `7*ns+7*nt+3*b+15` | `20*(length+1)` |

[LinearParser](../../Applications/Resources/RotationCertificate/LinearParser.lean),
[TreeParser](../../Applications/Resources/RotationCertificate/TreeParser.lean)
and [InputParser](../../Applications/Resources/RotationCertificate/InputParser.lean)
state recognition for arbitrary raw words. Tree success is equivalent to
`raw = treeCode tree ++ rest`, determining both tree and untouched suffix.
Whole-input success is equivalent to its exact code, including the actual fuel
bits and final EOF. Unequal endpoint sizes are syntactically valid and rejected
semantically by rotation preservation and final equality.

The tree parser separates recursion over the input tail from recursion over
pending frames. A frame awaits a left child or retains an actual returned left
child while awaiting the right. The mathematical stack-prefix invariant proves
recognition; the potential `2*frames.length` pays for resumes on malformed input.
Each successful move consumes exactly `depth+2` symbols, supplying strict suffix
decrease without a runtime length traversal. Emitter/parser round trips bind
actual measured outputs. Missing children, missing or repeated separators,
reserved tags and trailing input remain covered by
[parsing clients](../../Examples/RotationCertificateParsing.lean).

## Streaming acceptance and attained witnesses

[Streaming](../../Applications/Resources/RotationCertificate/Streaming.lean)
checks EOF by actual structural equality. Otherwise it executes predecessor,
move parser and positioned rotation in that order, then recurses on their actual
returned fuel, tree and suffix. Every failure stops immediately. A certificate
move after the target was already reached is still parsed, charged and executed.

Its raw acceptance equivalence is:

```text
checkStreamRun bs s t cert accepts iff
  ∃ moves, cert = certCode moves ∧ applyMoves? moves s = some t
    ∧ moves.length ≤ value bs.
```

The statement assumes no syntax validity, positive fuel, equal endpoint sizes
or canonical bit width. Soundness reconstructs actual consumed prefixes;
completeness follows a successful bounded trace. With width `b`, source size `n`
and certificate-symbol length `W`, the all-input stream bound is
`(3*b+3*n+12)*W+3*n+6`. The proof pays for disjoint consumed prefixes, including
borrowing, parsing, reconstruction and equality.

[Witness](../../Applications/Resources/RotationCertificate/Witness.lean) defines
`Yes` from explicit shape input codes and actual minimum distance, independently
of executable acceptance. A successful trace's encoding has length at most
`moves.length*n`. Selecting an attained minimum gives size at most `n*(2*n-2)`
and satisfies the supplied threshold. A fixed normalization route alone need
not satisfy that threshold. The connected three-node case retains this distinction.

[Verifier](../../Applications/Resources/RotationCertificate/Verifier.lean)
parses the entire input, then calls the stream with its actual returned values.
It accepts exactly the independent encoded bounded traces, is sound for `Yes`,
and supplies an accepted witness of at most `2*input.length^2` symbols for every
`Yes` input. Every raw pair has work at most
`32*(input.length+certificate.length+1)^2`. Input parsing failure leaves the
certificate unvisited.

## Binary representation and conventional pair input

[BitCodec](../../Applications/Resources/RotationCertificate/BitCodec.lean)
uses four least-significant-first bits per `Fin 16` tag. All sixteen complete
blocks decode, including reserved tags 11–15; syntax checks reject those later.
Decoding fails exactly when raw bit length is not divisible by four. Whole-word
packing costs `6*N+1`; unpacking a complete code costs `4*N+2`, with raw bound
`bits.length+2`. Partial final blocks remain covered.

[BinaryVerifier](../../Applications/Resources/RotationCertificate/BinaryVerifier.lean)
decodes the input, parses its syntax, decodes the certificate, then runs the
stream. Certificate decoding is eager: token-stream untouched-tail statements
do not imply an untouched bit tail. Its independent language `BinaryYes` means
a complete binary code of a `Yes` word. Acceptance is equivalent to exact raw
input/certificate codes of a successful threshold-bounded trace. Accepted
witnesses have at most `I²` bits, and every raw pair has source work at most
`40*(I+C+1)^2`.

The machine development separately implements framing, parsers, fuel, equality,
rotations and controller cleanup. The
[conventional verifier](../../Applications/Resources/TuringSimulation/ConventionalVerifier.lean)
uses a fixed finite machine before quantifying over raw input. The application
[BinaryYesVerifier](../../Applications/Resources/RotationCertificate/BinaryYesVerifier.lean)
connects it to literal pairs
`input.map some ++ [none] ++ certificate.map some`. Missing, repeated and
malformed delimiters have raw rejection obligations. The witness bound remains
`I²`, giving total pair length at most `I²+I+1`.

Raw `[]`, the valid empty pair `[none]`, and an encoded zero-node instance are
different inputs. The first lacks a delimiter; the second has empty instance
bits and is outside `BinaryYes`; the third is a nonempty encoding that may
accept an empty trace. The verifier criterion is explicit. Its identification
with an independently defined nondeterministic NP class remains separate work.

## Machine contracts and unfinished space arguments

The [machine map](textbook-machine-integration.md#source-families) locates native
TM2/TM1/TM0, ordinary-input and combined print/move owners. Preserve actual
transition counts and complete configurations, including register defaults,
all stack tracks, marker cells, raw rejection cleanup and final output. A live
halt configuration and a later outer-none observation are distinct events.

[VisitedSpace](../../Applications/Resources/TuringSimulation/VisitedSpace.lean)
contains live-prefix composition of configurations, full selected commands and
integer coordinates. The suffix starts at the actual prefix coordinate;
identical tapes alone do not prove equal displacement.

The preserved [normal-dispatch draft](../history/textbooks/handover-2026-11-25/received/current/research/space155/next/README.md)
proposes a stationary self-write and one actual primitive step, including loads
and register-dependent branches. The
[InternalHeight draft](../history/textbooks/handover-2026-11-25/received/current/research/height156/README.md)
follows old/new selected-stack heights along the actual source path. Both remain
uncompiled and uninstalled. `InternalHeight` neither follows a goto into a new
body nor bounds unrelated initial tracks. The reserve condition
`∀ j, length(S j)+actionBound q≤H` is sufficient, not necessary; empty selected
peek with `H=0` and another track of length four distinguishes them.

The [geometry plan](../history/textbooks/handover-2026-11-25/received/current/research/space154/PLAN.md)
still requires local outward/action/return coordinate traces, preservation of
the marker and other tracks, source-run composition, finite-control command
transport and interval cardinality. The proposed marked-simulator interval
`[-1,H]` and span `H+2` are unproved. Ordinary reflection, delimiter preprocessing
and combined print/move excursions require separate coordinate arguments.
Neither the existing time-derived bound nor endpoint equality supplies them.
