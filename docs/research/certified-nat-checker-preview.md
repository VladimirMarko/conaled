# Certified natural-number checker from checkpoint 233

The restricted natural-number checker and its source-agreement closure can be
reproduced independently of the unfinished sixteen-queens numeral proof. This
bounded #137 slice preserves the supplied source, connects its endpoint to an
existing commutative square, and exercises a different natural-number function.
It does not complete #137 or restart the stopped #149 reconstruction.

The [portable reproduction](../../experiments/certified-nat-checker/README.md)
extracts a frozen selection from the repository's
[checkpoint-233 archive](../history/algorithm-design-haskell/README.md).
[Selection metadata](../../experiments/certified-nat-checker/selection.json)
records all 20 members, hashes and direct imports. Thirteen were selected by the
supplied checker gate; seven are original source prerequisites that its recorded
run obtained from prepared objects. The current path builds all twenty fresh.

## Source and semantic correspondence

`CertifiedNatChecker.Endpoint source` contains a name, executable `Nat → Nat`
and universal equality to the source function. Parsing admits exactly four
canonical tokens, with natural operands spelled through `Nat.repr`. Checking
compares the certified implementation's result with the claimed value. The
universal acceptance theorem derives both the exact rendered token list and the
source equation from actual acceptance. Constructing an endpoint requires its
implementation proof; a request cannot provide another function or proof.

The generic name is only a label. `QueensNatChecker` constructs the actual source
binding to `ADWH.Chapter15.Queens.BitRepresentation.cqueens`. Its implementation
is `FirstOrderNat.SourceBridge.cqueens`, whose equality proof passes through
finite-fold uniqueness and `NatCounting.cqueensNat_eq`. The new checked client
also states that exact imported-source equality, using the endpoint's proof
field. It does not evaluate any queens instance. Agreement for all natural
inputs refers to the fixed Word16 source; mathematical counting theorems retain
the original width hypotheses, including `n ≤ 16` where required.

The selection deliberately uses the supplied scoped `QueensBitCounting`. The
portable selector replays the historical character edits in reverse and checks
byte equality with the original file and its SHA-256
`5c2a18183ca1525fb8dd98122d1ab4e37da51dc8c87e9907f0fdc447dd71e897`.
Those edits omit the `QueensExamples` import and three convenience numeral
theorems, add synchronous elaboration, and append axiom reports. The executable
counting definitions and symbolic theorems retain their source text. This byte
comparison is distinct from checking the selected dependency closure, which the
fresh compilation and audit perform.

## Reuse and checked client

[CheckerClient.lean](../../experiments/certified-nat-checker/CheckerClient.lean)
keeps the native endpoint interface. `endpointSquare` interprets its equality
law as an ordinary `Squares.Square` between identity representations of natural
numbers. `Squares.compose` combines it with a successor consumer. No new
categorical interface, universal IR, or replacement for the native parser is
introduced.

The independent specification is `n + n`, with executable realization `2 * n`.
`Nat.two_mul` discharges the endpoint obligation for every natural number.
`doubleThenSuccessor_correct` uses the composed square's law to obtain
`(n + n) + 1`. The token consumer returns the checked claim's value plus one;
`report_sound` uses the supplied acceptance-soundness theorem to connect that
value with the composed specification. Its acceptance premise is separately
witnessed by the canonical request `double 3 = 6`, which yields seven, and by
`double 0 = 0`. The public canonical theorem proves acceptance from these
independently expected arithmetic results.

Rejection claims through the public canonical and noncanonical contracts cover a false result, different endpoint name,
different operator, leading-zero numeral and extra token. These are ordinary checked proofs through the supplied API and standard string
lemmas, without native evaluation.
They do not establish execution correctness for a compiled checker binary.

## Evidence and validation boundary

The [initial reproduction record](../../experiments/certified-nat-checker/evidence/initial-reproduction.json)
records a fresh twenty-module investigation with the pinned Lean 4.35.0 compiler,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The archive hash is
`8a5e2b2d5535a149a67111c6adf9ba9e173cbbd2a986d63dc702d75178252e63`.
The authoritative hash is also checked by the selector and archive metadata.
The twenty compile processes took 7.225 seconds in aggregate. The initial
[exhaustive audit](../../experiments/certified-nat-checker/evidence/initial-audit.txt)
covered 1,144 safe declarations, including 787 theorems, with only `propext`,
`Classical.choice`, and `Quot.sound`, and no unsafe runtime exclusions. Peak child
RSS across compilation and audit was 1,569,416 KiB. These are host-specific
measurements, not runtime complexity or throughput claims. The initial record
predates the new client and is not its validation receipt.

Initial attempts under a 4-GiB virtual-address cap failed during Lean startup;
the coordinator authorized 8 GiB, under which compilation succeeded. The initial
auditor adaptation needed an explicit `Lean` import; its first failure occurred
after all source modules had compiled. The portable version instead reuses the
existing parameterized `ClosureAudit` directly. Its generated command names every
selected module and both new/native client dependencies as local roots, so
source-authored unsafe declarations are rejected. It retains source-policy
checks as well as the transitive axiom audit. Final candidate validation must run
the documented portable command; a main-library check does not cover this tree.

## Remaining #137 obligations

The earlier finite-order certificate experiment remains accepted within its
own contract. It is neither replaced by this client nor evidence of inspecting
all incoming kernel experiments. `EXT-137-001` remains open for the broader
preview inspection and reproduction.

| Supplied work | Disposition after this slice |
| --- | --- |
| Restricted Nat parser, evaluator/source agreement and original prerequisites | Exact source selection, inverse correspondence and fresh reproduction; native endpoint retained and independent client added. |
| Reflection/involution and original first-row counting routes | Initial source assessment retained; their complete selections, prepared dependencies and reported external numerical runs are not reproduced here. |
| Strong-CSP normalization/checker/producer | Initial source review retained. The fixed n8 endpoint's absent generated proof module and unexecuted producer remain separate evidence gaps. |
| Word112 and Interpreter185 complete runs | Supplied failures remain failures; accepted prefixes do not validate complete selections. No rerun or repair here. |
| Installed/GroupChecked and kernel integration | No adoption or completed integration claim; inspect the actual remaining source/trust contracts before scheduling implementation. |
| Stock `cqueens 16 = 14772512` | Remains unfinished in this preview. Not attempted by this slice. |
| Arbitrary Lean imports, modified host kernel, compiled checker binaries | Separate commitments, not consequences of parser soundness or fresh source checking. |

The endpoint is reusable when a natural-valued implementation already has a
universal source-agreement proof. Its four-token parser and numeric equality
checker do not by themselves justify owning a growing Lean fragment checker.
This slice provides a concrete source-preserving client and composition path;
the broader value comparison and external-kernel inspection remain with #137
under #128, coordinated with #235. It creates no new theorem-selection work for
#107/#108.
