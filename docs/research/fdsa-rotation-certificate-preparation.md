# Binary rotation certificates: unqualified preparation

C05-093 under CTB-24 asks for an explicitly encoded decision problem whose true
instances have polynomial-size certificates checked in polynomial work.
This paper reconciles 18 November 2026 preparation by `/root/rotation_distance_cases`
with the later root fixed-width-threshold continuation. Neither design is
implemented or qualified by this curation. Current requirements and receiving status are tracked in [CTB](../textbooks/CTB.json): CTB-78 integration acceptance precedes resumed book formalization. This paper is not a Lean dependency or a receiving validation receipt.

## Existing minimum and precise scope

[Mixed execution](../../Applications/Trees/Rotations/Mixed.lean) and
[distance](../../Applications/Trees/Rotations/Distance.lean) already supply
actual partial moves, attained shortest traces, `distance_le_iff`, common-size
`Shape n`, and the 2N−2 connectivity bound. The [distance note](fdsa-rotation-distance.md)
and `Examples/RotationDistance.lean` retain the minimum-versus-route, empty,
repeated-label, disconnected-label and stale-position cases. The original
C05-091 proposal is therefore represented by those source owners, not repeated
as unfinished work here. The original C05-094 tariff/finite-mean proposal and
its distribution/absent-query controls are represented by
[the three-key note](fdsa-three-key-search-mean.md) and its actual example.
C05-092's [sharp-diameter preparation](fdsa-rotation-diameter-preparation.md)
remains a separate obligation.

The original author fully read Basic/Position/Bounds at donor 117 and extracted
the relevant FDSA printed 67/76 text from the 27 July 2026 PDF, SHA256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Its rendered-page attempt did not establish fresh visual inspection. The root
continuation fully reread the certificate section; it did not claim a complete
new reading of both earlier preparation papers. No current complexity-status
claim follows from the textbook's historical prose. The canonical requirement
is [C05-093](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md).

## Candidate binary certificate construction

The following route is feasible in outline and is consistent with the parent's independently suggested design. **Its parser, binary-fuel arithmetic, cost recurrence, erasure proof, and polynomial bound have not been implemented or proved.** Recording a polynomial formula without these links would not close the row.

### Explicit representation

Use a fixed finite alphabet. Encode shapes in preorder with one node symbol and one nil symbol: `encode nil = 0` and `encode (node () l r) = 1 ++ encode l ++ encode r`. Prove the parser/encoder round trip, exact consumed input, rejection of malformed/trailing material, and `length (encode t) = 2*t.numNodes+1`. Finite-alphabet delimiters can separate the two input trees and the threshold field.

Encode threshold `k` by bits, with an explicit end delimiter and a fixed convention for zero and leading zeros. A canonical little-endian bit list with empty zero was the initial option. The fixed-width continuation below permits leading zeros and removes the runtime canonicalization obligation; delimiters still make an empty zero field unambiguous. Either convention requires its specified decoder and cost proof. Do not expand binary `k` into a unary list of length `k`.

A certificate is a finite sequence of moves. Each contains one direction symbol followed by left/right path symbols and a delimiter. This representation has size proportional to the actual number of moves plus the sum of their path lengths. A unary path encoding is appropriate because a successful path has depth bounded by the explicitly represented tree size. That fact does **not** justify unary threshold input.

Specify a complete invalid-input policy: malformed trees, mismatched sizes, malformed binary threshold, unrecognized direction/path symbols, missing delimiters, trailing material, and illegal rotations must reject. Equality of final unlabelled trees is structural, with work proportional to their explicit encodings.

### Threshold fuel and actual legal verification

Thread binary fuel through a fold over the certificate, together with the current tree. For each move, the checker must both perform its actual partial rotation on the current tree and decrement binary fuel; it rejects if the fuel is zero. After the last move, it accepts exactly when the resulting shape equals the target.

An executable bit-list predecessor avoids an unproved unit-cost operation on an unbounded natural. Its required primitive facts include: zero fails; successful predecessor decodes to the predecessor natural; canonical form is preserved if required; bit length does not increase; and its actual measured elementary operations are bounded linearly by the current bit-list length (with a specified constant). A naïve arbitrary-precision `Nat` decrement charged as one step is insufficient. The source-cost model must count the concrete bit-list traversal and reconstruction, not only count calls to a hidden arithmetic oracle.

Likewise, charge position traversal and rebuilding, move parsing, shape parsing, and final structural equality. A node/path operation can cost one elementary constructor operation, because its arguments and return observation are explicitly structural; copying or comparing an entire tree must be charged by the traversed structure. Natural-number arithmetic may remain in the *mathematical proof of the bound* without being an uncharged operation in the executable verifier.

### Soundness and completeness

Soundness: an accepting certificate erases to a successful mixed trace between the decoded input shapes. Binary-fuel correctness proves its move count is at most the decoded `k`. By the actual minimum-distance theorem, distance is at most `k`.

Completeness: if distance is at most `k`, choose an attained minimum trace. Its length is also at most `2*N-2` by C05-091. Every intermediate state has `N` nodes by actual rotation preservation, and each successful move's position depth is bounded by `N`. Thus an explicit encoding of this trace has `O(N^2)` symbols. Each move consumes available fuel, every rotation succeeds in its own current state, and the final comparison succeeds.

The universal successful-position-depth bound still needs a proof from `applyAt?`; it must cover failure at nil and should not be assumed as a field. A coarser `≤ N` bound suffices. The shortest-witness existence theorem is essential when `k` is smaller than the length of the readily available normalizing route: a route upper bound alone does not yield completeness for all true thresholds.

### Work bound and the chosen complexity statement

Let `M` be explicit input-symbol length and `W` certificate-symbol length. The two tree sizes and binary-fuel bit length are bounded by `M`. A direct measured checker can plausibly satisfy a bound of the form `C*(M+W+1)^2` (a larger proved polynomial is acceptable). The proof must actually derive its coefficients/degree from the parser, predecessor, `applyAt?` and equality recurrences. This displayed polynomial is an unproved design target, not a result.

For a standard verifier polynomial in combined input-plus-witness length, prove a uniform work bound for *every* input/certificate, including malformed and overlong certificates, and separately prove every yes-instance has a polynomial-size witness. Early failure must not cause an unbounded auxiliary operation. Alternatively a bounded checker may reject certificates once they exceed a polynomial budget derived from input shape length; if chosen, specify how that budget and its exhaustion are implemented in polynomial work. A list budget derived from explicit input length is allowed; a list derived by expanding the numeric value of binary `k` is not.

If the intended final theorem is membership in a preexisting formal complexity class, a further encoding/machine-cost bridge is needed. Do not label a source-level measured checker as a completed formal machine-level NP theorem without that bridge. Conversely, avoid adding an unproved structure field called `polynomialTime` merely to restate the desired conclusion. Resume by checking the repository's existing resource and encoding abstractions before deciding the narrowest complete theorem that meets the canonical polynomial-checkability obligation.

### Consequential expected cases

| Input/certificate | Expected result | Reason |
| --- | --- | --- |
| Empty source and target, binary zero, empty certificate | Accept. | Distance is zero and no rotation is required. |
| Equal nonempty trees, zero threshold, empty certificate | Accept. | Equality is an actual zero-length witness. |
| Distinct shapes, zero threshold | Reject every certificate. | Empty trace has the wrong endpoint; a nonempty trace exhausts zero fuel. |
| Distinct two-node shapes, threshold one, correct root move | Accept. | One legal rotation witnesses distance one. |
| The same pair, wrong direction | Reject. | The required child is missing. |
| Legal rotation and inverse, threshold one | Reject. | Two actual moves exceed the threshold even though endpoints agree. |
| The same two-move cycle, threshold two | Accept if the stated source and target coincide. | A verifier checks a witness within the threshold; it need not require the certificate itself to be shortest. |
| A large binary threshold with a short valid witness | Accept without unary expansion. | Runtime depends on bit length, not the threshold's numeric value. |
| A binary power of two decremented across trailing/low zero bits | Correct predecessor, measured linear bit work. | Exposes borrow propagation and hidden arithmetic costs. |
| Different tree sizes | Reject. | Rotations preserve node count. |
| Malformed preorder encoding or trailing bits | Reject. | Parsing must consume exactly the declared input. |
| An invalid position in a later state | Reject at that move. | Initial-state-only checking is unsound. |
| A true threshold smaller than the chosen normalization-route length | Some shortest certificate still accepts. | Completeness depends on minimum existence, not a fixed construction's length. |

Concrete example inputs for the final two rows remain to be chosen and independently checked. No current test run is claimed.

## A simpler explicit binary threshold representation

Permit leading zeros and use a fixed-width little-endian bit list. Its width is
the actual threshold field length. The grammar explicitly permits both an empty
zero field and nonempty all-zero fields. No runtime canonicalization is needed.
The mathematical value function is used to state and prove the contract; the
verifier operates on bits rather than converting the threshold to a natural
number or expanding its numeric value.

A partial predecessor can follow these equations:

* Empty input fails.
* On `true :: tail`, return `false :: tail`.
* On `false :: tail`, recursively decrement the tail, fail if it fails, and
  otherwise return `true :: decrementedTail`.

This algorithm preserves the complete bit-list length on success, permits
noncanonical leading zeros, and needs no deletion of high zero bits. Its desired
proved contract is: failure iff mathematical value is zero; success has value
exactly one smaller and the same width. A successful branch beginning with true
reuses its tail. A false branch follows borrow propagation and rebuilds only the
visited prefix. With explicitly charged pattern, branch, Option and constructor
events, the work is at most a fixed constant times width plus a constant.

The arithmetic proof is direct. For a true low bit, changing it to false changes
`1 + 2*v` to `2*v`. For a false low bit, a successful recursive result has value
`v-1`, and the returned value is `1 + 2*(v-1) = 2*v-1`; recursive success supplies
`v>0`, so the natural subtraction step is justified. These are intended proofs,
not checked Lean declarations. They preserve the original binary-threshold
requirement while avoiding an unnecessary canonicality invariant.

## Keep runtime work structural

The verifier need not compute the two tree sizes merely to reject unequal-size
inputs. Actual successful rotations preserve size, and structural comparison of
the final tree with the target will reject any unequal-size pair. Prove that
rejection semantically for every certificate. If an explicit early size test is
chosen, its actual traversal and number representation must also be charged.
Do not silently introduce unit-cost unbounded natural arithmetic for that test.

Use a fixed finite alphabet with distinct tags for shape syntax, threshold bits,
rotation direction, path branches and field/move delimiters. Its particular
number of symbols is a routine encoding choice, but the actual parser and
malformed-input policy must be explicit and proved. A tree parser must consume
its prefix exactly and preserve the remaining suffix; repeated reparsing or a
termination implementation that traverses the full remaining input at each
recursive call would need to be included in the work bound. Inspect existing
parser/encoding abstractions before selecting its Lean definition. No existing
parser implementation was inspected or claimed reusable here.

## Bound decomposition to prove on the actual measured checker

Let M be actual input-symbol length, W actual certificate-symbol length, n the
decoded source node count and b the threshold bit width. Valid input syntax
bounds n and b by M. Parsing is charged on the actual traversed symbols. Each
parsed move decrements at most b bits and executes its partial rotation on the
current tree, traversing/rebuilding only the selected path. Successful prior
steps preserve n. Failed path/rotation execution is also bounded by that tree's
size, with its actual failure work retained. Final equality traverses explicitly
represented trees. Thus a suitable uniform bound can be derived from

`C * (M + (n + b + 1) * W + n + 1)`

and then bounded by a polynomial in M+W+1. This is a proposed decomposition, not
a proved coefficient, recurrence or runtime result. The bound must cover every
malformed/overlong certificate as well as successful runs. All constants must
come from the eventual measured recurrences.

For completeness, use an attained minimum legal trace from the accepted distance
interface, not just the longer normalization route. At most 2*n-2 moves suffice
for nonempty equal-size shapes, and each successful path has length at most n
once that depth theorem is actually proved. Direction/path/delimiter encoding
therefore has a quadratic witness-size bound in n, including fixed per-move
overhead. The zero-node case has the empty trace. Keep the actual minimum below
the supplied threshold when choosing the witness.

The final source-level polynomial-checkability result still needs exact syntax,
parser round trips, bit predecessor, partial-execution erasure, length bounds,
soundness, completeness and measured work proofs. A formal machine-level NP
claim additionally needs the relevant machine/cost bridge; no such bridge is
assumed here. No part of this note closes C05-093 or changes the full sharp
diameter obligation C05-092.
