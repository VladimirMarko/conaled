# Canonical inverse specialization costs

[#693](https://github.com/VladimirMarko/conaled/issues/693) delivers a canonical
inverse consumer at the actual integer admission. Naming the complete witness
with an explicit type makes the existing whole-path comparison usable at the
default budgets. The shared constructor and comparison proof are unchanged.
The supplied-witness consumer remains available; no client migration is required.

## Mathematical contract

[NativeCanonicalInverse](../../Examples/NativeCanonicalInverse.lean) uses the
pointed-endomorphism systems and nonidentity integer shift from
[NativeStructureCoherence](../../Examples/NativeStructureCoherence.lean).
For an admission of the constant `ULift ℤ` family, `witness` is exactly
`move.witness.selectedInverseEquivalence`, using the admitted code's native
filling and its lawfulness proof on both sides. Its type is
`HomotopyEquivalence move.witness.selectedInverse`. It retains the selected
inverse, inverse data and contractions; it does not substitute the independently
constructed `HomotopyEquivalence.ofIso` witness used by the direct client.

`comparison` applies the existing `Coded.inversion` to that named witness.
Its inferred type is a term of a path between two whole selected structure paths:

- `Coded.path (move.inverseWith witness …)`, from system 1 to system 0;
- `homogeneousReverse (Coded.path move)`, with the same endpoints.

`actualComparison` specializes this to
`NativeLatticeTransport.Presheaf.admission (Γ := Γ) ℤ`, for every context `Γ`.
This is an actual inhabited admission, not a new assumption of the desired
comparison. The retained `Inspect.lean` run prints both elaborated types in
[results.json](canonical-inverse-costs/results.json). The comparison still uses
the original selected univalence paths; it is not an endpoint equality or an
existential replacement. Naming the witness discharges the measured need for a
proof boundary without adding a duplicate inverse algorithm or a generic helper.

## Frozen evidence and method

The unchanged failure source is
[ExampleCanonicalExplicit.lean.txt](native-structure-coherence/ExampleCanonicalExplicit.lean.txt),
SHA-256 `68b11cf9806ce79c65507ac42d9fd755fcd379bfb91e49af1327a4eea9cea181`.
Historical measurements use base `eb595d46179a48dfc3d1850e5051d33da04b7ffd`.
After the independent comma-interface integration, additional runs use
`511f0c89a041ed6a72538b9dbe506eaa26f74022`; their tags start with `integrated-`.
The earlier measurements remain attributed to their original base.

Both use Lean 4.35.0, compiler commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
The Linux 6.18.58 laptop has an Intel Core i9-14900HX, 32 logical CPUs and
65,541,744 KiB reported RAM. Per-run load averages, timestamps, source hashes,
commands and logs are retained. Other laptop activity was uncontrolled; Lean
probes were serialized with `flock`. These are local bounded observations, not
stable performance thresholds or measurements of author effort.

[measure.py](canonical-inverse-costs/measure.py) records child user/system CPU,
monotonic wall time, peak RSS in KiB, async setting and resource bounds. It also
records `CLOCK_BOOTTIME` minus monotonic elapsed time to expose suspension.
The retained runs show no material suspension gap. Shell setup and lock waiting
precede the measured child. Polling and process termination can slightly exceed
the requested wall bound. A harness exit of zero only means a record was written;
the Lean outcome is its `exit_code` and `wall_timeout`.

The initial compact harness is retained verbatim in the JSON. An intermediate
portable version used by the actual-admission batch was rewritten before its
exact bytes were saved. Its commands and results survive, but its exact wrapper
identity is unavailable. The current readable wrapper is checked with a passing
public consumer, a bounded timeout control, and a new matched comparison after
integration. This provenance limitation is not silently repaired by attributing
old runs to the current script.

## Matched comparisons

Default runs explicitly set depth 512 and 200,000 heartbeats. Larger runs set
1024 and 400,000 respectively. Each route in the main historical comparison has
two repetitions at each budget, a 30-second wall bound and the default async mode.
The supplied and named-witness probes differ from the frozen source only at the
inverse witness boundary. All invoke the same `Coded.inversion` contract.

| Historical route | Outcome, two runs at each budget | Wall seconds | User + system CPU seconds | Peak RSS KiB |
| --- | --- | --- | --- | --- |
| Inline canonical witness | All four wall-bound failures | 30.08–30.11 | 29.70–30.12 | 3,690,248–3,791,360 |
| Independently supplied complete witness | All four pass | 0.80–0.90 | 0.89–1.04 | 2,227,884–2,230,464 |
| Named, typed canonical witness | All four pass | 0.80–0.85 | 0.86–0.94 | 2,226,432–2,229,636 |
| Supplied witness, actual integer admission appended | All four pass | 0.75–0.81 | 0.84–0.91 | 2,225,492–2,230,156 |
| Named canonical witness, actual admission appended | All four pass | 0.75–0.81 | 0.84–0.87 | 2,225,940–2,230,408 |
| Public canonical client, including actual admission | All four pass | 0.65–0.71 | 0.67–0.73 | 2,224,120–2,224,940 |

The first three rows compare parameterized admissions. The actual-admission rows
append the same concrete specialization, preserving the full contract. Appending
it to the inline canonical probe still timed out at the earlier declaration;
that run does not establish a separate cost for concrete specialization.
An additional synchronous inline run also reached the wall bound. No retained
failure emitted a deterministic recursion-depth or heartbeat diagnostic.
Increasing the tested budgets therefore did not resolve this observed failure,
but these runs do not identify a precise elaborator or kernel hotspot.

The post-integration matched runs retain the frozen inline source and compare it
with both actual-admission probes, again twice at each budget. Their complete
records are in the JSON: all four inline attempts reached the wall bound, while
all eight actual-admission attempts passed. The short timeout control is a harness check, not an
additional mathematical or performance comparison.

## Unsuccessful explicit return types

Writing the full whole-path return type explicitly on the public comparison
also reached the 30-second bound. `PublicTyped.lean` isolates that behavior before
the concrete admission is appended. Adding explicit code arguments, then explicit
structure arguments too, did not make the retained trials pass. The witness-only
probe and the inferred comparison both check. The successful public declaration
therefore lets Lean infer the exact type of `Coded.inversion`; inspection confirms
that no endpoint or contraction obligation was removed.

The JSON retains `PublicTyped.lean`, `PublicAllArguments.lean`,
`public-without-equality.lean.txt`, `public-explicit-codes.lean.txt`, their outcomes,
and the interrupted first public attempt. That first attempt has ambiguous
source-read timing and no reliable CPU/RSS record, so it is excluded from cost
comparisons. Its additional reflexivity lemma was not isolated as the cause.
No failure here establishes a mathematical obstruction.

## Replay and decision

Extract any saved source by name, preserving its hash:

```sh
direnv exec . python3 - <<'PY'
import hashlib, json
from pathlib import Path
r = json.loads(Path('docs/research/canonical-inverse-costs/results.json').read_text())
out = Path('/tmp/canonical-inverse-replay')
out.mkdir(exist_ok=True)
for name, item in r['sources'].items():
    data = item['text'].encode()
    assert hashlib.sha256(data).hexdigest() == item['sha256']
    (out / name).write_bytes(data)
PY

direnv exec . flock /tmp/conaled-native-followups-lake.lock lake env python3 \
  docs/research/canonical-inverse-costs/measure.py \
  /tmp/canonical-inverse-replay/BoundaryActual.lean \
  --output-dir /tmp/canonical-inverse-replay --tag boundary-default-1 \
  --depth 512 --heartbeats 200000 --wall 30
```

Use the retained base and dependency pins for a historical replay; replay on a
newer checkout is a new observation. Repeat with `Canonical.lean` and
`SuppliedActual.lean`, then with depth 1024 and 400,000 heartbeats. `--sync` selects
the separate async-disabled diagnostic. Public-client correctness also belongs
to the normal integrated build and exhaustive axiom audit.

Adopt the typed canonical witness boundary for this client. Retain the existing
supplied-witness route and shared general proofs. No resource override or default
budget change is needed for the delivered client. The remaining explicit-type
cost belongs under [#235](https://github.com/VladimirMarko/conaled/issues/235):
minimize the retained annotation reproducer before proposing a new generic type
boundary, reduction lemma or upstream report. It does not block this consumer.
Automatic Cartesian inverse-witness construction remains separate; no concrete
consumer here requires it. The earlier interval-projection `PathData` solution
is unchanged. These results apply the completed #636 conclusions and do not
establish a general productivity advantage.
