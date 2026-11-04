# Prospective comparison of requirement discovery (#293)

This protocol precedes author dispatch. The inspected repository base is
`2525b12052e4c85c57f9050dbf18f7a36ba2ef19`; preparation incorporates accepted
#291/#294 work at `d8563a8420196fedff7c875c158d0eeca3403db2`. The freeze manifest
records exact task and support bytes. A later report will record observations;
preparation success is not an author outcome.

## Question and fixed allocation

Can independent authors discover and publish sufficient reusable requirements
from a completed concrete Lean proof, justify two interpretations, remove a
used but dispensable detour explicitly, and retain selected witness data?
Does an explicitly prepared dependency ledger help in this bounded task?

One fresh author uses route M (manual); one uses route D (dependency-assisted).
Both receive E then W, one attempt stream per route, with 20 minutes each from
recorded start. No author crosses routes or sees the other's work. The assigned
order is fixed rather than randomized. Shared order and independent authors
remove same-task crossover exposure, but author differences and tiny sample
size prevent a causal comparison. W follows E within each arm and is not an
independent first-exposure observation.

The exact mathematical contract is in [tasks.md](tasks.md). E is a held-out
reversal argument, absent from #286's published E/W solutions. W adapts that
paper's right-unit selected-witness construction with an observation that is
noninjective for lists. Report W as calibration-derived. Neither task addresses
recursive proof import, variable changes of logic, or #108's theorem selection.

## Public and private boundary

Each handoff contains only the support source, task and conduct text, its route
prompt, frozen skill/architecture guidance copies, the immutable-check wrapper,
pinned environment/Lake configuration and
copied dependency sources/caches. Route D alone includes the
[dependency ledger](dependency-ledger.md). No original Git history, private solution,
entrypoint, project build cache, preparation record or other trial files enter
either handoff. Dependency caches are separate copies, never writable links.
Each handoff has a fresh independent Git repository containing only its allowed
inputs, needed for Nix flake evaluation; its public HEAD is recorded. No remote,
alternates or objects from the original repository are copied. This is an
allowlisted experimental access contract, not an OS security sandbox.

`Examples/ProofRequirementSupport.lean` imports only a Mathlib List module and
contains concrete proofs and operations. It exposes no generic law interface.
The coordinator's `Examples/ProofRequirementReference.lean` contains private
reference proofs and controls. Its repository entrypoint import makes it part
of the eventual integrated build/audit, but that entrypoint is excluded from
both handoffs. The references become public evidence only after attempts close.

Allowed sources, immutable logs, distinct namespaces, exposed metadata and
intervention rules are fixed in [conduct.md](conduct.md). The coordinator
dispatches the exact route prompts after checking this boundary. Authors receive
no conversation history and must report actual prior exposure. There are no
paid model calls or author subagents. Full agent-session export was unavailable
at preparation; exact shell records and authored transcripts are retained.

## Assessment fixed before observation

For each author and task, record pass, partial, fail or unavailable with file and
diagnostic references. Do not replace failed attempts with repaired successes.
Successful proofs undergo Lean replay, statement review and exhaustive axiom
audit under the frozen contract. Accept alternative sufficient interfaces, not
just the coordinator's spelling or smallest known assumption set.

| Dimension | Evidence required |
|---|---|
| Publication | A named, reusable requirement interface with a generic result; its fields do not assume the requested client conclusion |
| Interpretations | Both supplied targets prove the interface obligations and derive the required results through the generic artifact |
| Proof dependency account | Distinguish zero use of ambient append-empty evidence from actual use of double reversal; retain original-dependency replay and identify/check any changed proof |
| Equality | Full Lean equality at the stated type, block order and all quantified inputs; empty/nonempty cases connect to the public theorem |
| Selected data | W returns a subtype with first projection exactly the input and recovers the concrete source as data |
| Rejection | Failed reversal target, inhabited but wrong-selection Nat target, and equal erased proofs with unequal list projections are checked |
| Cost and exposure | Read sources, commands, diagnostics, wrappers, obligations, assistance, start/end, attempts and unavailable metadata are reported separately from setup |

Full right-unit requirements for W are acceptable sufficient requirements.
Observation-only right-unit is a stronger generality result, not mandatory for
success. Likewise an author may retain involution in the original E replay, but
must identify it as dispensable and check a changed proof that removes it.
Associativity is neither demanded by the contract nor used by the private
simplified proof. An overstrong interface is recorded without inventing a
failure if both supplied target interpretations and other requirements pass.

Distinguish mathematical, interface, documentation, host-encoding and author
causes. A timeout or malformed Lean term is not evidence that the mathematical
route fails. Preparation includes hand-chosen cut points and private generalized
solutions; their effort cannot be counted as author savings or extractor work.

## Decision and continuation rules

Retain dependency assistance as an opt-in aid if its delivered ledger supports
correct reuse without concealing witness/logic obligations. Revise the format if
authors misread source dependencies as necessary laws or copy an overstrong
boundary without checking proof changes. Drop this ledger format for the tested
fragment if it adds obligations or errors without a demonstrated use. Record
mixed/incomplete results instead of forcing a ranking.

No outcome licenses claims of human usability, general model capability, causal
time savings, tool productivity, a universal importer or a globally weakest
theory. A substantial prerequisite earns a scoped issue under #290/#235 rather
than expansion inside the trial. Later interface changes require affected-task
reruns and a fresh held-out task while preserving this baseline. Research and
other architecture work may continue against their own pinned inputs.
