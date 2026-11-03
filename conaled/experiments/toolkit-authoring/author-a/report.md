# Author A trial report

All four fixed contracts completed in the prescribed order. The accepted self-contained source is `Final.lean`, byte-identical to `Examples/ToolkitAuthorTrialA.lean`. The latter location permits the supported Lean `--root` invocation to include the current module in the existing audit. These files remain isolated experimental artifacts.

The trial began at 2026-10-29 23:12:13 UTC. Final accepted compilation and audit finished at 23:16:59.749161 UTC. Report completion time is recorded in `completion.txt`; the 15-minute cap was not reached. The date differs from the protocol's local date because these timestamps are UTC.

## Attempts and results

| Route | Preserved source | Result |
| --- | --- | --- |
| A direct | Attempt01.lean | Failed: two simplifications needed explicit `Batteries.DList.toList_empty`. |
| A direct | Attempt02.lean | Passed; native accumulator inductions prove decode and summary. |
| A shared | Attempt03.lean | Passed; uses `dlist_batch_decode` and `dlist_batch`. |
| B direct | Attempt04.lean | Passed; native reverse/append laws and accumulator inductions. |
| B shared | Attempt05.lean | Passed; local laws discharged, then shared validity and batch theorems. |
| Combined | Final.lean | Compiled; direct invocation's audit omitted this experiment module. |
| Audit probe | AuditProbe.lean | Checked Lean environment APIs; passed. |
| Superseded audit harness | FinalAudited.lean | Passed and included current declarations, but changes module identity inside source; not the accepted artifact. |
| Stdin audit | Final.lean, FinalStdin logs | Passed, but virtual filename did not include current module in audit. |
| Accepted audit | Examples/ToolkitAuthorTrialA.lean, FinalRoot logs | Passed with supported `--root`; current trial module explicitly audited. |

Every Lean invocation has a separate raw `.log` and `.json` with exact command, UTC start/finish, exit status, and source SHA-256. Sources were written before compilation and never overwritten afterward. Failed Attempt01 is evidence, not an accepted theorem file. `setup-failure.txt` records the initial shell failure from invoking Python outside direnv; its exact timestamp was not captured separately, which is an evidence limitation. Subsequent runners used direnv. No build command or library mutation was performed by this author.

The accepted command from the checkout root is:

```sh
direnv exec . lake env lean --root=experiments/toolkit-authoring/author-a experiments/toolkit-authoring/author-a/Examples/ToolkitAuthorTrialA.lean
```

`FinalRoot.log` reports `Examples.ToolkitAuthorTrialA: 38 logical declarations; 28 theorem declarations; 0 unsafe runtime declarations` and a passing transitive audit using only `propext`, `Classical.choice`, and `Quot.sound`. The final source imports `Applications.Sequences.OrderedSummary` and `ProofAudit`. Individual route files import only the former. The compiler is Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, recorded in `toolchain.txt`.

## Statement review and checked cases

The final declarations quantify independently over element and monoid universes. They require a `Monoid`, with no commutativity assumption. `measure : A → M` is unrestricted. The initial route attempts used `Type`; the combined source generalized this to `Type u` and `Type v` and passed compilation again.

For A, both routes construct exactly `xs.foldl Batteries.DList.push .empty`. The decode theorem returns the complete list `xs`, and the summary theorem returns the specified left fold with multiplication `m * measure a`, seeded by `1`. The direct route's accumulator lemmas quantify over arbitrary initial DLists and prove the stronger decoded suffix and initial-summary statements. Their induction uses native `List.foldl_cons`, DList push observation, list associativity, and primitive summary laws. It calls no shared batch/fusion theorem. The shared route directly specializes the two existing DList results.

For B, both routes use the same definitions: reverse decoding, cons push, reversed argument order for append, and a cache pair whose validity is exactly its second component equalling the ordered summary of the decoded first component. The empty cache is `([],1)` and cache append multiplies left cache by right cache. The empty and append validity statements require no plain-list invariant. The direct proof uses reversal of concatenation to establish the intended observation order. Its batch proofs are accumulator inductions independent of the shared interface.

The shared B route supplies `empty_law`, `push_law`, and `append_law`. Its only validity conversion is `valid_iff`, equating the local equality with `Valid (fun _ => True) decode measure`. Thus the invariant adds no restriction. Closure witnesses are `trivial`, and observation obligations are the proved local laws. Empty and append preservation use `empty_valid` and `append_valid`; batch results use `batch_decode` and `batch_summary`. There is no replacement summary-only history, strengthened input assumption, or recreation of the shared library.

Each route retains empty and nonempty batch applications. The nonempty ordered observation is the `FreeMonoid Bool` word `[true,false]`, derived through the route's summary theorem. A further case proves the reversed input produces a different word, so commutation would fail. Empty applications exercise the `1` seed. Equal-length lists `[true,false]` and `[false,true]` are proved unequal, showing that length does not determine full history. B additionally constructs an empty valid cache, derives nonempty append validity through its preservation theorem, and rejects the deliberately invalid cache with stored list `[false,true]` and cached word `[false,true]`: decoding actually gives `[true,false]`. These cases witness usable inputs and detect order loss.

The reviewed statements match the fixed mathematical contracts. They make no cost, storage, allocation, physical runtime, or new-setting claim. The results concern this monoid/list setting and do not establish a general abstraction or model-capability comparison.

## Exposure and assistance

`prompt.txt` retains the exact author dispatch; `protocol.md` retains the frozen protocol; `exposure.json` lists public source/document paths and hashes. Public API and example source were read before A direct. Later routes therefore had earlier-route exposure, as permitted by the counterbalanced protocol. No other author's files were read. No subagents or external model calls were used.

`help.txt` records the coordinator's environment-only cache and audit advice. There was no mathematical assistance. Cache preparation was coordinator-owned, including a stale unrelated compiled module repair. Exact serving model revision, reasoning configuration, token usage, and pricing are unknown. The model was inherited with no override. The audit troubleshooting adds environment effort to elapsed time; the attempt timestamps preserve that distinction.
