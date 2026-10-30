# Finite byte-buffer adapter (#253)

The [implementation record](../../docs/research/finite-byte-buffer.md) defines
the model, adapter assumptions, statement review and measurement interpretation.
The existing #250 experiment is preserved unchanged and supplies workload and
unit-model functions; it is not the implementation being timed here.

From the repository root:

```sh
direnv exec . python3 experiments/finite-byte-buffer/test.py
direnv exec . python3 experiments/finite-byte-buffer/experiment.py /tmp/finite-buffer-new.jsonl
direnv exec . python3 experiments/finite-byte-buffer/experiment.py /tmp/finite-buffer-allocation-new.jsonl --fault allocation
direnv exec . python3 experiments/finite-byte-buffer/experiment.py /tmp/finite-buffer-output-new.jsonl --fault output
direnv exec . python3 experiments/finite-byte-buffer/experiment.py /tmp/finite-buffer-incomplete-new.jsonl --incomplete
```

Use fresh paths. The normal run exits zero with `complete.success: true`.
Allocation/output injections exit one with failed service outcomes and
`complete.success: false`. The controlled incomplete run exits two without a
completion marker. They are retained negative evidence, not successful runs.
Output-file or process failures can themselves prevent a final record. Flushing
lines does not provide durable publication or supervision.

The checked-in JSONL files retain raw command lists, source/toolchain identities,
paired timings and individual outcomes. Timing consumes every reply, but exact
output equality is checked separately by `test.py`. No Lean/compiler proof
connects this Python code to the modeled machine. Formal claims are integrated
under `Applications` and `Examples`, so they use the normal build and proof audit;
this directory's executable checks require the commands above.
