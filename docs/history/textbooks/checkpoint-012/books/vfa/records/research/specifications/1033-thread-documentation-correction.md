# #1033 documentation correction: distinguish concurrency controls

This is a narrow follow-up inside the existing native-environment review loop.
The accepted operational source candidate is
`e41336d46dffd7bddd42b242a7ea7484a6055e43`. The formal candidate remains
`c988f183887896c00b09aaff9077a6ea7fb8d68f` and its fresh4 run remains active.

Pinned-source inspection found that the native guide's phrase "one Lean thread"
was too strong. `LEAN_NUM_THREADS=1` controls the compiled Lake executable's
runtime worker pool. The CLI compiler instead initializes its internal task
manager from ShellOptions, whose default is hardware concurrency and whose
explicit override is `-j`/`--threads`. The current launcher passes no such flag.

The correction must:

1. Distinguish fresh-checker process jobs, Lake's ordinary compiler-job pool,
   and each Lean CLI process's internal workers.
2. State the scope of the source-supported Lake serialization conclusion; do
   not claim a global single OS thread or control of arbitrary custom targets.
3. Give the supported explicit Lean selector and the correct place for any
   intended Lake environment override, without claiming the frozen launcher
   already supplies the Lean flag.
4. Preserve every runtime/helper/compiler/source/cache input and all historical
   raw evidence. Existing commands remain evidence of their actual invocation;
   do not retroactively assign a different worker count or measured outcome.
5. State the exact scope of the bounded explicit-j1 FirstOrder probe: one checked
   invocation, matching output bytes, uncontrolled conditions, no causal
   performance claim and no full-candidate or chapter acceptance credit.
6. Pass independent Standards and Spec review on the exact documentation-only
   operational candidate, with reuse of unchanged runtime validation explicit.

Evidence: `validation/1033-native-environment/concurrency-and-mmap-assessment.md`
and `explicit-j1-firstorder-probe.json` in the same directory. No new compile is
required to validate a prose-only correction to already-inspected source facts.
The user's environment exception, local tracking, full formal gates and
checkpoint requirements continue unchanged.
