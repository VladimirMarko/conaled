# Clarification of IU-4 numerical comparison

The phrase “one unsplit command execution” in the frozen initial report should be narrowed. I intended one uninterrupted execution of the **same ordered numerical tick list**, not replacement of a subdivided command by a single larger numerical step. The original wording permits the latter reading and is misleading.

The precise existing equality is `Numerical.run_append` in `Applications/Orbifold/NumericalExecution.lean`. For fixed lists `cs`, `ds` and incoming packet `q`, if

```text
run cs q = some a
run ds a.final = some b
```

then

```text
run (cs ++ ds) q =
  some ⟨b.final, a.samples ++ b.samples, a.elapsed + b.elapsed⟩.
```

This compares chunking of an unchanged sequence of controls and durations. Equality of the final packet includes equality of its numerical state and stored error. `run_error` identifies that error with `errorAfter (cs ++ ds) q.error`; `run_clock` identifies elapsed time with the clock of that same list. The append equality needs no approximation premise. Relating the numerical result to an exact trajectory additionally uses the incoming `Approx` premise of `run_correct`.

For the proposed bridge test, freeze the actual accepted subdivision schedules, concatenate their ticks, and compare successful committed advancement with that fixed-list reference. Insert repeated endpoint observations and a failed trial between committed chunks. A read-only observation must leave the committed packet and clock unchanged. A failed trial must not become a committed chunk. Its resource charge and diagnostic log may change and are deliberately excluded from the equality. If a failure changes later schedule selection, compare the resulting accepted tick list against its own fixed-list reference; do not assert numerical equality with a run that selected a different partition.

This does not assert that `Numerical.run` itself retains a committed prefix on failure. Its definition returns `none` if any tick fails. Prefix retention is the separate behavior of `Driver.drive` in `Applications/Orbifold/Driver/Execution.lean`; `drive_partition` describes its committed events and pending suffix. The proposed test compares successful accepted chunks while separately checking the adapter's failure-state behavior.

For different partitions of the same constant-control command, `Driver.schedule_execute` in `Applications/Orbifold/Driver/Schedule.lean` identifies the **exact** decoded endpoint with `c.decode.finish p`, and `schedule_clock` identifies duration. `Driver.selected_sound` in `Applications/Orbifold/Driver/Interval.lean` gives each accepted numerical result an approximation contract to that exact endpoint. These results do not equate numerical endpoints or stored errors across partitions. `CheckedMotion.budget` in `Applications/Orbifold/CheckedMotion.lean` explicitly depends on step duration, and `Numerical.errorAfter` iterates it over the chosen ticks.

Suggested replacement for IU-4's test sentence:

> Compare successful committed advancement with an uninterrupted execution of the identical accepted tick list, using `run_append`; check separately that repeated reads and failed trials leave committed packet and time unchanged. When subdivision choices differ, require the respective approximation and clock contracts, without asserting equality of numerical states or error bounds.

This clarification changes no recommendation about testing the query/commit boundary. It corrects the proposed comparison's precision. Evidence remains source inspection and paper reasoning; I ran no Lean check or numerical experiment. The initial report is unchanged, and I have not read peer reports.
