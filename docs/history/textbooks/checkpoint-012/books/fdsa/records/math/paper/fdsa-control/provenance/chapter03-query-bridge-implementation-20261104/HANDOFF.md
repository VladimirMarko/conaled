# Root handoff and author hold — candidate01

Candidate `edd0132b491858feda3307da70817e157dcad151`; tree `54fd241a366cd77d73b2254ce6f29c5fae7c09ba`; parent `591ecdd855bc2fab3f788e6b134cc18aa80a3b6a`.

This is a local source commit only. The worktree is clean. Root owns the serial compiler; this author ran no Lean/Lake/build/install/hydrate/cache command. Static `git diff --cached --check` passed. No formal test or printed-type output is claimed. All four inherited files and all inherited provenance remain unchanged. No other author's commit/import, project gate, pin, toolchain, or aggregate entrypoint was changed.

## Focus targets

- Applications.Selection.CoordinateReadAll
- Examples.CoordinateReadAll
- Prepared exhaustive public inspection: Statements27-candidate01.lean (new 27), Statements95-candidate01.lean (inherited 68 + new 27).
- One new private helper: source-local Applications.Selection.CoordinateQueries.readPlan_run_from. Obtain its internal name from elaboration for the private audit. Existing two inherited private helpers stay in their old inventories.

## Mathematical scope

The finite readPlan operation requests coordinates only from fixed plan positions determined by transcript length, then applies fixed compute to chronological observed answers. The actual Runs witness is constructed by induction over the remaining plan. readAll specializes to finRange n, constructs an actual total run with exact result compute(ofFn input), and derives exact n queries and constant work c*n for every terminating empty-history run via determinism. Repeated planned coordinates remain separately charged. Inputs and values need not be distinct; n and c may be zero.

The examples include actual empty runs, arbitrary full runs, concrete [8,3,5], duplicate [4,4,4], and repeated-plan [0,1,0]. The supplied malformed-history example is solely an operation equation. The conditional generic correctness transfer is preparation only.

C03-083 is **not closed**. The actual measured median-of-medians selector, source-call observation relation, recurrence bound and tariff composition remain future authorized work. No Chapter 3 acceptance credit is requested. Full check/audit, explicit printed statements, independent Standards/Spec review and immediate verification remain root completion gates.

## Exact evidence

See candidate01.json for both new source SHA256/blob identities and slice/whole-query diff SHA256 values. Source snapshots, diff patches, initial/final index and status, commit receipt, exhaustive source headers, declaration inventory, independently expected cases and source statement assessment are preserved in this directory. These files are implementation evidence, not review decisions.

## Hold

All own source and provenance writes are held after this handoff so root can check this exact commit. Resume the same assignment when root explicitly reopens author work. No claim about actual kernel acceptance is made before that check.
