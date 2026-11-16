# Prepared Künneth author trial

This protocol is the handoff from #570 to
[#235](https://github.com/VladimirMarko/conaled/issues/235) and
[#117](https://github.com/VladimirMarko/conaled/issues/117). It prepares a later
independent trial. No authors have been assigned, no attempts have occurred,
and no productivity result is available.

## Freeze and assignment

Use the implementation candidate containing this protocol and the source hashes
in [kunneth-trial-inputs.json](kunneth-trial-inputs.json). The manifest identifies
the interface, models, calibration examples, Lean toolchain and Mathlib revision.
Before execution, the coordinator must resolve and record that candidate's exact
commit, verify these hashes, and freeze the task packet and allowed imports.
Any interface repair creates a new trial cohort; keep earlier attempts intact.

Assign fresh authors who did not implement or review this interface. Use matched
native and shared tasks with the same mathematical contract. The native packet
allows Mathlib and the existing adjoint-square/mixed-base-change interfaces;
the shared packet additionally exposes the Künneth modules. Both receive the
same model constructors, coefficient data and expected observations. Keep model
construction effort separate from routine proof authoring. Do not require the
native author to rebuild the entire model as part of an application comparison.

Before dispatch, record the author model and version, reasoning configuration,
resource budget, tools, source commit, toolchain, allowed references and exact
task text. Mark unavailable metadata explicitly. Preserve every submitted file,
compiler output, assistance message and repair. Record elapsed time and available
token/tool usage separately from compilation time. An empty attempt list below
means no execution, not successful completion.

## Matched tasks

1. **Construction.** For an arbitrary ordinary square, construct (K) from the
   two canonical PF components and BC, prove (E), and derive invertibility from
   exactly those components. The native and shared statements must have the same
   categorical observations and universe scope.
2. **Application.** Use the two-color predicate model with a noninjective
   surjection and coefficient families supplied in the packet. Derive the
   independently specified output predicate through the proper Künneth theorem.
   Include a coefficient family varying inside a fiber.
3. **Transport.** Duplicate one color into two. Identify the canonical target
   map with the conjugated source map using the specified endpoint comparisons,
   and transport its inverse. Separate instantiation of the target theorem from
   preservation of the source map.
4. **Diagnosis.** Present the empty-to-singleton base map with false external
   coefficient. Identify the failed PF/admissibility obligation, prove that an
   inverse is impossible, and state the additional hypothesis used by the
   positive model. A failed instance search alone is not the expected answer.

## Held-out packet

The held-out task uses base `Fin 3`, source space `Fin 3 × Bool`, source colors
`Bool`, and target colors `Fin 3`. Both base maps are the first projection.
For a source-space point `(s,b)` and color `i`, use

```
A((s,b),i) := s = 0 ∨ b = true ∨ i = false
B((s,b),i) := s = 1 ∨ b = false ∨ i = true
r(j) := (j = 0)                 -- Boolean-valued decision
 t(i) := if i then 0 else 2     -- Bool → Fin 3
```

The independently calculated source output is
`(i = false ∧ s = 1) ∨ (i = true ∧ s = 0)`.
After `r`, the output is `if j = 0 then s = 0 else s = 1`;
after the further color change `t`, it is `if i then s = 0 else s = 1`.
The author must apply the proper Künneth theorem, prove transport of the chosen
map and inverse through both changes, and identify the result with transport
along `r ∘ t`. The output predicates alone do not discharge map transport.

The preparation checked the finite source truth table independently of Künneth.
The generic route accepts arbitrary color maps; the two applications of
`indexed_transport` and the component composition law supply a feasibility
route. No author solution or timed attempt has been produced. The coordinator
must keep this section and its expected observations out of the calibration
packet until assigning the held-out task, then freeze the exact dispatch packet
and hashes. This is release preparation, not permission to alter its mathematics
or interface during the trial.

## Assistance and acceptance records

Default assistance is limited to the frozen packet, allowed source and ordinary
compiler diagnostics. Authors may ask clarification questions; record exact
questions and answers. If a missing interface lemma requires intervention, retain
the failed attempt, distinguish clarification from mathematical help, and either
finish the repaired cohort with that assistance recorded or start a fresh cohort.
Do not silently replace a failed attempt with its repaired submission.

For each task retain the submitted source, exact command, exit status, actual
elaborated statement, proof dependencies and whether the public shared result
was consumed. Use independent mathematical/spec review of the conclusions,
not only successful elaboration. Report completion, assistance and repair costs
without inferring a general productivity ranking from a small cohort.

Current execution record: no assigned authors, no attempts, no assistance to
trial authors, no trial repairs, and no outcomes. Implementation development and
its compiler failures belong to the implementation record, not author attempts.
