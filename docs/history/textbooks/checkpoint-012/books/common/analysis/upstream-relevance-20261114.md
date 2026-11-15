# Upstream incorporation — 14 November 2026

The user authorized updating the upstream pin from
`9175737c2b14ef738cfb6c2cdc68d885c0805ddd` to the observed latest master,
`983d0b6b602b71541f182737011621a8805be27b`. The original full-spec integration
review base remains `9175737c`; all previous integration changes and findings
remain in scope. The live lookup is recorded in `../evidence/master-pin-20261114.json`.

## Exact change

Two commits were added: `5a138818b9192d876fabe06605094847c6097549` proves
arbitrary-bound uniform sampling; `983d0b6b602b71541f182737011621a8805be27b`
realizes rational kernels and Metropolis–Hastings execution. The delta changes
15 files, with 2,382 inserted and 31 deleted lines. It changes no agent
instructions, implementation/review skills, checker, Lean/Lake/Nix pins or
dependency manifest. The checked blob identities are recorded in
`../evidence/upstream-merge-20261114.json`.

The incorporation commit is `6a4fb245642e31dea42e3bc56c413000caa3ce45`, with
parents C2 `f52a47b9` and the new upstream pin. Git merged it without conflicts.
Every changed upstream blob except the shared public entrypoint equals the
upstream blob exactly; the entrypoint retains both parents' public imports.
These are source-identity checks, not a build or mathematical acceptance.

## Relevance to the textbook work

| New owner | Capability and relevance |
|---|---|
| `Probability.BoundedUniform` / `BoundedUniformLaw` | A bit-reading rejection machine samples below an arbitrary positive bound. The laws retain returned cursors, actual transition counts, uniform output mass, almost-sure termination and a fresh suffix at the random returned cursor. This is a concrete operational foundation for future links to finite-choice and randomized textbook algorithms. |
| `Probability.RationalRow` / `TableSampler` | Explicit finite enumerations and natural multiplicities realize rational stochastic rows and their existing kernel semantics. These may support source-to-executor bridges for finite randomized models. The probability table describes a distribution; `Search.OrderedMap` describes partial lookup, so the two owners serve different concerns. |
| `TableSamplerComposition` / `TableSamplerIteration` | Sequential executions consume the returned cursor and retain intermediate results/work; their probability laws connect actual runs to composed/iterated kernels. A retained reused-cursor boundary distinguishes accidental correlated reuse from the required fresh draws. |
| `Probability.SamplerWork` | Explicit tariffs price bit reads, arithmetic, lookup, storage, preparation and interpretation. A future comparison with textbook comparison counts or amortized charges needs a proved observation/model relationship. Its theorem statements do not supply machine-time or arithmetic bit-complexity bounds. |
| `Progress.Sequential` | Operational inversion, return interpretation and family laws extend the existing machine owner. They are reusable when a textbook algorithm's actual executor is expressed in that model. |
| `Probability.FiniteMHSampler` | The existing finite Metropolis–Hastings kernel is connected to actual finite tape executions and stationary laws. Stationarity does not establish a mixing-rate result. |

These relevance judgments follow from the inspected definitions, public statements
and module scope notes. They identify available capabilities, not completed new
book correspondence. In particular, the retained FDSA permutation-expectation,
joint-order and placement donors still require their single-permutation and
independence hypotheses to be related to any operational sampler before credit
is transferred. No chapter or exercise is closed merely by receiving this delta.

The current map recovery can proceed through the unchanged `OrderedMap` owners.
The upstream delta changes none of the existing sorting, stack, potential or
partial-map source owners. Its only overlapping changed path with the C2
integration is the public import entrypoint.

## Validation consequence

The interrupted predecessor build has no terminal result or success receipt.
Its observed 630 completed cold targets out of 3,278 requested targets are
progress evidence only. The new incorporated/recovered candidate requires its
own full guarded check, exhaustive audit, independent final reviews and immediate
identity verification. Existing matching outputs may be reused only through the
unchanged guard; no cache deletion, pin substitution or acceptance waiver is
needed for this source incorporation.
