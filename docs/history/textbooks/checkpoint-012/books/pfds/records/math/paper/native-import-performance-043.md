# Native import performance: checkpoint043 observations

The approved native profile executes the unchanged official Lean4.35.0 and
bundled Lake5.0.0 binaries. These measurements investigate remaining import
latency; they are not formal candidate validation or a module-system migration.

## Actual outcomes

| Run | Source and scheduling | Actual result |
| --- | --- | --- |
| `import-901-native-fresh-r1` | Stock fresh check on exact901, later overlapping bounded probes | Four module completion messages; Squares256.21s, AD.Core1028.20s, AD.Modes1421.71s, FirstOrder14.18s. Root intentionally interrupted the owned tool session. Tool130/full lock free; original wrapper did not finalize a compiler/audit result. |
| `native-module-header-probe-043` | Standalone new-format `module` file importing Lean; concurrent full | Exit0, 29.582s, no axioms, 8436 mapped regions/1605102040 artifact bytes, maxRSS422724KiB. |
| `native-modular-project-probe-r3-043` | Copies of exact901 Squares/AD.Core, with only module/public-import/exposed-public-section headers added; concurrent full | Squares exit0 in47.987s. AD.Core exceeded the180s investigative wall limit and its owned process group terminated with observed-15; no mathematical diagnostic. |
| `native-modular-project-probe-isolated-ad-043` | Same copied AD.Core using the genuinely compiled copied modular Squares; both task scheduling locks held | Exit0 in110.395s; 17373 mapped regions/3222825960 artifact bytes, 128106 major faults, maxRSS921100KiB. Original/probe sources, Squares outputs and native profile identities unchanged. |
| `native-legacy-project-probe-isolated-043` | New verbatim copies of exact901 Squares/AD.Core; both task scheduling locks held; native profile/dependency paths unchanged | Both exit0. Squares9.906s, 11870 regions/2009200824 bytes. AD.Core11.496s, 22156 regions/3543443032 bytes, 12129 major faults, maximum child RSS2991188KiB. Original/copy source and native identities unchanged. |

Complete commands, source copies or source identities, stdout/stderr, resource
observations and terminal outcomes are in the corresponding JSON files under
`session/validation/`. The last record's RSS is the process family's cumulative
maximum, not an isolated instantaneous AD measurement. It is not evidence of
any fixed cgroup cap. Byte totals describe mapped import artifacts, not resident
memory or bytes read from storage. All reported import regions were mapped.

The first bootstrap attempt timed out while asking `lake env` for LEAN_PATH;
it did not start the source compilation. A later driver incorrectly assumed
nine package repositories implied nine materialized build directories and
failed before invoking Lean. Both are preserved separately as setup failures.
The actual probes use the unchanged stock fresh check's enumeration of present
pinned dependency build directories. Nine clean pinned source repositories
remain distinct from the count of built output directories.

## Interpretation and next action

These observations do not establish a general speedup or a controlled causal
comparison. Scheduling, available memory and filesystem cache conditions varied.
The isolated legacy source succeeds quickly enough to justify retaining the
existing project format and trying the required native gates serially. No
migration was applied, no compiler/proof budget or stock timeout was increased,
and no project theorem statement or proof was changed by this investigation.

The new module format changes exported/private artifact loading and can reduce
one fixture's resident set, but it is not a drop-in header edit for this project:
a new-format module cannot directly import a legacy local module, and the stock
fresh checker currently recognizes plain `import` lines for dependency ordering.
Any future migration must preserve public declarations and exhaustive audit
coverage, update relevant infrastructure, and receive its own full review.
The present experiments do not approve such a migration.

Use a single active compiler validation workload in this constrained workspace
until evidence supports more concurrency. Native metadata/profile behavior
remains the already independently reviewed contract. The existing chapter2 and
prerequisite gates, all stock regression obligations, independent formal reviews
and immediate final verification remain required. The accepted frontier has not
advanced.
