# Lean-native verification source handling

`./check.sh` retains guarded incremental compilation and an exhaustive audit on
every invocation. `./check.sh --fresh` recompiles every inventoried project
module into private temporary outputs before auditing them. Candidate receipts
and `--verify-candidate` retain their exact commit/dependency/compiler checks.
The toolchain, proof-audit implementation and permitted axioms are unchanged.

## Source interpretation

`scripts/lean-source-info.lean` uses the pinned Lean `Parser.parseHeader` and
`Elab.HeaderSyntax.imports`. Thus multiline, escaped, public and meta imports
have the compiler's meaning. Python receives the import names as JSON and uses
them for coverage and dependency ordering. The explicit inventory remains root
Lean files and the `SquareKit`, `Applications` and `Examples` trees; `ProofAudit`
is compiled last and is excluded from the required mathematical entrypoint
closure. Executable helpers under `scripts` are verification infrastructure.

The source policy uses Lean's native token, field-index, literal, whitespace and
comment parsers. It rejects the existing admission/axiom/unsafe/partial/native
proof/skipped-kernel-check constructs, while comments and literals remain data.
It does not implement another character escape or nested-comment grammar.
Unknown notation characters are registered as opaque tokens. A failed isolated
token can fall back to Lean's field-index parser or a single opaque character;
this matters for projections such as `.1.val` and imported notation such as
`⁻¹'`. No characters are discarded on this fallback. The compiler still checks
whether the complete source is syntactically valid.

A native command-parser check inspects initial module documentation and rejects
a following import before any project compilation starts. It stops at other
commands: arbitrary later commands can depend on syntax extensions whose local
imports have not yet been built. This is a targeted early diagnostic, not a
claim to parse an entire extensible Lean file without its environment.

This helper imports only Lean and does not elaborate project code or consume
cached project modules. Full compilation and exhaustive axiom auditing remain
separate checks. The lexical guard is deliberately conservative about prohibited
names in executable tokens; it is not a semantic proof that arbitrary metaprograms
cannot manufacture forbidden constructs. The audit continues to reject actual
forbidden dependencies and user-written unsafe declarations with source ranges.

## Build ownership

Lake supplies the configured dependency search path. Fresh mode removes the
standard project output directory from that path and substitutes its new private
directory. Unsupported nonstandard project layouts are rejected by the existing
layout validator. Dependency caches are reused; stale project outputs are not.
Caller `LEAN_PATH` is discarded. Compiler-version checks precede preflight;
the existing pinned-version `LEAN` override remains available only in fresh mode.

Python remains for process orchestration, bounded fresh scheduling, the guarded
incremental adapter and atomic candidate receipts. Porting these already-tested
external-state operations would add migration work unrelated to removing the
duplicate Lean grammar. No Python source/comment/import parser remains.

## Regression evidence

The public `scripts/test-check.py` fixtures cover fresh and incremental modes,
coverage failures, stale outputs, unchanged-module recompilation markers, audit
ordering, compiler pinning, candidate receipt binding and failure propagation.
The import-after-documentation regression first reproduced project elaboration
before the late failure; the new preflight rejects it before that marker is
written. Native syntax cases include multiline module imports, nested comments,
raw strings containing prohibited words, character literals, custom notation
and numeric field projections. Every prohibited source-policy construct has a
public rejection case. The existing public audit fixtures cover unused external
axioms, private transitive dependencies, private admissions and source unsafe
code; the independent root-enumeration suite remains unchanged.

Final real-repository incremental/fresh validation and exact candidate receipts
are recorded in the implementation handoff, alongside independent reviews.
Fixture success alone is not full-repository acceptance.
