# Architectural quality

When designing compiler frontends, internal proof interfaces, or interpretation
and transport facilities, read the [shared language direction](../language-direction.md).
Evaluate author effort and reuse across mathematical settings, including the
requirements an argument exposes; improved concrete notation alone does not
fulfill that direction.

Start with the current local interfaces, proofs, and checked applications.
For capabilities ported or extended from Felix, consult
`docs/research/felix-parity-implementation.md` and verify the relevant code.
Reuse those constructions and idiomatic Mathlib interfaces where their
hypotheses fit the task.

Felix remains the minimum standard for elegance, expressive power, and
architecture. Consult its definitions and proofs at the revision recorded in
`docs/SOURCES.md` when investigating missing capabilities, revisiting an
architectural decision, checking provenance, or performing an explicitly
requested upstream comparison. Assess any upstream TODO against the local
implementation before treating it as remaining work.

Evaluate designs by the generality of their assumptions, the size of the
interface callers must learn, and the definitions and proofs callers can
reuse. Keep operations, semantic equivalence, and laws distinct; require only
the structure each construction needs. Establish reusable structure-preserving
maps and law transport where applicable. Recover concrete implementations as
checked specializations of the shared abstractions, preserving their existing
theorems and semantic distinctions. A specialized application result alone
does not establish parity with Felix's general construction.

For architectural changes, state what changes relative to the local
implementation, the remaining gaps, and examples demonstrating reuse and
composition. When an upstream comparison is needed, distinguish inherited
capabilities, local extensions, and unresolved gaps. Treat gaps as work to
resolve, rather than lowering the quality standard. Keep routine application
documentation focused on the local APIs it uses; link the implementation
record for provenance. Historical discussions in `docs/history/` supply
motivation; verify their claims against current code and primary sources.

## Scope of parity

Architectural parity is the first milestone. The longer-term goal includes
porting Felix's full body of work to Lean and completing its unfinished
constructions and proofs. Track that broader work in [issue #8], separately
from the initial architecture plan in [issue #1]. Upstream TODOs identify work
to investigate; they are not established mathematical claims or reasons to
discard stronger local results.

[issue #1]: https://github.com/VladimirMarko/conaled/issues/1
[issue #8]: https://github.com/VladimirMarko/conaled/issues/8
