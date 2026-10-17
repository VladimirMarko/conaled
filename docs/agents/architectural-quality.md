# Architectural quality

Felix is the minimum standard for the library's elegance, expressive power,
and architecture. When designing or reviewing library abstractions, compare
the relevant Felix interfaces and constructions at the revision recorded in
`docs/SOURCES.md`. Check upstream definitions and proofs; distinguish completed
capabilities from unfinished work. Use idiomatic Lean and existing Mathlib
constructions where they meet the same requirements.

Evaluate designs by the generality of their assumptions, the size of the
interface callers must learn, and the definitions and proofs callers can
reuse. Keep operations, semantic equivalence, and laws distinct; require only
the structure each construction needs. Establish reusable structure-preserving
maps and law transport where applicable. Recover concrete implementations as
checked specializations of the shared abstractions, preserving their existing
theorems and semantic distinctions. A specialized application result alone
does not establish parity with Felix's general construction.

For architectural changes, state the corresponding Felix capability, the
remaining gaps, and the examples demonstrating reuse and composition. Treat
gaps as work to resolve, rather than lowering the quality standard. Historical
discussions in `docs/history/` supply motivation; verify their claims against
current code and primary sources.

## Scope of parity

Architectural parity is the first milestone. The longer-term goal includes
porting Felix's full body of work to Lean and completing its unfinished
constructions and proofs. Track that broader work in [issue #8], separately
from the initial architecture plan in [issue #1]. Upstream TODOs identify work
to investigate; they are not established mathematical claims or reasons to
discard stronger local results.

[issue #1]: https://github.com/VladimirMarko/conaled/issues/1
[issue #8]: https://github.com/VladimirMarko/conaled/issues/8
