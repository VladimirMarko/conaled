# Local #10014 suspension extension — version 1

Source: REQUEST.md and REQUEST-union-v2.md. This is the user's authorized
cross-cutting exception to chapter order, supporting book Exercise3.4(d),
Chapter4 and later lazy algorithms. It does not accept those chapters.

Fixed implementation/review base:
69f6f00de204617fdd7feefd5b9ee5b80fc0d9f4. This includes the pending complete
Chapter2 candidate and import prerequisite; their acceptance remains separate.
Implementation branch pfds/suspensions, worktree suspension-foundation.
At initialization the worktree is clean, with no unrelated user changes.

## Sources and scope

Exact identities: research/union-source-identities.json. Full source inspection
and statement distinctions: research/suspension-foundation-inventory.md.
Cover the union of the suspension mechanism in bookChapter4, thesisChapter2,
and every modification in thesisAppendixA pp131–135. Stream algorithms and
their exercises retain their Chapter4 owner; this foundation supplies their
evaluation, observation and resource contracts. Bookp38 and thesisp136 have
no additional mathematical content, as visually verified.

AppendixA extends the 1990 Standard ML Definition; the book cites the revised
1997 edition. State the inherited core-language fragment explicitly. A typed
core realization and checked rule correspondence may supply it; do not claim
a complete Standard ML elaborator/compiler or silently substitute another
edition's rules. Consult the primary base Definition when inherited details
are needed and preserve exact locators. No source manuscripts in deliverables.

## Required contracts

1. Syntax/static extension: reserved dollar expression/pattern productions,
   precedence and unary suspension type, excluded suspension equality,
   non-expansiveness, polymorphic derived force, and the restricted recursive
   suspension-binding form. Book-only lazy-function sugar must be hygienic,
   preserve its stated typing and delay ordered matching under strict application.
2. Finite mutable memory with values and expression/environment thunks, shared
   address space for references/suspensions, and retained exception-name state.
   Creation chooses a fresh address, captures lexical environment, evaluates no
   body, and relates deterministic allocation to the source fresh-choice rule.
3. Separate state-carrying normal, raised, failed-pattern, stuck and unknown
   observations. Fuel exhaustion is not a source failure or divergence proof.
   Cache hit skips body execution but performs the requested inner match.
4. An unevaluated body uses its captured environment. On normal return its
   result is installed BEFORE matching with the current match environment.
   Failed/exceptional matching retains earlier effects and memoization.
   Exceptional body propagation adds no successful write at that frame, while
   permitting updates already caused by inner/reentrant evaluations.
5. Ordered alternatives and reference patterns thread the state after failed
   matches. Cover the appendix's three-clause non-exhaustiveness and reachable
   fourth-clause examples using actual evaluation, not assumed postconditions.
6. Recursive function/suspension binding: implement the stated core Rec and
   SRec behavior, preserving memory domain, exception names and cells outside
   the bound address range while extending relevant unforced thunk environments.
   Cycles and reentrant forcing are supported. No implicit blackhole or global
   at-most-once law; retain the two discriminating recursive overwrite/outer
   exception cases from the source inventory.
7. Independent source-rule semantics and a source-specific execution machine,
   connected by finite-evaluation correspondence. Reuse Progress.Machine,
   Evaluates/search, Resources.Measured/workload and relational observations.
   Expose local demand steps instead of hiding an entire arbitrary body inside
   a claimed constant-time machine transition. Keep operations and laws separate.
8. Derived force and book lazy sugar have explicit value/effect observations.
   Force-after-delay does not imply literal whole-memory equality or equal
   resource traces. State fresh-name/private-garbage treatment and prove the
   correspondence required by the client domain. Stronger pure/nonreentrant
   cache/resource laws require proved client restrictions.
9. Connected public clients include lexical capture, nested and aliased versus
   repeated creation, ordinary cache reuse, failed/exceptional inner patterns,
   repeated body exceptions, SRec footprint, reentrant writes, and shallow
   constructor/root observation. Subsequent chapter algorithms supply further
   concrete specializations without weakening these distinctions.

## Architecture, validation and delivery

Follow AGENTS.md, architectural-quality, domain/ADRs and language-direction.
Reuse Durability.Heap/put where appropriate; its Extends law applies to fresh
allocation, not thunk replacement or SRec. Never impose immutable backward-DAG
invariants on recursive suspension environments. Add only the missing source
domain semantics, not a competing generic execution/resource framework.

Use example-driven-development and retain statement reviews/independently
expected conclusions. All additions enter the public closure and exhaustive
proof audit. No admissions/new axioms/native shortcuts or disabled linters.
Focused checks are development evidence. Exact isolated candidate validation,
matching record, final verification and independent Standards plus Spec review
on the same complete candidate are required for acceptance. Keep one finding
record across corrections. No GitHub writes. Local requirements, tickets, refs,
proofs and evidence are included in promptly uploaded recovery checkpoints.
