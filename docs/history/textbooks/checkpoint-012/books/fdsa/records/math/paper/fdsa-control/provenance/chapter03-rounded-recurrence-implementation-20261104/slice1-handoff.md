# Rounded recurrence: first immutable source slice

Prepared 4 November 2026. **Source only; uncompiled and unaccepted.** The fixed full assignment remains C03-039–044 in the unchanged 83-row Chapter3 inventory. This first handoff is deliberately bounded so the sole qualified root compiler can supply actual feedback before further implementation.

## Candidate and exact ownership

- Candidate: `a4cd1b6b53fdab38eab40433c3fd60293fdc054f`.
- Tree: `cdf8f8ffb0ea2a4afb1188b489491064a89c0a49`; sole parent: `c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5`.
- Branch: `work/fdsa-ch03-rounded-recurrence` in the existing `conaled-ch02-natural-runs` author checkout. Clean after the local Conventional Commit `feat(resources): prove rounded recurrence descent and sharp step (#174)`; command-local author identity ChatGPT <chatgpt@openai.com>.
- Exactly two new paths: `Applications/Resources/RoundedRecurrence.lean` (140 lines, 7,723 bytes) and `Examples/RoundedRecurrence.lean` (79 lines, 3,782 bytes). No other parent path changed.
- All other 72 refs were identical between the author's pre/post snapshots. Accepted `work/fdsa-book` remains Q `2da5708478a1d943a9214b5b386ec2db16cd9eca`; original `work/fdsa-affine-integration` remains c1ce. All five original XR source/documentary blobs are unchanged. This does not freeze unrelated authors' subsequent authorized work.
- `starting-state.json` and `allocation-result.json` are root-owned records and were retained byte-for-byte. Original XR preparation/correction evidence, programs, full attempts and global controls were not edited.

## Mathematical content and limits

The core uses Mathlib's `Nat.ceil` directly. There is no parallel rounding definition, recurrence structure, evaluator, or new instance. The first proof explicitly splits the nonpositive argument case, where the natural ceiling is zero, before applying the standard nonnegative-argument ceiling bound. Signed offsets are upper-bounded by `max 0 b` and `max 0 d`.

The two (3.16) thresholds imply exact natural child descent beyond their natural cutoff. The stronger combined (3.18) cutoff implies both earlier thresholds and gives the positive denominator `(1-a-c)*N-max 0 b-max 0 d-2`. These statements retain arbitrary signed offsets and use the actual coefficients a and c.

The slope result uses **C3 ≥ C1/(1-a-c)**. From C1 ≥ 0 and a+c<1 it derives both C3 ≥ 0 and a nonnegative induction slope. The absorption theorem retains the exact second numerator `C1*N+C2+C4` and denominator. C2 and C4 are arbitrary reals. No function positivity, offset positivity, C2 positivity or C4 positivity is imposed.

`recurrence_step_le` contains the exact real-valued rounded recurrence at one natural n and consumes bounds on both genuine child values. Its conclusion uses the same C3 and C4. It is a local induction step; it is not the completed all-input induction or an existence theorem. The hypotheses named `left_bound` and `right_bound` are explicit, not hidden claims that the recursion already terminates or that the children are arbitrary surrogate functions.

Eight connected examples retain: a negative ceiling argument and failure of the untruncated upper bound; individual and combined signed-offset descent; the actual zero recurrence; the printed maximum's zero-slope counterexample at a=c=1/4 and N=5; a public-law application at slope equality; the constant negative function with C4=-3; and simultaneous negative constant toll/intercept in the sharp algebra. The two numerical step examples apply the public recurrence theorem, while the negative-toll example applies the sharp absorption theorem. Their scalar observations make no claim about an implemented selector or its work.

## Exact first-slice declaration scope

There are **16 authored public theorems**: eight core, eight examples. There are no authored definitions, private declarations, instances or anonymous examples. These are source counts, not checked declarations, kernel-audit counts or completed coverage rows.

`slice1-statements-inventory.json` contains every fully qualified name, exact authored header, source line, Git blob and full-file digest. The raw header convention ends immediately before `:=`, retaining the preceding whitespace. Both complete files and every header/proof body were author-read after the final edit, before the commit; the full new-file diff is retained.

## Required continuation after actual feedback

1. Continue the same full C03-039–044 scope. Add the sharp strong-induction theorem using a real prefix bound C4 that may be negative, and choose the exact source witnesses: `N=max n0 (Nat.ceil(K/(1-a-c))+1)`, C4 the finite prefix maximum and C3 the maximum of the two source quotients, where `K=max 0 b+max 0 d+2`.
2. Prove the full all-real theorem with the recurrence above n0, fixed constants chosen before n, and every natural n including zero. Preserve all signed-parameter and nonnegative-C1 boundaries; no positivity restriction on f is permitted.
3. Derive the natural-valued corollary by casting the actual recurrence and rounding real constants upward. No second induction or weaker input range is substituted.
4. C03-045 and C03-046 remain required future consumers of actual scalar F and the measured selector; neither is implemented or claimed here.

The existing generic XR theorem is not imported by this first slice. Its availability on the ancestor branch does not replace the source's exact sharp constants, and its unaccepted full retry remains separately controlled by root.

## Prepared inspection and execution boundary

- Focused targets: `Applications.Resources.RoundedRecurrence` and `Examples.RoundedRecurrence`.
- `Statements16.lean` binds the exact candidate and checks all16 names with explicit `@`, retaining `autoImplicit=false` and `warningAsError=true`.
- Its supported pretty-printer options are `pp.universes`, `pp.explicit`, `pp.fullNames`, `pp.deepTerms`, `pp.proofs` all true, plus `pp.maxSteps=1000000`. There is no `pp.maxDepth` at the pinned Lean version. These settings alone do not prove output completeness; actual diagnostic/block inspection remains mandatory.
- No compiler, Lean/Lake, probe, cache/hydration, output capture, runtime/pin/profile, installation or GitHub action was performed by the author. No type output or validation credit exists for this slice. Root owns later serial execution through the qualified unchanged native profile, followed by the applicable full-scope reviews and all mandatory acceptance gates.

## Source and instruction read boundary

All510 lines of the frozen 83-row inventory, all559 lines of the Selection proof plan and the complete observed73-line C3 ticket were read. Actual book §3.5 was read from preserved text lines1837–2035, with full visual inspection of printed pp.42–43; its PDF full-byte identity was reverified. The earlier full affine preflight assessment was retained, with a bounded current reread of exact recurrence/constant-selection passages. No fresh full-book or entire Mathlib source review is claimed.

Current AGENTS, implementation/example-driven instructions, architectural-quality guidance and proof-dependency ADR were read. Pinned APIs were inspected for natural ceiling, zero truncation, real FloorRing construction and positive-denominator quotient inequalities. The deprecated Real.Archimedean forwarding module was avoided. The complete read boundaries and nineteen exact source/control/API input identities are in `slice1-input-bindings.json`. This is author statement/proof development, not either independent final review axis.

## Saved evidence and hold

`slice1-source-baseline.json` and `slice1-git-commands.json` preserve actual source-state guards and every Git mutation/result. `slice1-candidate.json`, `slice1-source.diff` and `slice1-preservation.json` bind the immutable two-file result and preserved source/refs. `slice1-requirements.json` retains all six assigned obligations, their first-slice witnesses and explicit remaining work. The inventory/program and author readback receipt complete this handoff. All source is **HELD** for root feedback; after the receipt is final, this package is also **HELD**.
