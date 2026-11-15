# Shared affine recurrence bound: exact implementation scope

Frozen 2026-11-02 before implementation. This is the bounded cross-cutting
resource theorem identified in `../research/affine-recurrence-preflight.md`,
SHA-256 `dc20f947d2ff84ece47299a2403c9166d28f8c6103697e3b4b6b28842979b273`.
It supports the book's later divide-and-conquer cost arguments without
activating or accepting any later chapter. The user's full request and
conaled's existing architecture, example, build and review rules remain in force.

Starting shared candidate: `c28ba71863d2a35ee1c3a089caa90464e4cca692`.
Development branch: `work/fdsa-affine-recurrence` in its own worktree.
No compiler may run concurrently with the current frozen Chapter 1 full gate.
The separate shared foundations and repaired Chapter 1 candidates remain
unaccepted; this theorem cannot be integrated or accepted before those relevant
dependencies are validated and reconciled.

## Required ordinary theorem

For `f : Nat -> R`, child maps `left right : Nat -> Nat`, a natural cutoff
`n0`, and fixed `rho K C D : R`, derive a uniform all-input affine upper bound
from:

```text
rho < 1
forall n > n0, (left n : R) + right n <= rho*n + K
forall n > n0, f n <= f(left n) + f(right n) + C*n + D.
```

The conclusion is `exists A B, 0 <= A and forall n, f n <= A*n+B`.
The construction may additionally return `0 <= B`. The constants must precede
all natural inputs, including zero and the finite enlarged prefix. Do not
require nonnegativity or monotonicity of f, sign assumptions on C or D, or
monotonicity of the child maps. Do not assume the final cost bound as a premise.

Use an Archimedean linearly ordered commutative ring, with the actual unbundled
Mathlib classes at the pin. The division-free proof does not require a field,
topology, completeness, norms, measure theory or a floor operation. Separate
the finite-prefix/induction argument from witness selection when useful.
An internal quantitative induction lemma may take explicit valid constants;
export it only if a retained checked use needs that public interface.

Reuse ordinary functions, standard finite maxima, `Archimedean.arch` and
natural strong induction. Do not introduce a recurrence record, executor,
timing class, source translator, renamed ceiling/logarithm operation, or
parallel Akra–Bazzi framework. Preserve the existing small `Growth.lean`
interface; keep broad analysis imports out of the arithmetic core.

The proof must obtain smaller natural child arguments above an enlarged
cutoff from the sum bound and strict contraction. It is a theorem about an
already given total f, not a termination proof for an arbitrary proposed
algorithm or permission to repair a bad recursive definition by increasing
only the later proof cutoff.

## Connected cases and statement review

1. Retain a nontrivial explicitly defined natural scalar recurrence:
   `Q n = 1` for `n <= 1`, and otherwise
   `Q n = 2*Q(n/4) + n + 1`. Prove definition-level termination and its branch
   equations. Independent values are `Q 0=1`, `Q 1=1`, `Q 2=5`, `Q 4=7`,
   `Q 8=19`, `Q 16=31`. Apply the generic theorem to its rational cast with
   `rho=1/2`, `K=0`, `C=1`, `D=1`, discharging the actual child-size and
   recurrence premises. This is a scalar recurrence client; do not call it
   the book's selector or imply an absent algorithm-to-cost correspondence.
2. Include an integer specialization with a signed base/function or toll to
   demonstrate that the generic theorem does not secretly require a field or
   nonnegative f. Explain the independently expected inequality and connect
   the client through the generic theorem.
3. Preserve the distinction between a one-sided signed bound and a norm
   bound. The pointwise example `-(n:R)^2 <= 0` does not justify a Big-O norm
   conclusion. No signed-function Big-O theorem is required in this unit;
   any optional such theorem must retain adequate absolute-value hypotheses.
4. Preserve family quantifier order. A separately bounded family
   `f p n = p` does not imply one intercept independent of every natural p:
   at n=0 there is no common natural bound. Retain a checked boundary witness
   and do not advertise pointwise parameter application as a uniform bound.
5. State explicitly that exact source ceilings/negative offsets, the source's
   sharper possibly-negative-intercept constants (C03-041/042), the actual
   median-of-medians recurrence and its selector correspondence, generalized
   grouping, and the genuine noncontracting halving counterexample remain
   Chapter 3 obligations. The present generic proof does not erase them.

Review quantifier order, casts, satisfiable examples, full finite-prefix
coverage, strict contraction and operation/value/cost boundaries. Keep
all statements, proofs, provenance and cases in ordinary reusable modules.
Integrate retained cases through the existing public root. No admissions,
extra axioms, partial definitions, unsafe proofs or kernel bypasses are allowed.

## Validation and completion

Record source draft and semantic assessment honestly before compilation.
After resources become available, use the unchanged pinned environment for
focused builds. Capture and validate the full integrated immutable candidate
with the applicable guarded check and exhaustive audit. Both retained
independent review axes must cover this exact scope and the integrated source
before immediate final candidate verification and acceptance. No focused
build, source preflight or checkpoint constitutes chapter acceptance.
