# Rounded recurrence: full-bound continuation design

Scope remains C03-039–044 in the frozen 83-obligation Chapter 3 inventory.
This is an additive continuation of the original implementation/review loop.
Baseline is a4cd1b6b53fdab38eab40433c3fd60293fdc054f. Root reported the exact
two-module slice1 focused pass, owned 52277 / terminal 3e669a / closure 67190b;
that result is focused elaboration only. The author runs no compiler.

## Intended claims before implementation

1. For every real ratio, taking its natural ceiling plus one gives a strict
   real upper bound. Applying this to K/(1-a-c), where
   K=max 0 b+max 0 d+2, produces the exact source cutoff
   N=max n0 (Nat.ceil(K/(1-a-c))+1).
2. The original sharp one-step bound becomes an all-input strong induction.
   Keep n0<=N, the exact combined strict cutoff and both non-strict slope
   constraints, and a genuine bound f n<=C4 on the finite prefix n<=N.
   No sign condition on f, b, d, C2 or C4 is added. The positive denominator
   and nonnegative slope are derived through the original public lemmas.
3. Choose C4 as the actual nonempty finite-prefix maximum, with no replacement
   by max 0 C4, and C3 as the maximum of the exact two source quotients.
   State the resulting bound with these choices exposed before existentially
   hiding them. All constants are fixed before the final natural input.
4. Derive the complete real existence statement and then the natural-valued
   corollary by casting the actual recurrence and taking natural ceilings of
   the real constants. Do not duplicate the induction or restrict to large n.

The new files will be Applications/Resources/RoundedRecurrenceBounds.lean and
Examples/RoundedRecurrenceBounds.lean. The existing 16 statements and both
existing source files remain unchanged. These scalar results neither define
the median-of-medians algorithm nor discharge its cost bridge.

## Independently expected connected cases

- The zero function with a=c=1/4, zero offsets/tolls has source C4=C3=0.
  The completed proof must support equality in the slope constraint.
- The constant function -3 satisfies the recurrence with C1=0, C2=3;
  N=5, C3=0, C4=-3 satisfy the sharp hypotheses even with negative offsets.
- The constant function 3 satisfies the recurrence with C1=0, C2=-3.
  This supplies an actual negative-constant-toll client of real existence.
- An actual scalar recurrence Q has Q(n)=n+1 for n<=5 and otherwise
  Q(n)=Q(ceil(n/4))+Q(ceil(n/4))+n+1. The termination proof uses the existing
  exact ceiling descent, independently of the later affine theorem. Direct
  calculations give Q(0)=1, Q(5)=6, Q(6)=13 and Q(21)=48. The last value
  recurses through Q(6), so this is more than a base-prefix calculation.
  The exact source construction at cutoff 5 has C4=6 and C3=24; prove the
  all-input bound Q(n)<=24n+6 through the public sharp induction, as well as
  applying the real and natural existence APIs to Q's actual recurrence.
- With two half-size children and positive linear toll, no fixed affine
  induction estimate closes for all n. Use the exact natural-ceiling children
  and even inputs to expose the missing contraction. This is an obstruction
  to this affine proof step, not a converse theorem asserting that every
  noncontracting recurrence lacks an affine bound.

## Source and API basis

The entire frozen inventory and 559-line proof plan were read. The pinned
book's actual section 3.5 and continuation through Theorem 3.10 were read at
LF-delimited book.txt lines 1837–2035. Python splitlines also treats page
breaks and several extracted control characters as line separators; LF
indices are used here to agree with the preserved source records. No
mathematical discrepancy in the prior read boundary was found.

The proof uses Mathlib Nat.le_ceil, Nat.cast_le/lt, Finset.range, Finset.sup'
and Finset.le_sup'. Existing Resources.RoundedRecurrence lemmas supply exact
descent, slope sign, positive denominator and the sharp one-step calculation.
No new rounding operation, general Akra–Bazzi framework, resource structure
or instance is introduced. Proof restrictions, exact pins, independent axes,
full candidate audit and immediate verification remain mandatory.
