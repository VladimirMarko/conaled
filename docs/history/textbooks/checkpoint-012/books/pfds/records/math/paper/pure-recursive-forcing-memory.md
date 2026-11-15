# Pure cache certificates and represented memory

Local10019; root implementation in Pure/Memory.lean and its connected example.
This is part of the existing implementation/review loop, not an accepted slice.

## Intended contract

CellRep distinguishes unforced thunks from cached values. An unforced thunk
needs its original body code and an environment representing the immutable
meaning's effective body environment. A cached value needs a represented pure
value and an actual finite Progress.Evaluates derivation of that meaning's
pure body. Nothing assumes that unforced thunks terminate, that pending forces
are distinct or that raw values themselves are unique representations.

StateRep requires bounded raw memory and an occupied, represented cell for
every world entry. The semantic frontier bound and freshness follow from those
two facts. Other raw cells may exist without semantic entries; no represented
address can point to such a cell. CellRep is monotone in the immutable world;
arbitrary world extension alone is deliberately not claimed to preserve StateRep.

Fresh allocation adds the body meaning and transports all earlier cell
certificates. Actual memoize replacement preserves StateRep when supplied with
the finite pure body derivation and represented return value. It permits writing
an already cached cell. Cache-result agreement follows from determinism of a
fixed pure body input; it is semantic agreement, not raw syntactic equality.

## Connected clients and statement review

The literal client first allocates an unforced suspension with no evaluation
premise. Its independent two-transition pure body calculation then justifies
actual memoization. A later unrelated delay preserves the original cache
certificate through the public world-extension laws.

The cyclic client uses the same function/delay definitions as the checked pure
recurrence example. Its closed recursive environment is represented by the
public GroupRep.unroll theorem. This is a valid unforced memory even though
the already proved positive recurrence rules out every finite pure body result.
The public no-cache theorem consequently excludes every cached raw value for
that meaning. This is a certificate-level statement, not yet a proof that the
raw evaluator preserves the invariant or cannot reenter that body.

Statement review checked world/memory separation, effective recursive captures,
the absence of termination/nonreentry assumptions for unforced cells, occupied
address bounds, and semantic rather than syntactic cache agreement. Initial
cache certificates are explicit input obligations. The intended raw execution
bridge must construct later certificates from already performed execution;
assuming those certificates for all future writes would be circular.

## Focused evidence

- r1 exit1: only the delay address witness had an underconstrained meaning.
- r2 exit1: the explicit meaning exposed a symbolic Nat equality inside put;
  direct reflexivity was insufficient.
- r3: core GREEN in20s after normalizing that equality. Only the example lookup
  still needed its explicit address argument.
- r4: complete target GREEN,752jobs, exit0, unchanged inputs; example16s. The
  explicit address was the only example correction. Public statements and
  independently expected values/counts remained unchanged throughout.

The complete JSON/log sequence is retained in session/validation under
suspension-pure-memory-rN. No admissions, added axioms, native shortcuts,
raised proof budgets or linter suppressions were used. Full candidate build,
exhaustive audit, final verification and independent review remain open.
