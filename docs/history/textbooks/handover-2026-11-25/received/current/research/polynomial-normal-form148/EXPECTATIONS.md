# Natural-polynomial normal form — fixed expectations before compilation

This is preparatory mathematics for the remaining conventional complexity
contract. It is not installed source, a compiled theorem, an independent review,
a machine construction, or an NP claim. Root owns compilation, after the active
C147 whole check has released its output boundary.

For an arbitrary polynomial `p : Polynomial Nat`, choose the exponent once,
before input size: `k = p.natDegree + p.eval 1`. Prove the universal bound
`p.eval N <= N^k + k` for every natural `N`, with no positivity restriction on
`N`, no assumed coefficient bound, and no exponent chosen separately for each
input. The zero polynomial is included; its selected exponent is zero.

The proof must retain these three actual cases:

- `N=0`: monotonicity gives `p.eval 0 <= p.eval 1 <= k`.
- `N=1`: `p.eval 1 <= k <= 1+k`.
- `N>=2`: writing `S=p.eval 1` and `d=p.natDegree`, coefficientwise summation
  gives `p.eval N <= S*N^d`; `S <= 2^S <= N^S` gives the desired power.

Independent arithmetic checks of the intended choice are: zero polynomial
has `(S,d,k)=(0,0,0)`; constant seven has `(7,0,7)`; `X` has `(1,1,2)`; and
`2*X^2+3*X+5` has `(10,2,12)`. For the last polynomial the values at `0,1,2`
are `5,10,19`. These numbers are expectations, not compiler results.

This bound transports an already proved time allowance. It does not prove
the existence, correctness or time bound of any machine, exact-length witness
padding, executable finite tables, or equivalence with a nondeterministic class.
No resource, recursion, heartbeat, linter, transparency or search-path override
is authorized. Preserve failed attempts and actual reading limits if a later
compiler check requires proof repairs.
