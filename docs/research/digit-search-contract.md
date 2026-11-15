# First-hit and finite-mean contract

Frozen for #478 before execution proofs. Native findIdx? fixes first occurrence:
[0,4,8,9] returns some2 at cost3, [0,4,3] returns none at cost3, and [8,8] returns
some0 at cost1. Each inspected digit costs1; empty costs0. A failing prefix then
a hit ignores any later suffix. Work must match native takeWhile0 0 1(!p).

The independent population is all functions Fin n→Fin10 once each. Its ordered
list presentation is head-major: words0=[[]], successor is digit-major cons
flatMap. At length2 the first words are[0,0],[0,1]; positions9/10 are[0,9],[1,0].
List.sections instead starts[0,0],[1,0], so cardinality is insufficient for order.
There are50 first hits,25 last hits and25 failures; costs1,2,2 give total150 and
mean3/2. At n=1 all10 words cost1; at n=0 the sole empty word costs0.

The mean must sum actual execution over the population, not be defined as a
closed expression. Target total recurrence T(n+1)=10^(n+1)+5*Tn and
Tn+2*5^n=2*10^n imply E=2−2/2^n. Preserve finite strict E<2 and native rational
convergence. Weighted Hn=Σ(k=1…n)k/2^k differs by n/2^n; at n=1 H=1/2 and E=1.
Reuse existing FiniteSums remainder/modulus, retaining failures and denominator1
at zero. No arbitrary distributions or physical runtime claims. Printed source
wording/licensing remains unverified under #149.
