# Counter geometry contract

Frozen for #479 before geometry proofs. Existing increment branches give bills
1,2,1,3 from empty, and final state[false,false,true]. Four transitions cost7;
three cost4, with two unit bills rather than exactly half the prefix. Five
seed-inclusive observed states contain four increments. Zero and one observed
states cost zero transitions.

For arbitrary Boolean tails, two increments starting false::bs write the low
bit twice and increment bs once. Derive even/odd work from these branches, not
potential identities. Empty and redundant false have equal work trajectories,
but their zero-step raw states differ. A three-true seed extends with four writes;
zero-start bounds do not apply unchanged to arbitrary seeds.

F(n,k)=Σ(j<k)n/2^j uses natural floor division and exponent zero. Require exact
C(n)=F(n,k)+C(n/2^k), then truncation only when the remaining quotient is zero.
F(4,2)=6 but C(4)=7; F(4,3)=F(4,5)=7; C(5)=8. Derive the geometric upper bound
independently, retain extending-write C(2^k)+1=2^(k+1), and use native real-cast
Theta. A complete-pair caller must retain final state and exact work.

Ordered bills come from each actual incWithCost on native run, not reconstruction
from its sum. Preserve arbitrary seeds, entry order, append and additive sum
reweighting. No new counter executor, renderer or generic traversal adoption.
