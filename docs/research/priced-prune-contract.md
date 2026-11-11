# Constant guard-price contract

Frozen for #472 before priced execution proofs. Existing WholeListTrim.Spec and
FoldedPrune.Spec remain independent values. Preserve their arbitrary-predicate
meaning and TailClosed qualification of prune's original longest-prefix result.
The new local parameter g:Nat prices each trim dispatch: empty g, nonempty
success n+g, failure2*n+g plus recursion. Empty does not evaluate p[]. Cut adds
one cons unit; tail-first prune empty costs0. Preserve full measured g=0 pairs.

For trim, Wg+g*k=W0+g*(n+1) and Wg+k²+g*k=n*(n+1)+g*(n+1).
For cut, Wg+g*k=W0+g*(l+2). Potential is length²+g*length and charge is
3*(length+1)+2*g. For arbitrary initial state and commands require the native
exact workload law and priced budget=old budget+2*g*commandCount. Prune from[]
has Wg+g*k=W0+2*g*n and Wg+k²+g*k=B0+2*g*n. Full measured reverse-workload
correspondence charges no actual reversal. Existing bind/foldr preserves ordinary
fold of independently specified output with total+k²+g*k=B0+2*g*n+(1+c)*k+1.

The nondecreasing ordered case[3,7,8,2,3] keeps[3,7,8]. At g=1, transition costs
3,4,15,4,5 give work31, priced budget43, potential12 and cons-fold38. At g=2,
work38/consumer45. Single trim g=1 costs24/consumer31. Distinct[1,2,1] g=1 gives
[1,2], work18/consumer23. Adjacent inequality accepts the wrong whole input.
Only-[1,2] remains non-tail-closed: prune[1,2]=[] at work10 and trim retains it
at work3. All these value fixtures already exist independently of pricing.

Empty trim costsg, empty prune0, empty final fold1. All-accept length3 trim/prune
cost3+g and9+3*g; all-reject cost12+4*g and9+6*g. A cut1 into initial[2,3] at g=1
has work5, initial potential6, final12 and charge11. Bounds must retain g:
trim≤n*(n+1)+g*(n+1), prune≤3*n²+2*g*n≤(3+2*g)*n². At g=1 recover the archived
5*n² prune bound. A finite coefficient independent of all g,n is refuted at n=1;
this says nothing against eventual bounds with g-dependent thresholds. Positive
empty trim refutes a pure finite quadratic bound including zero, not asymptotics.

The archive proves g=1; generic g is a new theorem of a previously proposed
source-price model. No varying measured callback or new accounting architecture.
Printed-book evidence/licensing and remaining parent reconciliation stay open.
