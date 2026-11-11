# Whole-list trim contract

Frozen for #470 before implementing measured recursion. `Accept` admits an empty
list or one accepted by `p : List α → Bool`. `Spec` independently requires a
prefix, admissibility and maximal length among all admissible prefixes. It has
no monotonicity or tail-closure premise. `Spec.of_checks` lets ordinary finite
prefix calculations certify an expected answer independently of a runner.

The native fixture module `Examples/WholeListTrimContract.lean` proves:

- Pairwise nondecreasing [3,7,8,2,3] has longest acceptable prefix [3,7,8].
- Pairwise distinct [1,2,1] has longest acceptable prefix [1,2]. Adjacent
  distinctness accepts the original whole input and therefore is insufficient.
- The predicate accepting only [1,2] has output [1,2] on [1,2,3]. It is not
  tail closed, since [2] is neither empty nor accepted.

The runner must test each nonempty current list, return it on acceptance,
and otherwise recurse on dropLast. Empty exhaustion returns []. Abstract
length prices are fixed independently: successful guard at length k costs k;
failed guard plus dropLast at length k costs 2*k; empty costs zero.
Thus the first fixture's observed bill must be 10+8+3=21 and the second's 6+2=8.
These are selected prices, not physical predicate time or ListExecution.init's
separate prices. A formula is not an implementation of the recursion.

For every predicate and input, with input length n and output length k, require
`work+k*k=n*(n+1)`. All-reject output is [] and bill n*(n+1); all-accept returns
its input and bills n, including zero. Empty output need not satisfy p.
Upper bounds must retain the positive-size premise when using `2*n*n`.
A quantified all-accept family must reject a universal quadratic lower bound.

The consumer must execute existing measured bind followed by ListExecution.foldr,
with arbitrary price c, function and seed. Independently specified output out
must determine value `out.foldr f seed` and bill
`total+out.length*out.length=n*(n+1)+(1+c)*out.length+1`.
At c=1, cons-fold gives [3,7,8] with total28 and [1,2] with total13.

Keep existing element-predicate SuffixTrim unchanged. Cut, folded prune,
TailClosed equivalence, cumulative potentials and positive-dispatch variants
remain R3 under #459. R5 is untouched. Workload/Potential retain their existing
ownership. Full printed chapter evidence and licensing remain #149; no new
runtime, resource hierarchy, general lazy semantics or whole-R3 completion.
