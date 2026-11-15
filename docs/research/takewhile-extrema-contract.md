# Native takeWhile extrema contract

Frozen before theorem development for #469, over the existing
`ListFusion.takeWhile`, `Resources.bind` and `ListExecution.foldr`.
The checked baseline examples in `Examples/TakeWhileContract.lean` use those
executors directly. They establish the independent expected pairs; the missing
connection is the general extrema and composition theorem layer.

For arbitrary `p : α → Bool`, list `xs`, combining function `f : α → β → β`,
seed `e : β` and declared combine price `c : Nat`, the consumer must execute:

```lean
bind (ListFusion.takeWhile 1 1 1 p xs) (ListExecution.foldr c f e)
```

Its value must be the ordinary list expression `(xs.takeWhile p).foldr f e`.
Let `k = (xs.takeWhile p).length` and `failure = if xs.dropWhile p = [] then 0 else 1`.
The existing producer bill is `3*k+1+failure`; the actual fold adds `(1+c)*k+1`.
The composite bill must therefore be `(4+c)*k+2+failure`. Neither formula becomes
a replacement executor. After an all-passing prefix and an actual failed next
element, changing any remaining suffix must preserve the full measured pair.

Producer obligations:

- Empty cost 1; nonempty cost at least 2; every input cost at most `3*length+1`.
- With one fixed identity predicate on Bool, false/true replicate inputs of
  length n return `([], if n=0 then 1 else 2)` and `(replicate n true,3*n+1)`.
- Those inputs attain minimum/maximum among **all** Bool lists of the same size.
  For positive size, best work is 2 and worst work lies between `3*n` and `4*n`.
- For every multiplier C and threshold N, there is n≥N with n>C*bestWork(n).
  A finite isolated example is insufficient to reject an eventual lower bound.

The false pipeline witness returns its seed and costs 2 at zero size, 3 otherwise.
The true witness costs `(4+c)*n+2` and returns the fold of all n values. At c=1
and positive n, its cost lies between `5*n` and `7*n`. These are bounds on the
all-true pipeline witness; producer maximality does not by itself prove a
separate pipeline maximality theorem.

Independent ordered calculation: predicate <3 accepts [1,2] from [1,2,9,4].
At c=1, cons-fold returns [1,2] and costs 13. The exhausted input [1,2] returns
the same list and costs 12. Empty input costs 2; a false-first input returns
[] and costs 3 regardless of its suffix. These distinguish source order,
terminal failure, exhaustion and demanded-prefix behavior.

Counts are declared dispatch, output-cell, predicate-test and fold work.
They exclude input construction, physical callback time, GHC allocation and
general lazy semantics. This contract selects takeWhile from residual R1;
head/reverse growth, R2–R7 and incomplete printed-book evidence remain #459/#149.
