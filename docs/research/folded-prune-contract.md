# Folded prune contract

Frozen for #471 before runner development. Spec recursively relates each tail's
independent answer to WholeListTrim.Spec on the next cons. It is meaningful for
any whole-list predicate. TailClosed requires acceptance of a nonempty list to
imply empty-or-accepted tail. Under this condition the recursive output must
also be the original input's longest admissible prefix. Pairwise relations need
no transitivity premise for this condition.

Execution evaluates the tail first, executes trim on x::state, and adds one cons
unit. Empty execution costs zero. Expected reverse command order 3,2,8,7,3 on
[3,7,8,2,3] gives nondecreasing states [3], [2,3], [8], [7,8], [3,7,8], with costs
2,3,12,3,4. Thus work24, charge budget33, potential9 and cons-fold total31. The
same single trim has value [3,7,8] but work21 and total28. Distinct [1,2,1] has
states [1], [2,1], [1,2], costs2,3,9, final work14 and consumer19. Adjacent
inequality accepts the wrong full list. Acceptance only of [1,2] loses both
singleton cuts, yielding empty at work6 on [1,2]; single trim retains it at work2.

The cut identity is work+k²=l²+3(l+1). Use native run_potential_exact and budget
for arbitrary command lists and initial state, retaining both potentials. The
entire measured prune pair must equal run cut xs.reverse []; reverse describes
order and is not charged. Prove native budget <=3*n*n for arbitrary predicates,
then work bound; do not introduce another generic charge summation layer.

The bind/fold consumer keeps arbitrary function/seed/price c, ordinary fold value
of an independently specified output, and total+k²=budget+(1+c)*k+1. Empty prune
is([],0), empty consumer([],1), all-reject three-element prune([],9), all-accept
[1,2,3] has work9. A cut of1 into accepting initial[2,3] has work4, final potential9,
initial potential4 and charge9; omitting initial potential breaks equality.
Positive/arbitrary guard-dispatch variants remain R3; book/licensing remains #149.
