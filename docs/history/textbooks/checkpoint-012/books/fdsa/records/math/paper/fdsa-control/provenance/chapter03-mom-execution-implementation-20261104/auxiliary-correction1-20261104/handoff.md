# C03-AUX-ELAB-001: auxiliary concrete-value correction

Candidate d204aa2c64937cb1f151bd52759bfcfa50e4248f, tree
6dd89b07000257bb72fa79a76aa5371cc94c2098, directly extends the immutable
8fef3ea5964f058f1c0036f53414d5d06fa56e59 auxiliary candidate.
Only Examples/SelectionAuxiliary.lean changed. The source worktree is clean.

## Actual failure and exact correction

The complete original focused log was read in tool 150833: 7,536 bytes,
SHA-256 3c643708f63fd68cb13ae619cc7a046e95da8650b3e0ef2ddd1ca07efed10cb0.
The run closed with actual exit 1, owned session 21687, terminal a10808 and
root closure/readback 0d93d8. Applications.Resources.SelectionAuxiliary built;
its example module exposed ten unsuccessful rfl value goals. None of the cost
goals failed. Canonical ordered-list observations do not reduce definitionally
in these positions. This is an elaboration-proof correction; the independent
expected mathematics is unchanged.

Three empty/out-of-range goals now consume slowSelectRun_none. Seven successful
value goals still consume the original slow-selection or slow-median public
value correspondence, then use Applications.Sorting.sortOn_eq_insertionOn.
Their concrete insertion indices are proved with decide +kernel, following
the established Examples/RankSelection.lean client pattern. No native-evaluation
shortcut, admission, axiom, source tariff or mathematical premise is introduced.

The source comparison mechanically confirms all twenty complete authored
example headers are byte-identical. Every expected result and cost remains:
empty selection 2; singleton value 7 with 4 calls; singleton invalid indices
1 and 17 with 5 calls; the duplicate occurrence rank; singleton median 7/6;
even reversed pair 2/10; equal pair 4/9; range-five and reverse-range-five
median 2 with 20 and 30 calls. Remaining symbolic, monotone-map and cutoff
clients are untouched. The core file and all six inherited value/chunk/pivot
files retain their exact original identities.

## Scope and validation boundary

The full existing Chapter 3 loop remains the acceptance scope. This correction
does not start a smaller acceptance workflow, remove any obligation, or resolve
the finding before actual qualified rechecking. The original first failure,
eleven prior provenance files, original source commit and all forty prepared
public names are preserved. There are still two auxiliary definitions,
eighteen core theorems and twenty example theorems, with no authored private or
anonymous declarations.

The unchanged explicit-@ AuxiliaryStatements40-candidate1.lean remains the
inspection program: 2,783 bytes, SHA-256
e3910f89e19232f125eca8c166556f2852ba9d171fe6317d066c9a5ab0a371ae.
Reusing that prepared input does not grant actual printed-type credit.
Every actual type, full candidate check/audit and independent review gate
remains required for eventual Chapter 3 acceptance.

The complete diff and updated source were read in 1b229d. The whitespace check
and local commit completed with actual exit 0; commit tool 19d030.
No Lean/Lake, compiler probe, cache operation, environment/configuration change,
qualified-checkout modification, canonical-control edit, GitHub mutation or push
was performed by this author. No new chop/map source was created before the
failure arrived.

## Next action and hold

Root owns the serial focused check of Applications.Resources.SelectionAuxiliary
and Examples.SelectionAuxiliary at the exact new candidate. All author source
writes are HELD until that terminal or a new assignment. After a passing result,
the next additive slice is the measured positive-size take/drop chopping
recursion and proof-carrying payload-median map. The actual nested selector,
termination/correctness, exact source-call recurrence, monotone scalar F and
uniform linear theorem remain outstanding. The pivot author's separate
correction must be incorporated only at the exact commit supplied by root.
