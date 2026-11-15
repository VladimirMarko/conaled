# Finite randomized execution: first elaboration correction

Candidate b059af864122a6b09912ba0db8095f422f8991bf, tree
c840851e8147e966507b96f240bb4f826150bc79, is the ordinary child of
94f10cf511785d2ecf50817e3c24abb3c6287010 on work/fdsa-ch03-random-selection.
The worktree is clean. The local commit and staged whitespace check actually
exited zero; commit tool f04556. No Lean/Lake command was run by this author.

## Preserved actual failure

C03-RANDOM-RUN-ELAB-001 is the first focused finite-execution failure, actual
exit 1, root-owned 51952 CLOSED, terminal 9341a5, root closure 2fbbbb.
The complete 14,916-byte outer log and complete closure were read in 039300.
All original failure and candidate04 records remain unchanged. Copied XR
verification remains XR evidence only, not Chapter 3 candidate validation.

## Exact correction and statement assessment

Only Applications/Resources/RandomSelectionRun.lean changed. The actual run
definition differs only by alpha-renaming its equality witness hstep to
_hstep because that witness is consumed by the equation compiler's termination
proof. Its recursive state, uniform occurrence sampler, selected child,
returned value, trace and source costs are unchanged. The warning-as-error
and unused-variable linter settings remain enabled.

The empty equation now explicitly reduces the empty measured length. The
cons equation uses congruence of PMF.bind, function extensionality and a split
on the actual step result to equate the dependent and ordinary matches.
Both recursive support proofs zeta-reduce their local action binding before
rewriting its discriminant. These changes do not alter a theorem premise or
conclusion.

All 30 declaration headers in the finite-run module were compared completely,
including the let-containing run_cons statement, and remain byte identical.
The other three source files are unchanged, including every independently
expected worked value, trace and call count. The 22 pre-existing provenance
files, original failed source and the 60-name explicit-@ input are preserved.

## Full scope and requested continuation

Focus Applications.Resources.RandomSelectionRun and Examples.RandomSelectionRun.
The unchanged Statements60-candidate04.lean is rebound by candidate.json to
this immutable successor. It still covers all 60 public names (19 previous
step names plus 41 finite-run names); both private proof helpers remain in
whole-source/audit scope. No new actual-type, full-check or acceptance credit
is asserted.

All original finite-execution claims remain required: each supported outcome
has the sorted-index value and visible Option failure contract; each active
step draws a current occurrence freshly; the selected strict child decreases;
active-call count is at most input length; n <= W <= n(n+1)/2 and
W <= T <= 9W+2 hold on the same execution. No duplicates or valid-rank
restriction was added to those existing pathwise statements.

The expectation, absorbing-size/residual bounds, exact natural-parameter tail,
worst-case attainment and pivot-policy obligations C03-059–080 remain later
work. No probability extension belongs to this correction. Both independent
axes, complete Chapter 3 validation/audit and immediate candidate verification
remain coordinator gates. All source and own records are held for root's
next focused check.
