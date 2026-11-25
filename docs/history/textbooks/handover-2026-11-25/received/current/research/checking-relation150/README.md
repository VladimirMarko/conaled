# Existing raw checking relation: connected draft150

**New clients UNCOMPILED.** Canonical sources, integration150-plan, repositories
and compiler outputs are unchanged. This is implementation assistance only.

## Finding

The exact requested arbitrary-raw theorem already exists in canonical
`Protocol144b.lean` as `GeneralProof1.verifyDelimited_accept_iff`:

`verifyDelimited raw = true` iff there are input/certificate words with
`raw = literalPair input cert` and `(verifyBitsRun input cert).1 = true`.

Its forward proof uses `splitLiteral_iff`, whose converse covers every raw word
through `protocol_cases`, including missing delimiters and arbitrary tails
after a second delimiter. `suffixBits_iff` and `splitLiteral_none_iff` give the
related exact parsing and malformed classifications. These are already part
of the retained delimiter proof family, not a new mathematical gap.

`CheckingRelation150.lean` imports `Protocol144b`, reuses the two general
equivalences in anonymous examples, and checks eight independently fixed
literal parser cases plus the mixed pair's actual checker-result equality.
It does not duplicate the parser proof or add a second public language API.
Well-formed cases do not guess acceptance values. Expectations were saved
before the new client body; none of these new clients has been compiled.

## Dependencies and observations

Resolve `Protocol144b` and its `DelimiterPrelude144b` import to the exact
canonical P149 members recorded in MANIFEST.json. Their sole normal project
dependency remains the existing FrontEndStreamTapeMachine import. Preserve all
parent bytes. The manifest records full descriptors, relevant declaration
slices, and a plan of 11 readable / 2 expanded / 4 selected-root observations.
The three anonymous examples are checked by compiling the whole new body.
There is no generated carrier or compiler invocation in this handoff.

## Actual next mathematical connection

The next task is generic conventional polynomial-decider/checking-relation
packaging, not another proof of the arbitrary-raw iff. Connect the existing iff
to the already passed composition150a: its actual target is the complete
`PrintMove.decidedCfg (verifyDelimited raw) ...`, whose terminal control is
accept precisely for true. Preserve the existing native/target witnesses,
counts, tape, supplied starts/defaults, and fixed finite alphabet/control.
The literal delimiter remains a designated nonblank input letter, distinct
from present false; it is not the physical tape blank.

Keep the fixed time allowance `N^k + k`, with N the complete literal pair
length. The selected checking-relation convention's certificate bound is
`I^k`, without an added constant: the existing
`binaryYes_iff_exists_small_delimited_certificate` already supplies
`cert.length <= input.length^2`, and preserves the delimiter's +1 in pair size.
The runtime and certificate exponents need not be identified. No new generic
record, conventional-NP equivalence, effective transition-table
construction, qualification or acceptance is established by this small draft.

Retain only EXPECTATIONS.json, CheckingRelation150.lean, README.md and
MANIFEST.json from this directory; parent bodies stay at their canonical routes.
