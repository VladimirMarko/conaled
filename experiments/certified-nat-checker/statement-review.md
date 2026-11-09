# Statement review for the new checker client

The original 20 sources remain byte-preserved archive selections. This review
covers the new `CheckerClient` declarations and how they use those sources.

| Declaration(s) | Intended statement and checked connection |
| --- | --- |
| `natRep`, `endpointSquare` | Identity interpretation of `Nat`; every supplied endpoint yields a square using its existing universal agreement. No inverse or additional algebraic capability is assumed. |
| `successorSquare`, `doubleSpec`, `doubleEndpoint` | The consumer adds one. Specification `n+n` and implementation `2*n` agree by `Nat.two_mul` for all natural inputs, including zero. Endpoint label `double` is explicitly chosen and does not identify an arbitrary external declaration. |
| `doubleThenSuccessor`, `doubleThenSuccessor_correct` | Existing `Squares.compose` proves that implementation composition returns `(n+n)+1`. It is a function-level equality, not a binary-execution theorem. |
| `report`, `report_sound` | Only a successful supplied checker result is mapped to result-plus-one. The soundness theorem consumes `acceptTokens_sound`; acceptance is its explicit premise, not hidden agreement of two executions. |
| `accepts_three`, `reports_seven`, `accepts_zero` | Three pairs give six; the successor gives seven. Zero pairs give zero. `acceptTokens_render_iff` supplies actual acceptance from the arithmetic facts, and `report_sound` supplies the consumer result. These witness satisfiability of the generic premise. |
| `report_rejects_noncanonical` | The supplied `reject_noncanonical` theorem implies that the consumer returns `none` when no claim renders to the token list. The hypothesis is discharged in each negative client. |
| `rejects_wrong_value` | The canonical request claiming seven for three pairs is parsed by `parseTokens_render`; the check rejects the false result. |
| `rejects_wrong_name`, `rejects_wrong_operator`, `rejects_extra_token` | Exact token equality contradicts the wrong name, wrong operator or list length. No stronger parser normalization is assumed. |
| `decode_leading_zero`, `rejects_leading_zero` | Standard digit parsing proves `03` denotes three. Canonical rendering would have to be `Nat.repr 3`, which is not `03`. This tests the roundtrip restriction rather than confusing it with a failed natural-number parse. |
| `queens_endpoint_source` | The actual imported endpoint's `run` equals the actual imported fixed-Word16 `cqueens` for every natural input, via its proof field. No concrete numeral evaluation or unrestricted-width counting claim follows. |

Focused development first proved the positive cases and universal composition.
Direct `decide`/`decide +kernel` attempts on full negative parser evaluations got
stuck in imported string reduction, so the retained proofs use public parser
contracts and string lemmas. The expected rejection results were unchanged.
A focused run also omitted synchronous elaboration and exhausted the virtual
thread allocation; retaining the prescribed `Elab.async=false` resolved that
setup failure. Final acceptance uses the complete portable fresh pipeline.

No new axiom, admission, native-decision shortcut or runtime source identity is
introduced. The axioms of these claims are checked by the isolated exhaustive
audit. The report keeps native execution and broader preview inspection outside
this slice.
