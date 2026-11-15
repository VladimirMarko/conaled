# Native behavioral contract for #463

Frozen before proof implementation against accepted integration `767249cc`.

The consumer is the existing two-request forwarding client. An environment is
an unchanged finite list of tagged Boolean replies. Both requests are issued
before the first reply. The required observation is the complete
`OverlappingQueries.native` result: rejection or acceptance, both pending or
answered states, result, and ordered tagged history. No eventual environment
reply or fair scheduler is assumed.

The three selected levels are the independent native observation, the
forwarding relay strategy at the same schedule, and the actual shared-wire
interaction of two negation strategies. The latter implements forwarding by
double negation. The two downward observations are middle-channel hiding and
client projection followed by native state execution. Vertical comparison must
retain the same environment index and prove the actual observation equation,
not merely invoke relational transitivity.

Accepted schedules require constructed behavior at every level. Pending
schedule boundaries and malformed-schedule rejection must be recovered.
Response production after a supplied reply is a finite evaluation guarantee;
it is not eventual response in an infinite execution. Empty implementations
or ones that permanently suppress supplied replies do not meet this contract.

A separate interaction compatibility case covers every legal finite wire
prefix, including intermediate administrative phases. Boundary value maps
must preserve each component response and use the same middle value map on
both components. A single constructed translated wire must realize both
component projections. Its hidden trace must equal the translated outer trace
in exact global order, with correlation slots unchanged. Two successive
boundary translations must paste through that same wire. This all-prefix
claim is separate from the selected schedule-boundary observation contract.

Negative cases retain the unchanged observation: legal negation is not
forwarding; dropping response order loses distinguishable observations;
unmatched middle translations do not preserve wire legality. The experiment
may reuse existing exact squares or directed coverage after their concrete
obligations are proved. It does not adopt a universal game or double-category
framework or change #440's accepted behavior.
