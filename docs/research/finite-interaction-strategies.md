# Finite interaction strategies and retained traces

[#390](https://github.com/VladimirMarko/conaled/issues/390) constructs a bounded
serial forwarding model alongside the existing retained-handler semantics.
The comparison proves equality of the entire selected service history and
return/pending result, including for history-dependent responders. It also proves
an exact composition law for all finite positions in the forwarding-policy
family. These are different claims from equality of final returned Booleans.

## Frozen native contract

[FiniteQueries](../../Applications/Interaction/FiniteQueries.lean) was specified,
checked and committed before the strategy construction. Its environment maps the
list of previous replies to `Option Bool`. `none` represents an unanswered query;
it does not erase that query or assert that no action happened. `native` performs
a finite number of queries and returns the last reply, stopping at the first
unanswered query. `Legal` admits complete query/reply rounds and an optional final
outstanding query.

The independent calculations are:

| Client and responder | Return | Selected service history |
|---|---|---|
| Once, constant `b` | `some b` | Ask, Reply `b` |
| Twice, constant `b` | `some b` | Ask, Reply `b`, Ask, Reply `b` |
| Twice, first `false` then `true` | `some true` | Ask, Reply `false`, Ask, Reply `true` |
| Twice, no reply | `none` | Ask |
| Twice, one `false` reply then silence | `none` | Ask, Reply `false`, Ask |

`handler_native` connects every finite native query loop to the actual
`RetainedException.Tree`, `fold` and retained-state algebra. It preserves an
arbitrary prior trace prefix and lets the operation inspect prior replies.
Pending completion becomes an exception, with the issued query retained.
This reuses the existing interpreter rather than implementing another state
and exception framework. The comparison does not depend on rollback policy;
#381 retains the separate Keep/Undo result.

## Primary sources and chosen restriction

AJM §2.1 specifies role-labelled legal positions; §2.2 describes strategies
through positions and inducing move functions. Section 2.4 defines composition
by matching projections on an intermediate interface and hiding its moves.
The copy-cat identity is the forwarding precedent. Our protocol allows repeated
serial Boolean exchanges and a fixed response map. It does not construct AJM's
exponentials, representation equivalence or PCF interpretation, so its
full-abstraction theorem is not used.
[Abramsky, Jagadeesan and Malacaria, version 2](https://arxiv.org/html/1311.6125v2).

Levy's Definition 6.7 retains deterministic well-bracketed plays; Remark 6.8
distinguishes which players obey bracketing. Here both sides obey the stricter
single-outstanding-query discipline. No pointer arena, general CBPV adjunction
or higher-order game model is constructed.
[Levy, *Adjunction Models for Call-by-Push-Value with Stacks*, pp. 22–23](https://pblevy.github.io/papers/ctcs02journal.pdf).

These source comparisons motivate the construction. The local theorems are
proved directly. In particular, the arbitrary history-dependent environment is
not asserted to be one of AJM's history-free strategies. No source theorem is
silently extended to physical effects or our repeated-query protocol.

## Independent strategy construction and composition

[FiniteStrategies](../../Applications/Interaction/FiniteStrategies.lean) gives a
partial deterministic transition system for a forwarding component. Its four
phases are idle, requested, waiting, and answered. The legal moves are a client
query, forwarding the query, receiving a service reply, and forwarding that reply.
The policy `f : Bool → Bool` transforms the reply. Phase transitions enforce
nesting and permit no second query while a response is outstanding.

`RelayPlay f` is the set of finite paths from idle, including administrative and
unanswered prefixes. `relay_nonempty` and `relay_prefix` prove its position laws.
`player_deterministic` proves uniqueness of the component's next move when it
is Player's turn. `roles_alternate` checks role alternation; Opponent's Boolean
reply is not predetermined. This is an independent protocol semantics, not a
wrapper around the native loop or the handler interpreter.

Two components interact on channels A, B and C. Each B query or reply is one
shared event, consumed with opposite roles by the adjacent components. The
serial `wireStep f g` protocol records those events explicitly. `left_local` and
`right_local` prove that each interaction step projects to the appropriate
component path; `components` lifts these facts to every finite interaction.
The final environment is on C and the original client is on A.

`hideMiddle` removes only B moves. `hide_local` and the generic finite-path
projection lemma prove that hiding an interaction yields a legal `f ∘ g` relay
play. The converse is also checked: `insertMiddle`, `Align`, and `lift_path`
construct matching intermediate events for every external relay play.
`compose_exact` therefore proves

```text
CompositePlay f g xs ↔ RelayPlay (f ∘ g) xs.
```

This is equality of the entire finite-play languages for this restricted policy
family. `identity_left`, `identity_right`, and `composite_associative` derive the
corresponding laws at that hidden boundary. They do not identify the differently
labelled internal traces of alternative associations. This is a serial interaction
construction with proved component projections, not a general parallel scheduler
or a theorem about every pair of arbitrary AJM strategies.

## Selected executions and observation boundaries

[StrategyQueries](../../Applications/Interaction/StrategyQueries.lean) constructs
a finite client's actual A/B/C execution against the adaptive environment.
`network_legal` proves it is a path of the interaction protocol. For example, two
forwarders emit A Ask, B Ask, C Ask, C Reply, B Reply, A Reply for each completed
round. A missing service reply ends after the three queries, preserving the C
query in the service observation.

`network_native` proves the exact service-history comparison for arbitrary
response policies. The final result is transformed by their composite; the raw
service replies are retained unchanged. Its identity specialization
`forwarding_native` agrees with the native loop, and `forwarding_handler` agrees
with the existing handler. `selected_contract` packages the two legal component
projections, the hidden composition, and the exact native observation.
`service_hiding` separately proves that hiding B preserves the C service history.
The [checked clients](../../Examples/FiniteStrategies.lean) exercise all frozen
calculations through these public results, not just by normalizing native code.

Changing one forwarding policy to Boolean negation changes the selected returned
value while retaining the raw reply. Two negations cancel at the full finite-play
boundary through `compose_exact`. Policy changes require the local response
agreement and its composed meaning; they do not require rewriting a global
finite-loop induction.

The controls use actual malformed forwarding traces. A duplicate forwarder
requests again before delivering the first reply; a cached forwarder answers a
new request without forwarding it. Both traces fail the protocol. With a constant
responder their chosen final Boolean still matches the intended client, but their
service histories have the wrong number of rounds. `unmatched_middle` also rejects
a B reply inconsistent with the C response.

A separate `constantReturns` setoid identifies finite clients exactly when all
constant responders yield equal final returns. Its quotient admits each constant
return observation via `Quotient.lift`. The once/twice clients are equal there.
`adaptive_does_not_descend` and `history_does_not_descend` prove that neither the
adaptive reply observation nor the exact service history can be added to that
quotient. This validates a deliberately coarse observational boundary rather
than requiring every client to retain the maximum possible data. No contextual
congruence for an unimplemented higher-order language is inferred.

## Architecture disposition and remaining owners

Reuse the existing retained-handler interface for finite query clients. The
strategy comparison supplies a separately useful account of intermediate-channel
matching and hiding, with exact finite-play equality. Keep this bounded model
experimental; the client does not justify a universal strategy interface or
migration of native handlers. The local `Path` helper supplies labelled finite
transition proofs within this experiment; it is not a replacement for the
repository's unlabelled reductions, indexed syntax paths or ownership runs.

The native route pays for the loop/operation comparison. The strategy route also
pays for phases, channel projections, local matching and lifting. Once established,
its laws cover arbitrary finite histories and arbitrary Boolean response policies.
The source callback/frame relation in #380 preserves a different operational
machine and selected arithmetic certificate; it does not already prove this
channel-hiding law. No measured author or execution advantage is claimed.

The games re-entry test has now received a bounded checked comparison. #196/#36
retain higher-order or overlapping-query interaction when a concrete client needs
it; #290 owns the corresponding observation and interpretation comparison. Such
a client must specify legal contexts, bracketing, synchronization and the chosen
quotient before a full-abstraction claim can be considered. Infinite interaction,
physical adapter adequacy, crash persistence and concurrent scheduling remain
separate contracts. A finite model recording a query is not evidence that a
physical service acted.

This result does not displace the other traditions. #371/#386–#389 retain the
internal selected-solution provider; #200/#36/#235 retain general probabilistic
sequencing and its model hypotheses; #289/#36 retain modal/higher combination;
#27/#36 retain analytic hiding and nonconstant-port dynamics; #289/#290 and
#100/#36 retain source/model admission under their existing gates. #107 stays
paused, #108's held-out theorem remains unselected, and #260 stays inactive.
