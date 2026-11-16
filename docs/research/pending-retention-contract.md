# Bounded retention for durable pending requests

This feasibility study for [#568](https://github.com/VladimirMarko/conaled/issues/568) compares three bounded-storage contracts. Finite lifetime permits full-history retention with explicit exhaustion. A retained-outcome window needs disclosed expiry and crash-safe peer retirement. Indefinite finite-identity reuse needs a target that can revoke every old actionable message; no such realization has been identified. These are proposed contracts and paper arguments, with policy selection and checked implementation still pending.

The unrestricted [#540](https://github.com/VladimirMarko/conaled/issues/540) service remains unchanged. Its full-history acknowledgements must not acquire an implicit expiry date.

## Existing guarantees and growth

The current peer keeps lifetime-unique natural-number identities and terminal receipts. Publication atomically produces the effect and records its receipt. `peer_effects_unique` proves the corresponding no-reexecution result for the existing peer transitions; deleting entries would add a transition outside that proof. See [Peer](../../Applications/FRP/PendingCrash/Peer.lean), particularly `dispatch` and the terminal-stability lemmas.

[Runtime](../../Applications/FRP/PendingCrash/Runtime.lean) separates its four-entry local queue from unrestricted external request/reply lists. External traffic survives local crashes and can be duplicated without accepting new work. Local `drain` leaves those external messages intact. Replays duplicate actually submitted traffic; the model does not admit forged receipts. A bounded target must preserve that provenance or supply an alternative admission contract. [Journal](../../Applications/FRP/PendingCrash/Journal.lean) retains complete frames and reserves fresh addresses during preparation, including interrupted attempts. Repeated migrations and failed preparation can therefore grow storage without increasing completed request count.

[Refinement](../../Applications/FRP/PendingCrash/Refinement.lean)'s `DurableFrames` validates the complete accepted frame sequence. `execute_acknowledged` in Runtime, using [Durability.Related](../../Applications/Durability/Protocol.lean) and [acknowledged_survives](../../Applications/Durability/Clients.lean), preserves acknowledged records and the prior history prefix. The independent `execute_source_refinement` additionally preserves ordered Boolean-delay behavior. Current logical state is not a replacement for the full-history observation contract.

[Retention](../../Applications/Durability/Retention.lean) already gives a finite-lifetime alternative: a fixed incarnation, nonwrapping position limit, retained Boolean suffix and exact prefix-parity summary, with explicit expired/exhausted responses. `read_refines`, `classify_refines` and `reserved_fresh` prove its observation policy. [RetentionBanks](../../Applications/Durability/RetentionBanks.lean)'s root/cut laws and [RetentionResources](../../Applications/Durability/RetentionResources.lean)'s `reachable_bounds` cover that local bank machine, not a remote peer or pending protocol.

## Candidate contracts

| Candidate | Retained observations | Naming and admission | Limitation |
|---|---|---|---|
| A: finite lifetime, full history | All accepted frames and terminal request outcomes; current and unresolved state | At most K identities, J fresh journal allocations; bounded traffic | Explicit exhaustion can stop accepted unresolved work |
| B: finite lifetime, expiry | Current state, live selected outcomes, and a bounded suffix of released outcomes | Nonwrapping identities below K; monotone local/peer retirement floors | Old retry/query rights expire; retirement can block admission |
| C: indefinite reuse under a closed target | Current state and explicitly scoped retained results | Finite identities reused only after complete replay revocation | No concrete reset target has been identified |

A frame record, request identity and effect occurrence are distinct. A request can produce several frame records. B and C do not offer historical frame queries; their acknowledgements promise their stated retained observations. Expiry removes later lookup/retry rights, not safety facts about past effects or the preservation of a live selected output.

### A: finite lifetime with explicit exhaustion

Fix K request identities and J journal allocation slots. Neither domain wraps or resets on restart. Retain every accepted frame and peer terminal receipt for the lifetime, including after exhaustion. Bound external queues and refuse input before allocating beyond their capacities. Admission and fresh-allocation exhaustion differ from temporary transport busy and from cancellation.

After allocation exhaustion, an accepted unresolved request remains inspectable as unresolved, with its selected output and any retained evidence. Its peer effect might already have occurred or could still occur through previously submitted traffic. Exhaustion never reports prevented, rejected-before-acceptance, or no-effect on that basis. Queries can report retained peer evidence, but local completion may remain stopped if it requires another durable frame. There is no completion promise under arbitrarily many failed fresh allocations: even an eventually crash-free run may begin that interval with its finite budget already spent.

The proposed representation uses a crash-safe high-water mark reserved before exposing each allocation. Its own bounded persistence mechanism is part of the target obligation; the existing abstract `Journal.nextAddress` field is not evidence of a physical implementation. Repeated creation of new lifetimes while keeping old receipts is not an indefinitely bounded service.

### B: finite lifetime with durable expiry and peer rejection floor

Fix K, a target retained released-outcome window W, two live slots, and a shared pool of U=W+2 outcome reservations. IDs remain unique within this finite lifetime. The proposed API exposes current logical state, live phase/input/selected output, retained released outcomes and a durable expiry boundary L. Below L, retry and query return `expired L`; invalid IDs/incarnation, future IDs, conflicts, busy and exhaustion remain separate responses. No historical frame-query API is provided.

Admission reserves one shared-pool entry for the occurrence before acknowledging it, in addition to a live slot. That reservation remains occupied through acceptance, computation, terminal commitment and release. A terminal occurrence becomes released only after local terminal commitment, route closure and owned callback cleanup; release fills or marks the same reserved entry and allocates no new outcome slot. The peer can acquire an entry only for an admitted reserved identity, so its retained entries also fit U. A peer-published but locally computed request is still live and cannot be retired. To make room, retire only a contiguous prefix of released terminal occurrences, never crossing an unresolved lower identity. A cancelled higher identity cannot force that crossing. If no reservation is free and space cannot be reclaimed, refuse admission. In particular, with W released outcomes and two live requests, a permitted terminal transition or release uses the existing reservation even when a lower unresolved identity prevents retirement; reservation does not bypass head-order or route-closure guards or guarantee progress. No third request can enter without freeing a reservation and a live slot. W is the retention target; unresolved ordering can temporarily retain up to U released/live outcomes in total. This is not an exact last-W-accepted-requests policy. Expiry remains explicit at L; the physical capacity alone never revokes rights.

There is at most one retirement in flight. Fresh admission stops throughout retirement, keeping retained peer entries bounded even when retirement acknowledgements are lost. A proposed simplification freezes other local durable mutations too; queries, recovery and retirement reconciliation remain available. External traffic already submitted can still reach the peer, whose existing terminal-stability rules remain necessary.

| Phase/cut | Durable action | Observable and recovery behavior |
|---|---|---|
| Propose target t | Check that every identity in [L,t) is released terminal and can expire | Before publication, old rights remain; no retirement request may leave |
| Relinquish locally | Publish current/live state, new L=t and pending target t together | This publication is the sole expiry point; old queries now return expired, even if cleanup never finishes |
| Advance peer floor | Publish F:=max(F,t) before, or atomically with, receipt deletion | Every command below F, including reserve, is rejected as expired without effect; floor survives restart |
| Delete covered receipts | Reclaim entries below F; retain bounded pending progress | Crash can leave undeleted entries, but cannot restore admission below F |
| Acknowledge completion | Reply identifies target t and confirms deletion for that target | Delayed old replies cannot complete a different pending target |
| Finish locally | Publish no-pending state, preserving L and all current/live observations | Crash selects pending or completed state; either is compatible with the advanced peer floor |

The invariant is F ≤ L, with one pending target equal to the published L during retirement. The peer may be ahead of locally recorded cleanup completion, never ahead of durable local relinquishment. Local recovery retries/queries the same target; it does not demand a receipt already authorized for deletion. Monotone `max` makes delayed old retirement requests harmless within the nonwrapping lifetime. An acknowledgement of deletion is required before admission resumes; acknowledging only floor publication would allow undeleted peer storage to accumulate.

Before a peer floor cut the peer retains old receipts. After it, every recovery state enforces the floor even if deletion was interrupted. Peer persistence cuts and recovery are new obligations: the current peer transition models atomic effect/receipt publication and has no independent crash/reset implementation. The bounded variant must preserve that effect premise while adding retirement durability.

### C: indefinite finite identities under a closed transport target

A conditional target can own both endpoints, every producer, request/reply/control queue, callback and caller admission path. A persistent reset controller closes ingress, stops producers, finishes or explicitly preserves unresolved requests, purges every old actionable message, retires released terminal state, establishes durable reset completion, and reopens. Crash during closure leaves admission closed until authoritative recovery completes. Reuse is allowed only after this barrier.

Reset requests and acknowledgements need the same protection as business messages. Reading an old reset-complete reply through a replayable finite-tag channel cannot establish current completion. Authoritative phase inspection must occur within the controller or through a separately justified fresh access path, whose storage belongs in the bound. Detached clients holding raw bytes outside the revocation domain invalidate this target. An affine API helps only for resources actually governed by its ownership discipline; [RetentionOwnership](../../Applications/Durability/RetentionOwnership.lean)'s proof-side connection/scope names are not an implementation of distributed revocation.

No inspected implementation supplies this target. An atomic reset primitive would place these obligations in the target specification; it would not prove an ordinary asynchronous network algorithm. C therefore remains conditional and unavailable for adoption without a named realization. Finite wrapped epochs, silence and elapsed time do not fill this gap.

## Wasm execution boundary

The [Wasm capability assessment](wasm-capabilities.md#delivered-work-and-existing-plans) leaves durable peer realization open in #581. It supplies no concrete realization of C. Worker termination, Wasm isolation, component resource ownership and asynchronous cancellation do not revoke external or client-held messages, including stale retirement/reset controls. The current Node artifact path has no host imports or durability and creates a worker for each invocation.

A bounded custom host API in Node or Wasmtime could expose admission, query and retirement operations for A or B with fixed buffers. This is a proposed execution adapter. Atomic effect/receipt publication, persistence of the rejection floor and deletion-complete acknowledgement still require the durable host/storage contract owned by [#581](https://github.com/VladimirMarko/conaled/issues/581). Async stream facilities do not establish those guarantees. A future adapter should make their evidence and refusal outcomes explicit.

## Parameterized storage inventory and construction obligations

The following bounds describe proposed finite representations. Their capacities are parameters to be fixed by the selected implementation's allocation schedule, not measured constants or bounds already proved for the current Lean lists. The inventory makes missing buffers visible without choosing an unsupported number of full-history copies or network queues.

Fix K≥1, J≥1 and 1≤W≤K. Let b=max(1,ceil(log2(K+1))) and a=max(1,ceil(log2(J+1))). Request IDs occupy b bits with values below K; next-ID and both retirement floors may equal K. Journal addresses are below J and the allocation high-water mark may equal J, using a bits. The fixed incarnation has a separately chosen width e; it never increments within the lifetime. For a capacity n, write width(n)=max(1,ceil(log2(n+1))) for a length/cursor field. Pool capacity U=W+2 uses its own width(U), including when K is small. Reject malformed/out-of-range fields before unbounded decoding or allocation.

Write Rbits and Fbits for upper bounds on one request and valid frame; F remains the peer retirement floor. The inspected `requestBits` and `frameBits` definitions in [Costs](../../Applications/FRP/PendingCrash/Costs.lean) give conservative Rbits=2b+13 and Fbits=5b+32 when every request/receipt/counter name fits b bits. These are bounds for those particular flattened formulas. A new binary codec must establish its own corresponding bounds, including framing. Let Cbits bound a journal cell including address, predecessor, record key and tags; Obits bound a retained outcome/reservation; Mbits(k) bound a message of kind k, including control fields. Let Pbits and Tbits bound one complete local and peer snapshot. For B their required payloads include:

- Pbits: one current frame, U reserved outcome entries, local expiry L, pending retirement target/status, pool occupancy/index metadata and current ownership/control fields.
- Tbits: U peer entries, floor F, pending deletion/acknowledgement state and pool occupancy/index metadata.

Those requirements yield explicit inequalities such as Pbits ≥ Fbits + U·Obits + localDescriptorBits and Tbits ≥ U·peerEntryBits + peerDescriptorBits. Codec construction fixes these descriptor widths and proves the inequalities sufficient, rather than using an unspecified constant allowance.

For each owned fixed array r define A(r)=capacity(r)·elementBits(r)+descriptorBits(r). Define its full size even if currently empty. Let S_A and S_B be the finite sets of allocated regions in the chosen layout. The proposed whole-storage bounds are BA=Σ(r∈S_A) A(r) and BB=Σ(r∈S_B) A(r), with the following required inventory. Entries named separately may share a physical region only if a transition-level ownership proof establishes that their lifetimes cannot overlap.

| Owned region or finite region family | Required contents and capacity | Operation that needs it |
|---|---|---|
| A durable journal | J cells of Cbits, roots, high-water mark and its persistent update state | Reserve before preparation; append and every crash cut |
| A cached history | At most J records plus cursor/length | Ready-state lookup and frame-history queries |
| A pending-before and pending-after | Each at most J records if materialized separately | Append preparation while old history remains authoritative |
| A recovery accumulation | At most J records/addresses, according to the chosen decoder | Interrupted reconstruction alongside durable journal |
| Local authoritative and inactive banks | Explicit bank count, Pbits each for B; selected-root metadata | Write/persist/selector cuts; inactive old contents still count |
| Local staging, current-frame and output areas | Separate capacities for every concurrently owned payload/frame/output | Replacement construction, ready use and bounded query streaming |
| Peer authoritative, update and recovery areas | Explicit region counts, Tbits per complete B snapshot or capacity K for A entries | Atomic effect/receipt target, floor publication, deletion and restart |
| Copy, validation and failed-preparation scratch | Declared maximum capacities for each concurrent scratch owner | Every internal copy/codec step, including failures before publication |
| Active, prepared and former backend allocations | Capacity for each permitted simultaneous owner plus conversion scratch | Migration preparation, failed validation and delayed cleanup |
| Each endpoint/transport queue and callback buffer | For each actual queue q, Qq·Mbits(q)+descriptorBits(q) | Submission, duplication, response, retirement controls and delivery |
| Parser and response staging | Explicit per-admission/response capacity | Range check and rejection before allocating decoded input |
| Reader, plan and cursor state | Bounded handles/descriptors plus any retained payload copies | Pin, query, reconstruction and suspended operations |
| Configuration and controller state | Encoded K/J/W/incarnation, flags, counters and durable update copies | Admission, exhaustion, restart and cleanup |

This is an explicit parametric sum over an enumerated layout, not permission to omit a row. The constructor must supply each capacity, element/descriptor width, region multiplicity and overlap decision. For example, copying a list while retaining its source requires both source and destination plus any actual temporary prefix. A streaming implementation may reduce that scratch requirement only with an operation schedule establishing the reduction. Likewise, the number of queues comes from the selected transport graph; it is not inferred from the two local slots.

For B, reserving a shared outcome entry at admission proves the proposed logical entry-count invariant: live plus released-but-unexpired local occurrences ≤ U, and retained peer identities ≤ U. Retirement freezes admission until deletion completion, so expired-but-not-yet-deleted peer entries coexist only with the same pre-retirement set, not an accumulating new backlog. Two durable banks and staging can hold copies of those U entries; each copy is separately charged through its region in S_B. This count argument does not establish codec sizes or the scratch/ownership bound.

The future uniform claim is: for each admitted configuration and fully specified region layout, every reachable state and internal operation cut under every admissible finite command/crash/replay prefix fits the same BA or BB. Its proof requires transition-level allocation/ownership maps for all rows, crash-safe metadata, pool reservation preservation, rejection before overflow, and bounded query streaming. Cumulative work can grow; retained execution logs cannot grow unless they are explicitly outside the implementation and streamed as observations. Failed work remains part of the executed-event cost model.

For C, a conditional bound has the same sum plus every reset-controller region and additional ingress/revocation buffer. All positions become fixed scoped indices, with no hidden epoch or consumed-token set. This conditional inventory is not a controller construction: no complete replay-owning target or its region map has been identified.

The current [Costs](../../Applications/FRP/PendingCrash/Costs.lean) model measures flattened list encodings and explicitly charges external messages, history copies and growing name widths. The paper inventory above proposes a route to uniform bounds; it does not claim the existing runtime already satisfies them. Physical byte encoding, allocator peaks, filesystem ordering and network conformance require separate target evidence. An unlimited stored business-output archive cannot be omitted from a total-deployment storage claim.

## Worked B layout with a fixed peak bound

Here is one conditional construction for B, not a selected implementation. It uses a serial controller, fixed arrays, and only the current Boolean delay/redundant-pair backends. Admission may return busy while a reader, update, recovery or migration holds the controller. The transport has exactly four queues: local outbound, peer ingress, peer outbound and local ingress. Each holds Q≥1 packets; duplication consumes an ordinary queue slot and is refused or dropped when full. No hidden transport backlog or retained execution log is permitted within this target. Outputs are streamed observations, not a stored business archive.

Use the widths above, u=width(U), q=width(Q), and the following padded record layouts. Option payloads and unused fields are zeroed; validation rejects invalid tags, lengths and names.

| Record | Fixed fields | Bits |
|---|---|---|
| Current frame | Kind and logical bit; next ID; two-bit order length and two order bits; two request slots | D=5b+34 |
| Request slot, included in D | Present, ID, input, output-present/output, receipt-present/ID/three-bit answer/input/output, three-bit phase, route-open | 2b+14 |
| Outcome entry | Occupied, ID, input, output, two-bit status (reserved/published/prevented), released | O=b+6 |
| Local snapshot | Frame, U outcomes, incarnation, L, pending target, pool length, pending and cleanup-complete bits | P=D+U·O+e+2b+u+2 |
| Peer snapshot | U entries using the outcome format, incarnation, F, pending target, pool length, pending and cleanup-complete bits | T=U·O+e+2b+u+2 |
| Packet | Incarnation, optional frame-sized payload, two names, four-bit opcode, four-bit answer/status, input/output, six presence/control bits | M=e+D+2b+16 |

The frame header takes b+6 bits. The two request slots account for the remaining 4b+28. The packet can carry one current frame, one outcome, or a retirement request/reply. A query returns one record at a time; it never materializes a pool or history response. The two persistent cleanup flags distinguish unpublished work, a pending target and deletion completion. A deletion scan restarts from zero after a crash, so its cursor need not be persistent. This representation replaces full journal history under B's changed observation contract; it does not encode the old journal in a smaller space.

Each endpoint gets two persistent snapshot banks, one staging snapshot and one recovery snapshot. All four copies count even when inactive or stale. Three shared M-bit buffers hold input decoding, the current dispatched command and the response. Four three-bit backend slots hold active, prepared, former and conversion-scratch values: one kind bit and two Boolean payload bits per slot. The controller prevents a second migration while a former owner remains.

For an explicit descriptor budget, let v=width(max(P,T,M,U,Q)). Four queues use head, tail and length fields, totaling 12q bits. Eight v-bit registers hold source offset, destination offset, validation offset, pool scan, recovery offset, deletion scan, reader position and remaining copy length. Configuration stores K, W, Q and incarnation, taking 2b+q+e bits. A 26-bit control record comprises a four-bit phase, four-bit opcode, three-bit selected-region code, two bank-pin bits, busy bit, four backend-occupancy bits, two durable bank-selector bits, two temporary Boolean bits, three packet-valid bits and admission-closed bit. The phase vocabulary is idle, decode, scan, copy, validate, mutate, persist, publish, effect, enqueue, query, retire, reclaim, convert, recover and cleanup. Region codes select among the eight snapshot regions; packet and backend slots have fixed roles. Iteration uses these registers rather than a recursive stack or stored list of work events. Layout offsets are fixed by the configuration.

Thus the proposed abstract bit bound, charging all allocated regions at every cut, is

```
C = 12q + 8v + (2b + q + e) + 26
Bworked = 4P + 4T + 4Q·M + 3M + 12 + C.
```

The following schedule explains how those regions suffice, including overlaps:

| Operation | Allocation and publication schedule |
|---|---|
| Update | Pin the selected bank, copy into staging, mutate and validate there, then copy to the inactive bank. Persist it before atomically selecting it. The old bank remains charged. Unpin before the next overwrite; failure discards staging without allocating another copy. |
| Retirement | Publish L and its pending target in the local banks before sending. The peer first publishes F with old entries still present, then scans/deletes covered entries in staging and publishes a deletion-complete snapshot. At most U entries occur in each copy. Admission remains frozen until the exact-target completion reply arrives; lost replies reuse the same buffers and target. |
| Recovery | Read only the selected bank into the recovery region, validate it with bounded scans, and reconstruct the backend slots. Unselected banks and interrupted staging remain counted but are not authoritative. Crash discards volatile operation state; restart reuses the same regions. A pending retirement restarts its scan or reconciliation without a new identity or allocation. |
| Migration | Keep active and prepared backends simultaneously, with the conversion slot available for validation/copying. Publish the new kind and logical state through the ordinary snapshot schedule. Hold the old backend in the former slot until cleanup; failed preparation retains the original active owner and clears the other slots. Recovery reconstructs from the selected frame. |
| Query and traffic | Pin one selected bank during a bounded read, copy one result into the response buffer, then unpin. The bounded queues own all delayed packets. Transfer may copy while the source remains occupied, since both slots are charged. A full destination causes backpressure or loss with retry, never an extra queue. |

This schedule admits ordinary successful runs: with empty queues and no crash, admit a request, reserve/publish at the peer, reconcile its receipt, commit/release, retire the released prefix and admit again until K is exhausted. It also has room for the lost-retirement-reply recovery trace. Busy, queue loss and an unresolved prefix can prevent progress; the construction claims no progress under arbitrary refusal, replay or crashes.

The paper bound depends on a target with atomic durable bank selectors, persistence ordering, and atomic peer effect plus receipt publication. Peer effect publication must select the corresponding durable receipt snapshot in the same target transaction; a separate effect followed by selector update would be unsound. Selected banks cannot be overwritten while pinned. Admission validates within the fixed packet buffers, all entry mutations preserve the U reservation bound, and serialization/recovery use the displayed bounded workspace. These are implementation and refinement obligations, not properties supplied by ordinary files or Wasm. A physical target must additionally declare a finite H-bit maximum for its code, allocator metadata, transaction machinery, device buffers and other owned storage, yielding Bworked+H; unbounded transaction logs do not meet this target. Byte padding must also be charged there or in a revised byte layout. The construction supplies a feasible symbolic layout and overlap schedule; its codec, transition proof and physical realization remain future work after policy selection.

## Positive and separating traces

The following additions are paper fixtures to formalize after policy selection. Existing [PendingCrashRecovery examples](../../Examples/PendingCrashRecovery.lean) remain preservation targets.

1. **Successful A recovery:** accept, durably compute, peer publishes once, lose reply, crash, recover, query the same identity, confirm and commit. Exhaust later fresh admission and still query the accepted history. Separately exhaust J through interrupted preparation while work is unresolved; report stopped/unresolved without denying a possible peer effect.
2. **Successful B retirement:** complete and release i; publish L=i+1 with pending target; peer publishes its floor, deletes i and loses the reply; local crash/recovery retries the same retirement; completion resumes admission. Queries below L are expired from the local publication onward. Test each local-bank and peer-floor/deletion cut, and duplicate retirement requests/acks.
3. **Unresolved prefix:** lower i remains computed with a selected output while i+1 is cancelled. Refuse retirement past i and refuse admission when the bounded pool fills. Retain the selected output through restart.
4. **Premature deletion:** reserve(i,x), publish(i,x,y), delete i without a floor, then replay reserve(i,x) and publish(i,x,y). The second publication emits y again. Replaying publish alone would return absent in the present peer. Also delete a prevented receipt and replay reserve/publish, violating prevention.
5. **Finite reuse ambiguity:** reuse i with equal input/output; an old published reply can falsely confirm the new computed occurrence before its peer effect. An old prevented reply can falsely cancel it. Wrap a generation and repeat; include a stale retirement command or acknowledgement against newly opened work.
6. **Conditional C cycle:** finish pending work, close admission durably, purge all inventoried traffic, reset terminal state, complete authoritative control agreement and reopen. Crash at every cut and repeat until finite tags recur. An old message retained outside the purge domain separates a real barrier from a local drain.
7. **Resource stress:** duplicate traffic without new admissions; repeat failed copies, migrations, queries and crashes. Refuse at capacity and preserve charged old/new copies. No successful whole-operation state bound may hide an overflowing intermediate allocation.

## Why a policy choice is necessary

A uniform finite-bit bound on all query-support state cannot preserve arbitrarily many independently variable full histories with later distinguishing queries. With n independent Boolean choices there are 2^n histories; for n greater than a B-bit state budget, some histories share state but require different answers. This paper argument assumes no caller-supplied historical evidence or excluded archive. It does not exclude finite lifetime, exact finite summaries or disclosed expiry.

Finite tags with unrestricted replay also cannot distinguish stale and new byte-identical calls at an indistinguishable admission boundary when the new call must sometimes execute and the stale one must not. Permanent refusal is safe; a genuine revocation target changes the replay premise. This is not an impossibility claim about every finite-state service.

## Direct realization and native reuse

A direct bounded adapter can retain the frame transitions and independent delay source while replacing history storage. B needs an inductive retained-state/provenance relation linking current state, live selections, retained outcomes and peer floors. A well-typed current frame cannot establish the predecessor history that was discarded.

The existing bank payload and primitives specialize to Boolean items, position and parity. A protocol-specific paired-bank adapter is therefore a useful baseline against a narrow payload-copy generalization. Compare both on the same lost-reply, retirement and crash-cut cases. Require the generalized version to recover the existing Boolean bank laws and instantiate the pending-frame consumer, including safe overwrite, bounded reconstruction and reader/plan ownership. Encoding a frame as unrelated Boolean appends would need framing and an atomic frame boundary. Remote retirement remains a separate proof in either design. No shared interface is adopted merely because both use two banks.

The decision ready for the user is: preserve full historical observations and accept finite-resource exhaustion (A); authorize explicit historical expiry within a finite lifetime (B); or pursue a named closed transport target before attempting indefinite finite-identity reuse (C). Caller-driven relinquishment is another possible expiry policy if automatic window loss is unsuitable, but it still needs backpressure and retirement. The next implementation requires that policy decision, reviewed transition/observation contract, checked positive and rejecting traces, exact build/audit and independent Standards/Spec review. This first-stage study does not authorize weakening #540.
