# Independent finite-prefix observation contract

Issue #467, frozen before implementation against accepted `0dbe057b`.

Inputs are finite globally ordered tagged wire events for the existing two-slot
Boolean response-policy family. Each slot starts at the existing idle wire
stage. Admitted inputs are exactly the existing `InteractionPlay` traces,
including repeated use of a slot after delivery and every intermediate
propagation phase. A malformed event or wrong policy response is rejected.

A detailed diagnostic contains each slot's final propagation stage, including
the buffered value already represented by that stage, and the complete ordered
wire history. The observer executes the existing local `wireStep`; it must not
introduce a second copy of its transition rules. Success must be equivalent to
admission, and the recorded stages must be the unique endpoints of the actual
projected paths.

The external observation is the original native client observation of the
client-visible history: A asks and A replies, with slots and order retained.
It includes pending/answered states and result. B events are hidden; C service
events remain visible at the relay boundary but are hidden at the client
boundary. On admitted prefixes, this external projection must be accepted,
including before requests or responses have propagated. Finite replay uses
the existing native transition function and does not assert that stage alone
reconstructs external state.

Step compatibility must connect actual internal transition paths to native
client execution. A visible A event performs the corresponding native step.
Other events stutter at the client boundary while internal stages can change.
The lifted statement covers arbitrary finite admitted histories, not only
caller-generated blocks. At the old caller schedule boundaries it must recover
#463's unchanged complete observation theorem.

A detailed history ending at idle can retain an answered client value, while
an initially idle history retains an idle client. Conversely, `aAsk` and
`aAsk,bAsk` have identical hidden histories but distinct internal stages.
Non-recoverability must use the existing hiding function unchanged.

The existing middle-only value flip must preserve external observations and
stage endpoints, while changing the recorded middle-value history; two flips
must recover the original detailed observation. Proofs must use the same
shared interaction witness and the actual path interpretation. Finite delivery
examples must explicitly supply the remaining events. No runtime, scheduling,
fairness, durability, infinite progress or universal game framework is added.
