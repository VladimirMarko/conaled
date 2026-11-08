# Held-out task: dependent selected positions

The independent `Examples.DependentOperationTrialSpec` defines the required
mathematics. A position in a nonempty array is `Position n = Fin(n+1)`; preserve
the selected position, not merely the bound or existence of a position.
This task is disclosed only after the protocol/interface freeze passes review.
No new-operation solution is included in the public fixtures.

Extend the prepared operations with:

- clockwise rotation: `(i+1) mod (n+1)`, preserving n;
- halving: `i/2`, preserving n;
- compression: `i/2`, changing the output index to `n/2`.

The new operations must be admitted locally in the source signature. Retain
old reflection, insertion, symmetric padding and reset. Compression is a
noninvertible dependent operation; a representation requiring every operation
to be an equivalence would not satisfy this specification.

For arbitrary typed terms, including variables and arbitrary compositions,
connect source typing, selected meaning, actual compilation, two-stage typed
substitution and emitted-code quotation. Use the existing intrinsically indexed
term type or construct and justify an alternative with the same outcomes. An
unrelated `True` predicate or host result computation does not replace source
typing. A bounded frontend is sufficient; no full reference-calculus model or
Agda translation is required.

Provide actual instruction data and executors. Runtime instructions must not
contain source derivation trees, correctness proofs, calls to the independent
Spec functions, or a precomputed answer. Compilation may use two passes, or
extend the prepared typed lowering and macro-to-word emission; connect the
passes by a theorem about the exact produced instruction word. A phase rename
without an actual executable quotation is insufficient. Preserve padding's
existing expansion into distinct left/right instructions. General laws may
make that task cheap; do not manufacture work when a reusable result applies.

## Checkpoints

**A:** Admit rotation. Prove selected execution for all terms in the admitted
fragment on the total/position machine. Include the empty/variable case and
wraparound at the last position. Construct `stageOne` as an actual source term;
its emitted result at input3 has total bound4 and selected position4. Preserve
exact quotation and typing. Record local versus whole-term obligations.

**B:** Admit halving and add the distance-coordinate executor for the admitted
operations. It stores `(left,right)`, meaning the selected index is left and
bound is left+right. Implement its operations independently rather than calling
the first executor or decoding to Fin before using source semantics. Prove
universal preservation on both machines and quote the four-step `stageTwo`:
rotation, halving, rotation, halving at bound5/input4 returns position1.
Disprove a concrete commuting equation between rotation and halving and explain
why their separate local correctness laws do not establish that interaction.

**C:** Admit compression and a third executor using two unary lists of Unit.
Its semantic encoding is `(replicate i (), replicate (n-i) ())`. Lists, lengths,
concatenation, truncation and replication may be used in its algorithms; do not
call either earlier executor or the source interpreter. Prove the selected
full-list result, not only equality of lengths. Preserve all three realizations
for arbitrary terms and the old operation cases.

Construct the nine-step `stageThree` source term in the independent Spec:
rotation; halving; insertion; compression; reflection; padding; rotation;
reflection; insertion. At bound8/input6 it yields bound7/position3. Apply actual
typed context substitutions replacing every variable by its reflection, then
every variable in that expression by reset-to-zero. The same term yields
bound7/position2, then bound7/position1. Prove the general two-substitution
connection for arbitrary typed substitutions, not only these evaluations.
Retain the dependent tail `(i : Position n) × Fin(i.val+1)` with chosen last
member. Show interpretation/compilation preserve that selected tail. Reject the
same-bound wrong final position0. Recover the prepared selector result and keep
its failed interchange control; old native/shared schedule modules remain
regressions in the integration build, not new author tasks.

**Repair:** Change rotation to `Spec.backward` in all source/target contracts
and update the required comparisons and selected cases. Preserve snapshots of
the old statements. Recompute the independent fixed client oracles under that
change and connect them through your general results; do not keep false old
expected values. Count changed local, global, quotation, substitution and
interaction declarations. A representation change is allowed but its cost counts.

## Delivery

At each checkpoint submit one exact cumulative Lean file and an activity record
with stage, timestamps, attempts, available resources, assistance and unfinished
obligations. Use the protocol's unchanged wrapper, fresh filenames and limits.
Native authors may generalize reusable native helpers; shared authors may
instantiate local laws. Neither is required to follow a prepared proof style.
Explain which obligations remain per operation, per backend and per interaction,
and which universal results were reused. Incorrect or unfinished work remains
part of the experiment; do not conceal it or claim a mathematical obstruction
from authoring difficulty.
