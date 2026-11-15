# Mathematical development and repository workflow

Use the actual source checkout's `AGENTS.md` and its referenced instructions.
The user's current exceptions keep issue/spec tracking local and make Nix
optional while preserving pinned inputs. [RESUME.md](RESUME.md) owns the
authorized compatible native route; this does not waive the actual checkout's
snapshot, review, build or audit requirements.
`reference/conaled/` is an immutable a887a8d9 guidance snapshot for orientation;
it has not replaced the original source base. Recheck guidance when a later
integration pin is selected. This archive cleanup performed no code integration.

## Preserve and review the complete intended scope

Follow `.agents/skills/implement/SKILL.md` or the appropriate enclosing workflow;
do not launch nested implementation/review hierarchies when already assigned a
role. Record full user/spec requirements, stable base/candidate identities and
existing staged/unstaged/untracked work before changes. Use the checkout's
`review_snapshot.py` procedure and stable isolated candidates. A ticket's
incorporated base may change as that procedure allows; the full-spec integration
review retains its original starting base and all unresolved findings.

Keep operations, equivalence, laws, representations, observations, resource
models and target capabilities distinct. Reuse current owners/Mathlib where
semantics match. Keep native Lean specializations usable; use checked bridges for
representations or settings rather than assuming an interface preserves every
source capability. Read domain guidance, GLOSSARY and applicable ADRs first.

For each new or changed formal claim, use example-driven development and statement
review: actual elaborated domains/hypotheses/quantifier order; useful witnesses,
partiality, equality and occurrence order; nonvacuous independent expectations;
checked consumers that use the public result. Retain discriminating boundary and
counterexamples. Paper designs need these scope checks too. Failed elaboration is
not itself a mathematical impossibility proof.

Independent Standards and Spec review must both cover the same full candidate
and requirements, with stable finding IDs and applicable validation. Carry prior
findings and failures through corrections. Missing evidence means Blocked, not
Passed. Reuse matching evidence only under the repository's documented identity
conditions. Optional originator review does not replace either axis.

## Applicable formal validation

Use the checkout's commands through a compatible environment authorized in
RESUME. Its current README owns triggers:

```sh
./check.sh --candidate HEAD
./check.sh --verify-candidate HEAD
```

Run in a clean isolated committed candidate, preserving the successful verification
record and complete terminal evidence. Perform immediate verify-candidate before
acceptance and compare the accepted content with the reviewed snapshot. A failure,
unknown terminal, stale record or new conflict resolution leaves gates pending.

Routine acceptance uses the guarded incremental build and exhaustive audit.
Add `--fresh` when required by tooling/toolchain/dependency changes, suspected stale
artifacts or the current README's other triggers; do not mechanically demand a
fresh rebuild merely because a workspace was restored. Focused builds and setup
smokes do not replace integrated coverage/audit. Only propext, Classical.choice
and Quot.sound are permitted; admissions, new application axioms and native
execution axiom shortcuts are not proofs. Preserve public-entrypoint coverage.

After applicable acceptance, update only the current STATE and maintained scope
records with exact evidence. Before another extended phase, make the checkpoint
durable under DURABILITY and CHECKPOINTS. Incomplete work is checkpointable without
being accepted. Do not publish to GitHub outside the user's authorized scope.
