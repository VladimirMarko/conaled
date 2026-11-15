# Stage05: actual absorbing sizes and exact residual-work tails

Candidate `331178cac124394fd5c86da0877fa670463f3280`, tree `3476e8d1834c3f6c541cbee12352d47d4e9b5aeb`, parent `cd20a36f52b4ddd95be3cb9d85c0b95368ef1248`.
Branch `work/fdsa-ch03-random-selection`; clean worktree.
Commit `feat(selection): derive actual residual work tails (#174)`.
The two new files and all proposed results are **uncompiled**. All ten assignment
sources and own provenance writes are now held for root's actual terminal or
explicit release. No proof or acceptance credit is inferred from this handoff.

## Preserved checked base and recovery

Root drift attempt4 at the parent closed0: owned52024, terminal `18ce07`, complete
root closure `adf424`. The entire log/closure/terminal were read in `f9fb72`.
Outer9,730 bytes SHA-256
`7692228411f3e0cdd61031bf1168cedcd41f44938c553c3cbfd51fdb162850ac`;
native9,446 bytes SHA-256
`d4d54c34dcdaabe2a415e6cf51fdea8a7786c63942504c80205f8052118b5e80`.
All eight preceding sources,139 public names and15 authored private helpers
remain byte-identical. All131 earlier author records and14 passing-focus records
retain their hashes. Earlier failed and interrupted histories remain unchanged;
the interrupted second drift attempt still has no secured terminal credit.

The initial3,339-byte trace draft was honestly checkpointed in0129. Its immutable
archive was verified/uploaded/exposed and released at21:20:31, SHA-256
`877c6bf0d8eb0c21c77a91d6f23942879d9ab69a3afafabc105759a7f08083e3`.
The full durability/release records were read in `9ef8ec`; `db3d83` verified the
exact saved draft and all previous sources before authorized continuation. The
historical draft hold is retained; it is not treated as the current file hash.

## Proposed mathematics and exact domains

The new core observes the already checked run trace. `activeSize j trace` is its
j-th actual recorded length, zero after the finite trace; `residualWork w trace`
is exactly `scanVolume (trace.drop w)`. There is no second random execution,
independence premise or larger-side process substituted for actual selected work.

1. Pure trace lemmas express scan volume as the finite sum of active sizes and
   prove exact take/drop decomposition. The existing actual support contracts
   give X0=n, positive entries bounded by initial n, zero exactly after the final
   active call, persistent zero, and absorption by at most n active calls.
2. `sizeExpectation` and `residualExpectation` are weighted observations of the
   original `run`. Exact successor equations follow `workExpectation_cons` and
   the actual `prepend`: the selected strict child remains, the equal branch is
   already absorbed. Time induction with the checked conditional drift proves
   E[Xj]<=q^j*n and E[Rw]<=4*q^w*n, q=3/4. The residual base is the checked4n
   expectation of the same execution. No desired bound is supplied as a premise.
3. Prefix work<=w*n and the exact decomposition give
   W>=(4+w)*n implies Rw>=4*n, on supported outcomes. Residual work is nonnegative
   and dominated by actual scan volume. Its Nat marginal has finite bounded
   support; its standard lower integral equals the weighted observation and its
   real observation is integrable. The private integral bridge uses standard PMF
   map/singleton/ENNReal-tsum laws and adds no payload measurability assumption.
4. Pinned standard non-strict Markov on that Nat marginal, with positive finite
   threshold4n, gives the exact natural-w inequality
   Pr[W>=(4+w)*n]<=(3/4)^w for n>0. Event inclusion is transported through the
   existing PMF map and support-aware outer-measure APIs on the same run.
5. The unchanged pathwise T<=9W+2 bridge gives the exact source event inclusion
   at9*((4+w)*n)+2 and the same tail upper bound. Source calls retain their
   declared tariff, including the invalid worker empty-call offset.
6. The empty scan law is actually pure0; at its proportional zero threshold the
   >= event has probability1 for everyw. The explicitw1 theorem refutes omission
   of n>0. The event is not changed to > and no real-w extension is claimed.

Worker ranks remain zero-based and arbitrary, including the checked invalid
extension. Valid-rank clients obtain positive length and RankedAt correctness
from the unchanged contracts. There is no Nodup, input-distribution, finite or
inhabited payload assumption. For fixedw the probability upper bound is fixed;
no probability-to-one claim as n grows is made. The natural-w proof is original;
unread Karp1994 wording is not quoted or claimed reconstructed.

## Cases and exhaustive inventory

Expected cases were saved before source creation in `starting-state.json`.
The new examples consume the actual run and new general theorems:

- The finite trace[5,1] decomposes as total6, residuals6/1/0, with later absorption.
- The two supported [0,1] rank0 traces[2] and[2,1] give X1/R1 values0 and1.
  Exact expectation calculations yield X0/X1/X2=2,1/2,0 and R0/R1/R2=5/2,1/2,0.
- Valid and invalid singletons absorb after one active call, retaining source
  means9 and11 and the valid scan expectation1.
- Duplicate [x,x] rank1 keeps both occurrence draws yet has residual law pure0
  and both expectations0 after the first active invocation, for every later time.
- Generic cases connect absorption, integrability and both geometric bounds;
  valid returned answers are combined with the exact scan/source tails.
- Naturalw0 retains threshold4n and upper1. The empty case explicitly refutes
  the positive-domain conclusion atw1.

New scope:52 core public names,18 example public names, one private integral
helper. Cumulative assignment inventory: **209 public targets,16 authored private
helpers across ten files**. These are authored-source counts, not kernel audit
counts or completed obligations. Every new header, source context, claim group,
case and retained source identity is in `precommit-assessment.json`. The final
complete core was read in `0bd52d`, examples in `dfb314`.

## Root-only focused validation and full statement input

```text
lake build Applications.Resources.RandomSelectionTail Examples.RandomSelectionTail
```

`Statements209-stage05.lean` retains all139 previous names in exact order and
appends all70 new public names, with complete explicit-@ printing. Input11,862
bytes, SHA-256 `5f3c2af90ccbd65dcdb7e91a555d5cbb2ae2a4579eaf2b9c3fd05f5c44c3c3df`.
Its preparation binds the exact candidate/tree and all ten source blobs. It is
prepared only; no actual type output exists for this stage.

Source/evidence preservation and exhaustive inventory preparation exited0 in
`eb6285`. Staging, staged whitespace check and commit exited0 in `811c8d`; the
staged diff exactly matched the captured707-line new-file diff. The two
no-index diff exits1 are recorded as expected differences, not build failures.
No author compiler, runtime/cache/output/profile/dependency action occurred.
The fixed task review base remains
`2da5708478a1d943a9214b5b386ec2db16cd9eca`.

## Remaining scope and hold

This proposes C03-069--072 and the tail part of075, with the required absorbing
observations and C076 quantifier review/C077 cases. No obligation is accepted by
the author. Endpoint path probability1/n!, distinct-valid-input triangular
attainment, unbounded quadratic families, general all-equal behavior and source
worst-case transports remain required for subsequent work. C078--080 source
ownership remains root/values. All83 Chapter3 obligations remain the enclosing
scope. Full candidate check/audit, both independent review axes and immediate
candidate verification are mandatory root-owned gates. All writes are HELD.
