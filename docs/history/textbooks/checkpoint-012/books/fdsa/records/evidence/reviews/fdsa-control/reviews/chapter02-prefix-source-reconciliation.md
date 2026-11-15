# First Chapter 2 foundation prefix: exact source reconciliation

Recorded 2026-11-02. **Preparation only; integration unexecuted; all inherited
sources remain unaccepted.** This is a source reconciliation of three fixed
saved commits, not a new requirement, implementation candidate, compiler result,
or independent final review.

The corrected Chapter 1 candidate must first satisfy its existing complete
acceptance requirements. This report neither activates Chapter 2 nor permits
integrating shared drafts before that prerequisite. Root's Chapter 1 attempt 3
remains the sole authorized compiler/checker; this investigation did not inspect,
interrupt, restart, or reuse its running build.

## 1. Exact inputs and original scope

| Role | Exact commit | Verified immediate parent |
| --- | --- | --- |
| B — common base | `1aabd512284fe86254278ac631eda061d311050b` | `7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd` |
| R — corrected Chapter 1 candidate | `07e480f6ec9958d4975bb90151005b84f2907614` | `503081dccdbe64188eceb6524724fc445c840d68` |
| P — unchanged initial Chapter 2 foundation prefix | `c80eec92f5458eccfd1c34c8314d666c2a1e3847` | `50dc7df3649d9f4f33bc6b3464c2c9fb6399aa46` |

The actual `git merge-base R P` is B. R and P are divergent descendants of B;
neither side contains the other. The original Chapter 1 review base remains
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`, not B.

The complete retained `reviews/shared-integration-preflight.md` and the original
component scopes were read before the source comparison. They remain unchanged.
The exact records governing this preparation are:

| Control record, relative to `fdsa-control/` | SHA-256 |
| --- | --- |
| `reviews/shared-integration-preflight.md` | `e1d9c119e2bca35bbbd283eb47d05330f35d7e548f92e063eeebe7d4d53552eb` |
| `reviews/chapter01-requirements.md` | `7b7ce18bcfe9bb888ac9e99810a1095a823f9a67dbb54717c5bf673017a890ba` |
| `reviews/chapter01-cost-model-requirements.md` | `1b88c327e465db8d1575d0af086e0b954fb0a21b393f145ae89f630d361914a1` |
| `reviews/insertion-requirements.md` | `fbd77fa19c83df3e6d7d10d6e7bd6cddf2d5aa888b512d5af2a7322f222f1a68` |
| `reviews/list-library-requirements.md` | `83cffa5aff717943d449f4380189a9e9a761252730f5a14f4e392f1e62d154d4` |
| `reviews/list-calls-requirements.md` | `0a2f7a2869c10276da2cc9a852e20936c6aba2d094d5232b96e94fbf47ecf78d` |
| `reviews/notation-requirements.md` | `21a4ad13752d4316817e97f655af9a768726aa682124a39a2aeac248460b5a48` |
| `reviews/chapter02-requirements.md` | `f0c9bc939fbfb6da02c1734b121456c35fd6b4c9ee43f1284003d0b8db087a36` |
| `research/scope-reconciliation.md` | `21de30d9c317dadc2cb8aee51ea84ca26f74c8208b754feea57d81140c1a3e87` |
| Current `research/chapter02-obligations.md` | `a689f01dbf1ed93b20962276735cfc5fe7701dfb7a93232cbe26e7e4c70095b2` |

The frozen Chapter 2 requirements retain their original 107-row snapshot. The
recorded scope reconciliation retains every original row and appends
C02-108–112, so the current inventory has **112 obligations**. P supplies the
already-scoped insertion/list/notation foundations; it does not purport to
implement all those sorting obligations. The builder, natural-run, randomized,
merge and other remaining obligations are not removed by choosing this prefix.

### Preserved branch histories

R retains the entire Chapter 1 cost-model repair and all four subsequent
compiler-driven correction commits:

```text
B
  a14977b9e316cc484ffad8a470d26b15615956c0  call comparisons and shared demand
  057e07cd0bd16c7877967aedc46aeefaca01a7a6  cost-proof elaboration corrections
  94d9af50df283dee3a314025a8c24859445b5793  cached catalogue reduction
  503081dccdbe64188eceb6524724fc445c840d68  call-model proof simplification
  07e480f6ec9958d4975bb90151005b84f2907614  redundant cache-example term removal
```

P is exactly the prefix already selected in the original integration plan:

```text
B
  697bcf242ce65d74815b5639bddb1c6e754dd10f  insertion costs
  333f900d04be3153518e68cc8c10920f40a08e05  Appendix A list interfaces
  df116c2f6d834eeb952157505b5c93a9ab5497e8  Appendix B.1 list calls
  c994c22b754db5300d28670dff6b6f83ad56df02  Appendix C notation
  50dc7df3649d9f4f33bc6b3464c2c9fb6399aa46  notation dependency/type corrections
  c80eec92f5458eccfd1c34c8314d666c2a1e3847  empty-index notation boundary
```

These are parent-chain lists, not new acceptance sequences. In particular,
`c28ba71863d2a35ee1c3a089caa90464e4cca692` and its potential-accounting changes
are **outside** the initial prefix. The later affine, builder, probability,
tree, ADT, priority-queue, merge and search drafts also remain outside this
reconciliation. No branch tip or original prefix was changed.

## 2. Read-only method and exact changed-path intersection

Project Git reads ran through the unchanged pinned Nix development shell in
`/workspace/scratch/845aa1048b05/conaled`, with `GIT_OPTIONAL_LOCKS=0`:

```text
/root/.nix-profile/bin/nix --extra-experimental-features 'nix-command flakes' --option build-users-group '' develop --command python3 ...
```

The subprocesses read `show`, `log`, `merge-base`, and
`diff --no-ext-diff --no-textconv`. The explicitly authorized legacy
`git merge-tree --trivial-merge B R P` was used only for its read-only three-tree
text output. It was not the object-writing `--write-tree` mode. Its exit status
was 0 even though its output contained a conflict; conflict markers, not that
exit status, identify the unresolved hunk below. No actual merge, checkout,
index update, tree creation, ref change, source write, or compiler operation
was performed.

B→R changes **7 paths**; B→P changes **9 paths**. Their intersection is exactly:

1. `SquareApplications.lean`;
2. `docs/research/fdsa-reconstruction-map.md`.

The union has 14 changed paths relative to B. The other 12 paths are additions
on exactly one side; there is no add/add collision or source deletion. Neither
delta changes dependency pins, the toolchain, build scripts, checker settings,
or any preexisting resource, sorting or selection module. The preexisting
Chapter 1 definitions already in B are retained through both histories.

| Path group | Required source disposition |
| --- | --- |
| Four C1 Lean additions and the C1 call-model note | Preserve the complete R blobs, including all correction commits. |
| Six foundation Lean additions and the notation map | Preserve the complete P blobs, including both final notation corrections. |
| Public root | Resolve its one concurrent-insertion conflict by the exact import union in §3. |
| Reconstruction map | Preserve the clean automatic text merge, with the semantic readback in §4. |
| All other tracked paths | No reconciliation edit; retain the common inherited content. |

This path analysis identifies textual integration scope. It does not by itself
prove elaboration compatibility, absence of all global simp interactions, or
passing full-candidate verification. The separately assigned source/API
compatibility pass is complementary; it is not a compiler result either.

## 3. The one actual conflict: public imports

At B, `SquareApplications.lean` ends its imports at lines 246–247:

```lean
import Examples.FunctionalBasics
import Examples.ListReversal
```

Both sides insert immediately after B:247. R adds `Examples.CallModels` and
`Examples.SharedDemand`; P adds `Examples.InsertionCosts`, `Examples.ListLibrary`,
`Examples.ListCalls` and `Examples.FunctionalNotation`. The legacy text output
shows precisely these two alternatives between `.our`/`.their` conflict
markers. No other root-import hunk differs.

The proposed resolution preserves all preceding bytes through B:247, then uses
this exact suffix (including the existing public-entrypoint comment):

```lean
import Examples.CallModels
import Examples.SharedDemand
import Examples.InsertionCosts
import Examples.ListLibrary
import Examples.ListCalls
import Examples.FunctionalNotation

/-! Complete public entrypoint. The separate ProofAudit module checks every local proof root. -/

```

Thus the complete final block begins with the unchanged FunctionalBasics and
ListReversal imports and contains all six added example imports once. It keeps
the repaired Chapter 1 public coverage and all four shared foundation example
entrypoints. Selecting only one side would drop an existing scope from public
coverage; importing a later branch's root wholesale would introduce unrelated
drafts. No root reordering outside this block is needed.

### Exact root identities

| Version | Bytes | Lines | SHA-256 |
| --- | ---: | ---: | --- |
| B | 8,236 | 250 | `2d33ca173e9220ec45155b52aa3cdf309872c96bafd05603b12ef0dca7660db6` |
| R | 8,292 | 252 | `b36e3743af5043667735caab1327fda8fc1b6eebc2d7842cdd926b329b2efd68` |
| P | 8,356 | 254 | `6e8bf36ee835ffe8719dccabde5cd1c0cfc3a9832b6131b866d7f25ffa93a7ab` |
| Proposed union, computed in memory only | 8,412 | 256 | `7f00379973161019217585a5ed32d0374247300544ae448b2a4b86aa11c6bf64` |

The last row is a byte-level reconciliation recipe, **not a written source
file, Git object, candidate identity or validation record**.

## 4. Reconstruction map: compatible adjacent edits, with required readback

The earlier shared-integration preflight conservatively called attention to
nearby changes around B:193–206. The exact comparison here refines that warning:
**this file has changes on both sides, but the legacy three-tree text merge has
no conflict markers in it.** It must still be read as a complete combined
scope, because taking an entire side manually would lose substantive content.

### Exact edit locations

Line references in this table refer to the original B file unless another
version is named. The reported replacement intervals are inclusive.

| Side | Exact old position | Content that must survive |
| --- | --- | --- |
| R | Replace B:142 | Change the nonrecursive-inlining row to the qualified entry-omission row, citing `CallCount.tick`, `tick_cost_comparison` and `add_entry_isBigO`, with explicit positivity. |
| R | Replace B:194–200 | Retain the nonprimitive-observation and compiler/runtime/representation boundary, without using it to discard cost-comparison mathematics. |
| R | Replace B:202–205 | Explicitly retain pp.7–9's required fine/coarse comparison, positivity and shared-demand claims, their source note and unvalidated status. |
| P | Replace B:42–43 | Chapters 2 and 3 remain queued and point to shared insertion costs. |
| P | Replace B:68 | Appendix A points to shared standard interfaces/adapters, with acceptance separate. |
| P | Insert after B:206 | Preserve P:207–422: all shared insertion, Appendix A and Appendix B.1 sections. |
| P | Insert after the B:207 architecture heading | Preserve the complete Appendix C notation-map link and correspondence paragraph before the unchanged architecture prose. |

The single blank B:206 remains between the end of the repaired Chapter 1
boundary and the insertion point. P does not replace R's required Chapter 1
paragraphs. The different chapter-status and Appendix A table edits are also
disjoint from R's changes.

### Concrete content-preserving construction

Starting from the **entire R map**:

1. Apply exactly P's two queued-chapter table edits and its Appendix A table
   edit above.
2. Before `## Architecture and statement review`, insert exactly P's section
   text from `## Shared insertion costs for Chapters 2 and 3` through the end
   of `## Shared list call counts — Appendix B.1`, including its boundary
   paragraphs and examples.
3. After the architecture heading, retain exactly P's Appendix C paragraph:

   > Appendix C's complete notation correspondence, source corrections and checked
   > semantic boundaries are recorded in [the notation map](fdsa-notation-map.md).
   > It reuses these list and foundation interfaces rather than introducing source
   > editor syntax as a second notation layer.

4. Keep all remaining R text unchanged. In particular, do not copy P's obsolete
   original Chapter 1 interpretation paragraph back into the combined file.

This construction was compared **in memory** with the entire map diff printed
by the legacy text merge: applying that diff to R yields byte-for-byte the same
proposed map. No reconstructed map was written to the repository or elsewhere.

The important resulting junction is:

```markdown
These source repairs remain subject to compilation, full candidate gates and
independent final review; their presence does not close the chapter. Section
1.5.3's preference for explicit bounds remains explanatory. Higher-order time
conventions refer forward to Appendix B.1 and stay on that appendix's list.

## Shared insertion costs for Chapters 2 and 3

The local cross-cutting ticket FDSA-X002 develops the insertion-sort cost model
used by §2.2, Exercise 2.1 and the small-input sorting case in Chapter 3. Its
development does not accept either chapter or omit their remaining obligations.
```

The preceding R paragraphs retain all three corrected C1 obligations:
finite-catalogue fine/coarse bounds and the actual append connection; entry
omission under pointwise/eventual positivity with both zero boundaries; and
actual shared-demand transitions/value agreement/eager-catalogue work with
external correspondence and unshared duplication explicit. The superseded
claim that the remaining discussion asserted no further algorithm theorem is
absent from the proposed combination.

The new sections retain their own distinctions: insertion observations are
source invocation counts; list optional/proof-domain operations do not invent
payload defaults; map/filter charge actual callback occurrences; optional
lookup failure costs are a named extension; separate take/drop and fused split
have separate observations; and Appendix C's finite/otherwise-neutral set folds
are not replaced by finite-support sums. None of these obligations is accepted
by appearing in the combined document.

### Exact map identities and resulting section positions

| Version | Bytes | Lines | SHA-256 |
| --- | ---: | ---: | --- |
| B | 15,233 | 250 | `ec8a3478e6cd3567768cb9170fd8a11868b1d397afe74668fa5372862f06a993` |
| R | 15,963 | 262 | `3283880ec3b0d55286be1b080c3b58e606577e9a522f21477b8499306c627668` |
| P | 30,817 | 471 | `0a232d0ca909c3c74ee7da1d09527b183c9605d7d540996251083d6b7c39efbd` |
| Proposed clean combination, in memory only | 31,547 | 483 | `5abe715bf852908d8d3f2269be9c94565a516d7fdca8330a6975ed42c4de44e1` |

In the proposed map the qualified entry-omission row remains at line 142;
shared insertion begins at line 219, Appendix A at 283, list calls at 363, and
architecture at 435. The line count is R's 262 plus P's 221 additional lines.
These expected identities cover only the stated content-preserving resolution.
If a later, separately authorized acceptance-status update changes prose, that
must be recorded as its own candidate change; it is not silently folded into
this preparation's byte identities.

## 5. Exact blobs to preserve outside the two shared paths

The following are all one-sided additions. Copying older repair snapshots or a
later shared branch instead of these exact blobs would change the stated
candidate scope. Byte hashes were obtained from the saved Git blobs with
ordinary SHA-256, not from a project hash/checker helper.

| Side and path | Bytes / lines | SHA-256 |
| --- | ---: | --- |
| R: `Applications/Resources/CallComparison.lean` | 5,498 / 123 | `8d6d9324aa9dc71ceeaeaa04073f0f2a4f721a309995f0b623650bb19f01b520` |
| R: `Applications/Resources/SharedDemand.lean` | 12,012 / 251 | `c9740655b7afb51b28b044f1a72006d7a393b74a3e60e2f26464dc7eca7ee996` |
| R: `Examples/CallModels.lean` | 4,188 / 105 | `c1d13360a1229f21bf749d7e7db463eaf9d094089d6c2aa7c92171540e5616ac` |
| R: `Examples/SharedDemand.lean` | 7,844 / 188 | `5b0e374c3d57a9a681d49b9ae0b1bff41a6f60490efadc79cd2d3432b7737fc9` |
| R: `docs/research/fdsa-call-models.md` | 11,832 / 209 | `1f3594a8745f40c3aa9de63469c98886efb035f8d5b1030b9884be241509a0ae` |
| P: `Applications/Resources/InsertionSort.lean` | 7,257 / 178 | `385ea0ba077ac05a10547bc95cd37eb4fa80ef8fe826c6e2c250cca33f2b4aad` |
| P: `Applications/Resources/ListCalls.lean` | 7,970 / 190 | `fba668d88d4c929543a4d5337314761f74f9958cbbd8fc16cf41ca71da5a7e64` |
| P: `Examples/FunctionalNotation.lean` | 8,002 / 193 | `90a6af225009db0ab8b422318a7e7d2746f336f71b1f326c2d150dce0ec76f50` |
| P: `Examples/InsertionCosts.lean` | 3,862 / 101 | `f808254936f1757e639b4f49d94904056b92c84802d9a887a16d31c861c7ff37` |
| P: `Examples/ListCalls.lean` | 4,333 / 124 | `d364a891af384d69683c5df1c4944856e84f2ce6e4104c6e283be552cf27a944` |
| P: `Examples/ListLibrary.lean` | 6,761 / 170 | `036cf4c12ddf5d25ce433d9f7dbedfcbb96dfc3c7f602d10605388d2791e47ad` |
| P: `docs/research/fdsa-notation-map.md` | 24,087 / 313 | `fb34f592ebfb993dee8bdfc1ac0008de3d3b4f83073425da6fed28e23a2cf965` |

The later C1 corrections therefore survive wholesale in their actual R files.
There is no formal-proof conflict to resolve in CallComparison, SharedDemand,
CallModels or SharedDemand's examples. The scope still includes all six P Lean
files and both source maps; no file or Empty/partial-operation case is removed
to reduce future validation work.

## 6. Future application within the existing workflow

This report is not permission to execute the following steps now.

1. Finish and accept the repaired Chapter 1 candidate through its original
   requirements plus the cost-model addendum and matching existing gates. If
   acceptance requires a successor of R, recompute the exact path/hunk comparison
   against that successor; this report does not certify unseen corrections.
2. Preserve both saved histories. Starting from the accepted repair, root may
   form the already-planned isolated foundation candidate by an ordinary
   history-preserving merge of **exact P**, retaining the original refs and all
   existing evidence. There is no need for a separate merge of 697bcf, 333f900,
   df116c or c994c: they are ancestors of P. Do not replace P with c28ba718,
   cherry-pick around original scopes, or reset away the repair history.
3. Use the import union and map readback above. For exact R/P and no separately
   authorized source correction, preserve all 12 one-sided blobs and the two
   proposed combined-file identities. Read the complete resulting diff against
   both parents; retain source limits, cases, public coverage and the full
   original component requirements.
4. Capture the immutable combined candidate and its actual parent identities
   before relying on any verification. Reuse the existing combined-foundation
   workflow and requirements; this source reconciliation creates no new review
   loop or acceptance gate.
5. Follow the retained integration plan for the existing idle isolated normal
   cache only **after** root establishes that the active gate's writers have
   finished and preserves its actual outcome and evidence. No current output
   directory is shared, transplanted, deleted or repurposed by this report.
6. Obtain the existing applicable focused/full build and exhaustive audit,
   independent Standards and Spec reviews on the matching immutable combined
   scope, and immediate candidate-identity verification before acceptance.
   Historical focused successes, clean text merging, source readbacks, saved
   branches and content hashes do not substitute for those existing gates.

The supplied report is the sole filesystem write from this task. No repository
source, control requirement, ticket, index, ref, worktree, cache, toolchain,
compiler session or remote artifact was changed. Its complete text was read
back after writing. All integration and acceptance work remains with root.
