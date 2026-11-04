# Preparation record, excluded from both author handoffs

The implementing agent designed both tasks, wrote concrete source proofs and
private generalized reference solutions, prepared the dependency ledger and
selected its opaque lemma boundary. Those are mathematical judgments supplied
before measured attempts, not extractor output. Reading #286's published paper
comparison informed W. E was chosen as a new three-block reversal argument.
The coordinator checked the protocol boundary; independent authors did not
participate in preparation. No #108 material was selected or prepared.

The initial local base was `2525b12052e4c85c57f9050dbf18f7a36ba2ef19`. Before
freeze the branch incorporated `d8563a8420196fedff7c875c158d0eeca3403db2`, the
accepted #291/#294 integration tip. Private package/build caches were copied
from the main checkout with `cp -a --reflink=auto`; no project outputs are shared
writable with another checkout. Handoffs copy only dependency packages and
build their own support output. The support imports no private project module.

## Preparation failures and retained commands

`Support01.lean` and `Reference01.lean` preserve the first sources. The first
support invocation was `direnv exec . lake env lean -o
.lake/build/lib/lean/Examples/ProofRequirementSupport.olean
Examples/ProofRequirementSupport.lean`. It failed because `List.reverse_append`
has implicit list arguments in this pinned library: applying it explicitly at
source lines 18 and 20 produced `Function expected at List.reverse_append`.
An immediate reference invocation then failed because the support `.olean`
did not exist. These two diagnostics survive in the agent tool conversation;
there is no separately exported raw shell log or exact UTC timestamp for them.
This paragraph is a transcribed account, not a raw transcript.

`check02.json/.log` record successful support compilation; `check03.json/.log`
record successful initial reference checking, including linter suggestions.
The first retained check start is 2026-11-04T20:11:35.332916+00:00. Subsequent
edits changed proposition definitions to theorems and removed misleading public
comment hints. `ProofRequirementSupport04.lean` and
`ProofRequirementReference04.lean` snapshot the later sources;
`check04.json/.log` record a successful focused Lake build. The support's legacy
module-system warning is nonfatal and consistent with the repository's existing
module style. No new axiom or admission was used.

The printed-term inspection records validate the supplied ledger at the chosen
leaf boundary, including the generated proof helper for the subtype property.
The `_ambient` proof argument occurs only as a binder; the two double-reversal
leaves actually occur. The ledger supplies these observations but does not
include the private generalized interface, changed proof or target proofs.

Preparation paused to free agent capacity for independent reviews of #291/#294
and later resumed. Active reasoning time, token usage, serving revision and
price are unavailable. Full elapsed time includes this pause and cache copying
and must not be called author effort. The JSON check records measure individual
compiler processes only. No paid API calls or additional research agents were
used by this assigned implementer.

The first smoke builds in both copied handoffs failed before Lean: `use flake`
found an unrelated `/tmp/.git` marker above their initially non-Git directories
and Nix reported it could not open `/tmp` as a Git repository. Both exact raw
outputs are retained in `handoff-*-build.log` with command/time/status JSON.
Each handoff then received a fresh independent Git repository containing only
its public allowlist; there is no original repository history or remote, and
caches/attempts are ignored. The second build records retain the result of
that correction. This is setup effort, not author effort or mathematical help.

## Validation scope

Focused checks establish the concrete support and private reference claims.
README candidate build/audit evidence is stored outside the checkout while it
runs, then recorded against its exact commit. New successful author artifacts
will require their own recheck, statement review and integrated audit after the
attempts close. The setup is not complete acceptance of #293.

The immutable attempt wrapper is supplied to both routes. Its preparation
checks exercise a successful source, an actual Lean failure, and refusal to
overwrite an existing archive. This tests evidence retention, not the task's
mathematics. Author namespaces are distinct and frozen. No agent-session export
tool was exposed, so authored transcripts must not be presented as raw sessions.
